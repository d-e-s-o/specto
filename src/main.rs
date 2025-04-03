// Copyright (C) 2018-2025 Daniel Mueller <deso@posteo.net>
// SPDX-License-Identifier: GPL-3.0-or-later

//! A watchdog for starting and restarting another program.

mod args;
mod backoff;
mod signal;
mod util;
mod watched;

use std::ffi::OsStr;
use std::ffi::OsString;
use std::io::ErrorKind;
use std::ops::Deref as _;
use std::os::unix::process::ExitStatusExt;
use std::path::Path;
use std::process::ExitStatus;
use std::thread::sleep;
use std::time::Duration;
use std::time::Instant;

use anyhow::Context;

use clap::Parser as _;

use env_logger::init as init_log;

use log::debug;
use log::error;
use log::info;

use mio::Events;
use mio::Interest;
use mio::Poll;
use mio::Token;

use crate::args::Args;
use crate::backoff::Backoff;
use crate::signal::sigchld_events;
use crate::signal::sigint_events;
use crate::signal::sigterm_events;
use crate::watched::Watched;


/// Format a command with the given list of arguments as a string.
fn format_command<C, A, S>(command: C, args: A) -> String
where
  C: AsRef<OsStr>,
  A: IntoIterator<Item = S>,
  S: AsRef<OsStr>,
{
  args.into_iter().fold(
    command.as_ref().to_string_lossy().into_owned(),
    |mut cmd, arg| {
      cmd += " ";
      cmd += arg.as_ref().to_string_lossy().deref();
      cmd
    },
  )
}


fn evaluate_status<C, A, S>(status: ExitStatus, command: C, args: A)
where
  C: AsRef<OsStr>,
  A: IntoIterator<Item = S>,
  S: AsRef<OsStr>,
{
  let command = format_command(command, args);
  if status.success() {
    info!("`{command}` exited successfully");
  } else {
    let code = if let Some(code) = status.code() {
      format!(" ({code})")
    } else {
      format!(
        " (terminated by signal{})",
        status
          .signal()
          .map(|num| format!(" {num}"))
          .unwrap_or_default()
      )
    };

    error!("`{command}` reported non-zero exit-status{code}");
  }
}


fn kill_child_now(watched: Watched) {
  info!("forcefully killing child process");
  if let Err(err) = watched.kill() {
    error!("failed to kill child process: {err:?}");
  }
}


fn watchdog(command: &Path, arguments: &[OsString], backoff: Backoff) {
  let mut backoff = backoff;
  let mut poll = Poll::new().expect("failed to create poll instance");
  let mut events = Events::with_capacity(16);

  let mut sigterm_events = sigterm_events().expect("failed to register SIGTERM handler");
  let sigterm_token = Token(0);
  let mut sigint_events = sigint_events().expect("failed to register SIGINT handler");
  let sigint_token = Token(1);
  let mut sigchld_events = sigchld_events().expect("failed to register SIGCHLD handler");
  let sigchld_token = Token(2);

  let () = poll
    .registry()
    .register(&mut sigterm_events, sigterm_token, Interest::READABLE)
    .expect("failed to register poll for SIGTERM events");
  let () = poll
    .registry()
    .register(&mut sigint_events, sigint_token, Interest::READABLE)
    .expect("failed to register poll for SIGINT events");
  let () = poll
    .registry()
    .register(&mut sigchld_events, sigchld_token, Interest::READABLE)
    .expect("failed to register poll for SIGCHLD events");

  let mut timeout = None;
  let mut should_exit = false;

  loop {
    let spawned = Instant::now();

    match Watched::new(command, arguments) {
      Ok(mut watched) => {
        'poll: loop {
          match poll.poll(&mut events, timeout) {
            Ok(()) => {
              for event in events.iter() {
                match event.token() {
                  token if token == sigterm_token => {
                    if should_exit {
                      return kill_child_now(watched)
                    }
                    should_exit = true;
                    timeout = Some(Duration::from_millis(500));
                    continue 'poll
                  },
                  token if token == sigint_token => {
                    // The first request to terminate causes us to ask
                    // the child to terminate gracefully and after that
                    // we force-kill it.
                    if !should_exit {
                      if let Err(err) = watched.terminate() {
                        error!("failed to terminate child process gracefully: {err:?}");
                      } else {
                        should_exit = true;
                        continue 'poll
                      }
                    }
                    return kill_child_now(watched)
                  },
                  token if token == sigchld_token => {
                    match watched.try_wait() {
                      Ok(Some(status)) => {
                        let () = evaluate_status(status, command, arguments);
                        break 'poll
                      },
                      Ok(None) => {
                        // Apparently the child is not yet ready? I
                        // guess we just continue then. It's
                        // questionable whether this is a reachable
                        // path.
                      },
                      Err(err) if err.raw_os_error() == Some(libc::ECHILD) => {
                        // We should only see this error if the child
                        // somehow died without us noticing, which
                        // should not be possible. Yet, in the spirit of
                        // being as fault tolerant as possible, just
                        // continue with a restart.
                        break 'poll
                      },
                      Err(err) => {
                        // SANITY: We should not hit this case, as the
                        //         remaining conditions for the
                        //         underlying waitpid system call to
                        //         fail are all related to faulty
                        //         inputs.
                        Err(err)
                          .context("failed to wait for watched process")
                          .unwrap()
                      },
                    }
                  },
                  _ => unreachable!(),
                }
              }

              // Attempt to detect a poll timeout, which should be
              // signaled with a successful return. We do that after
              // draining any otherwise outstanding events.
              if timeout.is_some() {
                debug_assert!(should_exit);
                return kill_child_now(watched)
              }
            },
            Err(err) if err.kind() == ErrorKind::Interrupted => continue,
            Err(err) => {
              // SANITY: We should not hit this case, as the remaining
              //         conditions for the underlying epoll_wait system
              //         call to fail are all related to faulty inputs.
              Err(err).context("failed to poll events").unwrap()
            },
          }
        }
      },
      Err(err) => error!(
        "failed to execute `{}`: {err:?}",
        format_command(command, arguments)
      ),
    }

    if should_exit {
      return
    }

    if let Some(delay) = backoff.next_delay(spawned, Instant::now()) {
      debug!("using back off delay {:?}", delay);
      // TODO: This sleep isn't actually interruptible by Ctrl-C, so we
      //       may end up unintentionally delaying termination.
      let () = sleep(delay);
    }
  }
}

fn main() {
  init_log();

  let args = Args::parse();
  let backoff = Backoff::new(args.backoff_base, args.backoff_multiplier, args.backoff_max);

  watchdog(&args.command, &args.arguments, backoff)
}
