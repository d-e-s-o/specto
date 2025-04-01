// Copyright (C) 2018-2025 Daniel Mueller <deso@posteo.net>
// SPDX-License-Identifier: GPL-3.0-or-later

//! A watchdog for starting and restarting another program.

mod args;
mod backoff;

use std::ffi::OsStr;
use std::ffi::OsString;
use std::ops::Deref as _;
use std::os::unix::process::ExitStatusExt;
use std::path::Path;
use std::process::Command;
use std::process::ExitStatus;
use std::process::Stdio;
use std::thread::sleep;
use std::time::Instant;

use anyhow::Context;
use anyhow::Error;

use clap::Parser as _;

use env_logger::init as init_log;

use log::debug;
use log::error;
use log::info;

use crate::args::Args;
use crate::backoff::Backoff;


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


fn execute(command: &Path, arguments: &[OsString]) -> Result<ExitStatus, Error> {
  // A watchdog is for running non-interactive programs, so we close
  // stdin.
  let mut child = Command::new(command)
    .args(arguments)
    .stdin(Stdio::null())
    .stdout(Stdio::inherit())
    .stderr(Stdio::inherit())
    .spawn()
    .with_context(|| "failed to spawn child")?;

  child.wait().with_context(|| "failed to wait for child")
}

fn watchdog(command: &Path, arguments: &[OsString], backoff: Backoff) -> ! {
  let mut backoff = backoff;

  loop {
    let spawned = Instant::now();
    match execute(command, arguments) {
      Ok(status) => evaluate_status(status, command, arguments),
      Err(err) => error!("failed to execute {}: {:#}", command.display(), err),
    };

    if let Some(delay) = backoff.next_delay(spawned, Instant::now()) {
      debug!("using back off delay {:?}", delay);
      let () = sleep(delay);
    }
  }
}

fn main() -> ! {
  init_log();

  let args = Args::parse();
  let backoff = Backoff::new(args.backoff_base, args.backoff_multiplier, args.backoff_max);

  watchdog(&args.command, &args.arguments, backoff);
}
