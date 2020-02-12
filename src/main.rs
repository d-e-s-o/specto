// Copyright (C) 2018-2020 Daniel Mueller <deso@posteo.net>
// SPDX-License-Identifier: GPL-3.0-or-later

//! A watchdog for starting and restarting another program.

use std::borrow::Cow;
use std::ffi::OsStr;
use std::ffi::OsString;
use std::os::unix::process::ExitStatusExt;
use std::path::Path;
use std::path::PathBuf;
use std::process::Command;
use std::process::ExitStatus;
use std::process::Stdio;
use std::thread::sleep;
use std::time::Duration;
use std::time::Instant;

use anyhow::Context;
use anyhow::Error;

use structopt::StructOpt;


/// Arguments for the watchdog.
#[derive(Debug, StructOpt)]
struct Opts {
  /// The managed program's command.
  command: PathBuf,
  /// The managed program's arguments.
  #[structopt(parse(from_os_str = OsStr::to_os_string))]
  arguments: Vec<OsString>,
  /// The backoff time in milliseconds to use initially.
  ///
  /// This value also acts as the minimum time the program needs to be
  /// alive in order to not increase the backoff.
  #[structopt(long = "backoff-millis-base", default_value = "100")]
  backoff_millis_base: u64,
  /// The factor to multiply the current backoff with to get the next
  /// backoff.
  #[structopt(long = "backoff-multiplier", default_value = "2.0")]
  backoff_muliplier: f64,
  /// The maximum backoff (in milliseconds) to use.
  #[structopt(long = "backoff-max", default_value = "30000")]
  backoff_millis_max: u64,
}


fn code(exit_status: &ExitStatus) -> Option<i32> {
  if let Some(code) = exit_status.code() {
    Some(code)
  } else if let Some(code) = exit_status.signal() {
    // TODO: Unclear if that negation is correct or whether the
    //       result is already negative.
    Some(-code)
  } else {
    None
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

fn watchdog(
  command: &Path,
  arguments: &[OsString],
  backoff_base: Duration,
  backoff_muliplier: f64,
  backoff_max: Duration,
) -> ! {
  let mut backoff = backoff_base;

  loop {
    let spawned = Instant::now();
    match execute(command, arguments) {
      Ok(exit_status) => {
        let status = code(&exit_status)
          .map(|code| Cow::from(code.to_string()))
          .unwrap_or(Cow::from("N/A"));

        eprintln!(
          "program {} exited with status {}",
          command.display(),
          status
        );
      },
      Err(err) => eprintln!("failed to execute {}: {:#}", command.display(), err),
    };

    if spawned.elapsed() <= backoff_base {
      backoff = backoff.mul_f64(backoff_muliplier);

      if backoff > backoff_max {
        backoff = backoff_max;
      }
      sleep(backoff)
    } else {
      // Reset the backoff.
      backoff = backoff_base;
    }
  }
}

fn main() -> ! {
  let opts = Opts::from_args();

  watchdog(
    &opts.command,
    &opts.arguments,
    Duration::from_millis(opts.backoff_millis_base),
    opts.backoff_muliplier,
    Duration::from_millis(opts.backoff_millis_max),
  );
}
