// Copyright (C) 2018-2025 Daniel Mueller <deso@posteo.net>
// SPDX-License-Identifier: GPL-3.0-or-later

//! A watchdog for starting and restarting another program.

mod args;
mod backoff;

use std::borrow::Cow;
use std::ffi::OsString;
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

use crate::args::Args;
use crate::backoff::Backoff;


fn code(exit_status: &ExitStatus) -> Option<i32> {
  if let Some(code) = exit_status.code() {
    Some(code)
  } else {
    // TODO: Unclear if that negation is correct or whether the
    //       result is already negative.
    exit_status.signal().map(|code| -code)
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
      Ok(exit_status) => {
        let status = code(&exit_status)
          .map(|code| Cow::from(code.to_string()))
          .unwrap_or(Cow::from("N/A"));

        error!(
          "program {} exited with status {}",
          command.display(),
          status
        );
      },
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
