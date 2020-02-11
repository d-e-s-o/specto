// Copyright (C) 2018-2020 Daniel Mueller <deso@posteo.net>
// SPDX-License-Identifier: GPL-3.0-or-later

//! A watchdog for starting and restarting another program.

use std::borrow::Cow;
use std::ffi::OsStr;
use std::ffi::OsString;
use std::io::stdout;
use std::io::Write;
use std::os::unix::process::ExitStatusExt;
use std::path::Path;
use std::path::PathBuf;
use std::process::exit;
use std::process::Command;
use std::process::ExitStatus;
use std::process::Stdio;
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
  /// The maximum number of "quick" failures to encounter before
  /// exiting.
  #[structopt(long = "quick-failures", default_value = "5")]
  quick_failures: usize,
  /// The maximum runtime of the managed program in milliseconds up to
  /// which a failure is considered a quick failure.
  #[structopt(long = "quick-failure-millis", default_value = "2000")]
  quick_failure_millis: u64,
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
  max_quick_failures: usize,
  quick_failure_nanos: u64,
) -> i32 {
  let mut quick_failures = 0;

  loop {
    let spawned = Instant::now();
    let exit_code = match execute(command, arguments) {
      Ok(exit_status) => {
        let exit_code = code(&exit_status);
        let status = exit_code
          .map(|code| Cow::from(code.to_string()))
          .unwrap_or(Cow::from("N/A"));

        eprintln!(
          "program {} exited with status {}",
          command.display(),
          status
        );
        exit_code
      },
      Err(err) => {
        eprintln!("failed to execute {}: {:#}", command.display(), err);
        None
      },
    };

    if spawned.elapsed() <= Duration::from_nanos(quick_failure_nanos) {
      quick_failures += 1;

      if quick_failures >= max_quick_failures {
        eprintln!(
          "maximum number of quick failures ({}) reached",
          max_quick_failures
        );
        break exit_code.unwrap_or(1)
      }
    } else {
      // Reset quick failures if the program ran for longer but then
      // failed.
      quick_failures = 0;
    }
  }
}

fn main() {
  let opts = Opts::from_args();

  let quick_failures = opts.quick_failures;
  let quick_failure_nanos = u64::from(opts.quick_failure_millis) * 1_000_000;
  let exit_code = watchdog(
    &opts.command,
    &opts.arguments,
    quick_failures,
    quick_failure_nanos,
  );
  // We exit the process the hard way next, so make sure to flush
  // buffered content.
  let _ = stdout().flush();
  exit(exit_code)
}


#[cfg(test)]
pub mod tests {
  use super::*;


  #[test]
  fn too_many_quick_failures() {
    let code = watchdog(&PathBuf::from("/bin/true"), &[], 10, 1_000_000_000);
    assert_eq!(code, 0);

    let code = watchdog(&PathBuf::from("/bin/false"), &[], 2, 1_000_000_000);
    assert_eq!(code, 1);
  }
}
