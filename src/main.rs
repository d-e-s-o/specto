// Copyright (C) 2018-2025 Daniel Mueller <deso@posteo.net>
// SPDX-License-Identifier: GPL-3.0-or-later

//! A watchdog for starting and restarting another program.

use std::borrow::Cow;
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

use anyhow::anyhow;
use anyhow::Context;
use anyhow::Error;

use env_logger::init as init_log;

use log::debug;
use log::error;

use clap::Parser;


/// Parse a duration from a string.
fn parse_duration(s: &str) -> Result<Duration, Error> {
  let durations = [
    ("ms", 1),
    ("sec", 1000),
    ("s", 1000),
    ("min", 60000),
    ("m", 60000),
  ];

  for (suffix, multiplier) in &durations {
    if let Some(base) = s.strip_suffix(suffix) {
      if let Ok(count) = base.parse::<u64>() {
        return Ok(Duration::from_millis(count * multiplier))
      }
    }
  }

  Err(anyhow!("invalid duration provided: {}", s))
}


/// A program for "watched" invocation of others.
#[derive(Debug, Parser)]
struct Args {
  /// The managed program's command.
  command: PathBuf,
  /// The managed program's arguments.
  arguments: Vec<OsString>,
  /// The backoff time to use initially.
  ///
  /// This value also acts as the minimum time the program needs to be
  /// alive in order to not increase the backoff.
  ///
  /// Accepted suffixes are 'ms' for milliseconds, 's' for seconds, and
  /// 'm' for minutes.
  #[arg(long = "backoff-base", value_parser = parse_duration, default_value = "100ms")]
  backoff_base: Duration,
  /// The factor to multiply the current backoff with to get the next
  /// backoff.
  #[arg(long = "backoff-multiplier", default_value = "2.0")]
  backoff_muliplier: f64,
  /// The maximum backoff to use.
  ///
  /// Accepted suffixes are 'ms' for milliseconds, 's' for seconds, and
  /// 'm' for minutes.
  #[arg(long = "backoff-max", value_parser = parse_duration, default_value = "30s")]
  backoff_max: Duration,
}


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

        error!(
          "program {} exited with status {}",
          command.display(),
          status
        );
      },
      Err(err) => error!("failed to execute {}: {:#}", command.display(), err),
    };

    if spawned.elapsed() <= backoff_base {
      backoff = backoff.mul_f64(backoff_muliplier);

      if backoff > backoff_max {
        backoff = backoff_max;
      }
      debug!("using back off {:?}", backoff);
      sleep(backoff)
    } else {
      // Reset the backoff.
      backoff = backoff_base;
      debug!("reset back off to {:?}", backoff);
    }
  }
}

fn main() -> ! {
  init_log();

  let args = Args::parse();

  watchdog(
    &args.command,
    &args.arguments,
    args.backoff_base,
    args.backoff_muliplier,
    args.backoff_max,
  );
}


#[cfg(test)]
mod tests {
  use super::*;


  /// Check that we can parse duration descriptions properly.
  #[test]
  fn duration_parsing() {
    assert_eq!(parse_duration("1ms").unwrap(), Duration::from_millis(1));
    assert_eq!(parse_duration("500ms").unwrap(), Duration::from_millis(500));
    assert_eq!(parse_duration("1s").unwrap(), Duration::from_secs(1));
    assert_eq!(parse_duration("1sec").unwrap(), Duration::from_secs(1));
    assert_eq!(parse_duration("13s").unwrap(), Duration::from_secs(13));
    assert_eq!(parse_duration("13sec").unwrap(), Duration::from_secs(13));
    assert_eq!(parse_duration("1m").unwrap(), Duration::from_secs(60));
    assert_eq!(parse_duration("1min").unwrap(), Duration::from_secs(60));
    assert_eq!(parse_duration("13m").unwrap(), Duration::from_secs(13 * 60));
    assert_eq!(
      parse_duration("13min").unwrap(),
      Duration::from_secs(13 * 60)
    );
  }
}
