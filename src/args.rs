// Copyright (C) 2025 Daniel Mueller <deso@posteo.net>
// SPDX-License-Identifier: GPL-3.0-or-later

use std::ffi::OsString;
use std::path::PathBuf;
use std::time::Duration;

use anyhow::anyhow;
use anyhow::Error;

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
#[clap(version = env!("VERSION"))]
pub(crate) struct Args {
  /// The managed program's command.
  pub command: PathBuf,
  /// The managed program's arguments.
  pub arguments: Vec<OsString>,
  /// The backoff time to use initially.
  ///
  /// This value also acts as the minimum time the program needs to be
  /// alive in order to not increase the backoff.
  ///
  /// Accepted suffixes are 'ms' for milliseconds, 's' for seconds, and
  /// 'm' for minutes.
  #[arg(long = "backoff-base", value_parser = parse_duration, default_value = "1s")]
  pub backoff_base: Duration,
  /// The factor to multiply the current backoff with to get the next
  /// backoff.
  #[arg(long = "backoff-multiplier", default_value = "2.0")]
  pub backoff_multiplier: f64,
  /// The maximum backoff to use.
  ///
  /// Accepted suffixes are 'ms' for milliseconds, 's' for seconds, and
  /// 'm' for minutes.
  #[arg(long = "backoff-max", value_parser = parse_duration, default_value = "30s")]
  pub backoff_max: Duration,
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
