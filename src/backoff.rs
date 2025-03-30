// Copyright (C) 2025 Daniel Mueller <deso@posteo.net>
// SPDX-License-Identifier: GPL-3.0-or-later

use std::time::Duration;
use std::time::Instant;


pub(crate) struct Backoff {
  backoff_base: Duration,
  backoff_multiplier: f64,
  backoff_max: Duration,
  backoff: Duration,
}

impl Backoff {
  pub fn new(backoff_base: Duration, backoff_multiplier: f64, backoff_max: Duration) -> Self {
    Self {
      backoff_base,
      backoff_multiplier,
      backoff_max,
      backoff: backoff_base,
    }
  }

  pub fn next_delay(&mut self, prev: Instant, now: Instant) -> Option<Duration> {
    if now.saturating_duration_since(prev) <= self.backoff_base {
      let delay = self.backoff;
      self.backoff = self.backoff.mul_f64(self.backoff_multiplier);

      if self.backoff > self.backoff_max {
        self.backoff = self.backoff_max;
      }
      Some(delay)
    } else {
      // Reset the backoff.
      self.backoff = self.backoff_base;
      None
    }
  }
}


#[cfg(test)]
mod tests {
  use super::*;


  /// Check that our backoff delay logic works as it should.
  #[test]
  fn backoff() {
    let base = Duration::from_secs(1);
    let multiplier = 2.0;
    let max = Duration::from_secs(30);
    let mut backoff = Backoff::new(base, multiplier, max);

    let now = Instant::now();
    let prev = now - Duration::from_secs(2);
    // The previous "event" is further than `base` in the past, so there
    // should be no backoff.
    assert_eq!(backoff.next_delay(prev, now), None);

    let prev = now - Duration::from_millis(500);
    let delay = backoff.next_delay(prev, now).unwrap();
    assert_eq!(delay, base);

    let delay = backoff.next_delay(prev, now).unwrap();
    assert_eq!(delay, base.mul_f64(multiplier));

    let delay = backoff.next_delay(prev, now).unwrap();
    assert_eq!(delay, base.mul_f64(multiplier * 2.0));

    let delay = backoff.next_delay(prev, now).unwrap();
    assert_eq!(delay, base.mul_f64(multiplier * 4.0));

    let delay = backoff.next_delay(prev, now).unwrap();
    assert_eq!(delay, base.mul_f64(multiplier * 8.0));

    let delay = backoff.next_delay(prev, now).unwrap();
    assert_eq!(delay, max);

    let delay = backoff.next_delay(prev, now).unwrap();
    assert_eq!(delay, max);

    let prev = now - Duration::from_secs(2);
    assert_eq!(backoff.next_delay(prev, now), None);

    let prev = now - Duration::from_millis(500);
    let delay = backoff.next_delay(prev, now).unwrap();
    assert_eq!(delay, base);
  }
}
