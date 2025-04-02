// Copyright (C) 2025 Daniel Mueller <deso@posteo.net>
// SPDX-License-Identifier: GPL-3.0-or-later

use std::cmp::PartialOrd;
use std::io;
use std::io::Error;


/// Check the return value of a system call.
pub(crate) fn check<T>(result: T, error: T) -> io::Result<()>
where
  T: Copy + PartialOrd<T>,
{
  if result == error {
    Err(Error::last_os_error())
  } else {
    Ok(())
  }
}
