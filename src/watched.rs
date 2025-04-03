// Copyright (C) 2025 Daniel Mueller <deso@posteo.net>
// SPDX-License-Identifier: GPL-3.0-or-later

use std::ffi::OsString;
use std::io;
use std::io::ErrorKind;
use std::path::Path;
use std::process::Child;
use std::process::Command;
use std::process::ExitStatus;
use std::process::Stdio;

use anyhow::Context as _;
use anyhow::Result;

use libc::kill;
use libc::SIGTERM;

use crate::util::check;


#[derive(Debug)]
pub(crate) struct Watched {
  child: Child,
}

impl Watched {
  pub fn new(command: &Path, arguments: &[OsString]) -> Result<Self> {
    // A watchdog is for running non-interactive programs, so we close
    // stdin.
    let child = Command::new(command)
      .args(arguments)
      .stdin(Stdio::null())
      .stdout(Stdio::inherit())
      .stderr(Stdio::inherit())
      .spawn()
      .with_context(|| "failed to spawn child")?;

    let slf = Self { child };
    Ok(slf)
  }

  pub fn try_wait(&mut self) -> io::Result<Option<ExitStatus>> {
    loop {
      match self.child.try_wait() {
        Ok(result) => break Ok(result),
        Err(err) if err.kind() == ErrorKind::Interrupted => {
          // This case may not be possible to hit in practice, but it's
          // unclear whether that's guaranteed, so play it safe.
          continue
        },
        Err(err) => break Err(err),
      }
    }
  }

  pub fn terminate(&self) -> Result<()> {
    // TODO: Ideally this would be PidFd based.
    let pid = self.child.id();
    let pid = pid
      .try_into()
      .with_context(|| format!("failed to convert PID {pid} into required type"))?;
    let result = unsafe { kill(pid, SIGTERM) };
    let () = check(result, -1).with_context(|| format!("failed to send SIGTERM to {pid}"))?;
    Ok(())
  }

  pub fn kill(mut self) -> io::Result<()> {
    self.child.kill()
  }
}
