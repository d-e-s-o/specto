// Copyright (C) 2025 Daniel Mueller <deso@posteo.net>
// SPDX-License-Identifier: GPL-3.0-or-later

use std::ffi::OsString;
use std::io;
use std::io::ErrorKind;
use std::os::fd::FromRawFd as _;
use std::os::fd::IntoRawFd as _;
use std::path::Path;
use std::path::PathBuf;
use std::process::Child;
use std::process::Command;
use std::process::ExitStatus;
use std::process::Stdio;

use anyhow::Context as _;
use anyhow::Result;

use libc::kill;
use libc::SIGTERM;

use mio::unix::pipe;
use mio::unix::pipe::Receiver;

use crate::rotate::Rotate;
use crate::util::check;


#[derive(Clone, Copy, Debug)]
pub(crate) enum Streams {
  /// The `stdout` stream.
  Stdout,
  /// The `stderr` stream.
  Stderr,
  /// Both the `stdout` and `stderr` streams.
  Both,
}


#[derive(Debug, Default)]
pub(crate) struct Builder {
  log_file: Option<PathBuf>,
  log_streams: Option<Streams>,
  max_log_lines: Option<usize>,
  max_log_files: Option<usize>,
}

impl Builder {
  pub fn set_log_file<P>(mut self, log_file: Option<P>) -> Self
  where
    P: AsRef<Path>,
  {
    self.log_file = log_file.map(|path| path.as_ref().to_path_buf());
    self
  }

  pub fn set_log_streams(mut self, log_streams: Option<Streams>) -> Self {
    self.log_streams = log_streams;
    self
  }

  pub fn set_max_log_lines(mut self, max_log_lines: Option<usize>) -> Self {
    assert_ne!(max_log_lines, Some(0));
    self.max_log_lines = max_log_lines;
    self
  }

  pub fn set_max_log_files(mut self, max_log_files: Option<usize>) -> Self {
    assert_ne!(max_log_files, Some(0));
    self.max_log_files = max_log_files;
    self
  }

  pub fn build(self, command: &Path, arguments: &[OsString]) -> Result<Watched> {
    let Self {
      log_file,
      log_streams,
      max_log_lines,
      max_log_files,
    } = self;

    // A watchdog is for running non-interactive programs, so we close
    // stdin.
    let mut command = Command::new(command);
    let _command = command
      .args(arguments)
      .stdin(Stdio::null())
      .stdout(Stdio::inherit())
      .stdout(Stdio::inherit());

    let (rotate, stdout, stderr) = if let Some(log_file) = log_file {
      let rotate = Rotate::builder()
        .set_max_lines(max_log_lines)
        .set_max_files(max_log_files)
        .build(log_file)?;

      let log_streams = log_streams.unwrap_or(Streams::Both);
      let stdout = matches!(log_streams, Streams::Stdout | Streams::Both);
      let stderr = matches!(log_streams, Streams::Stderr | Streams::Both);

      let stdout_source = if stdout {
        let (sender, receiver) =
          pipe::new().context("failed to create pipe for stdout forwarding")?;
        let _command = command.stdout(unsafe { Stdio::from_raw_fd(sender.into_raw_fd()) });
        Some(receiver)
      } else {
        None
      };

      let stderr_source = if stderr {
        let (sender, receiver) =
          pipe::new().context("failed to create pipe for stderr forwarding")?;
        let _command = command.stderr(unsafe { Stdio::from_raw_fd(sender.into_raw_fd()) });
        Some(receiver)
      } else {
        None
      };

      (Some(rotate), stdout_source, stderr_source)
    } else {
      (None, None, None)
    };

    let child = command.spawn().with_context(|| "failed to spawn child")?;
    let poll_data = if stdout.is_none() && stderr.is_none() {
      None
    } else {
      Some(PollData { stdout, stderr })
    };

    let slf = Watched {
      child,
      rotate,
      poll_data,
    };
    Ok(slf)
  }
}


/// Data necessary for polling stdio streams.
#[derive(Debug)]
pub(crate) struct PollData {
  pub stdout: Option<Receiver>,
  pub stderr: Option<Receiver>,
}


#[derive(Debug)]
pub(crate) struct Watched {
  child: Child,
  rotate: Option<Rotate>,
  poll_data: Option<PollData>,
}

impl Watched {
  pub fn builder() -> Builder {
    Builder::default()
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

  /// Forward data from a stream to the file rotation facility.
  pub fn forward(&mut self, stream: &mut Receiver) -> Result<()> {
    match &mut self.rotate {
      Some(rotate) => rotate.forward(stream),
      None => Ok(()),
    }
  }

  /// Take the [`PollData`] associated with this object.
  ///
  /// By design, this is possible only a single time. Callers
  /// effectively take ownership of the receiving ends of stdio streams,
  /// if captured.
  pub fn take_poll_data(&mut self) -> Option<PollData> {
    self.poll_data.take()
  }
}
