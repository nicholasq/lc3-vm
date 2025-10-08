use libc::STDIN_FILENO;
use nix::sys::select::{select, FdSet};
use nix::sys::time::{TimeVal, TimeValLike};
use signal_hook::consts::SIGINT;
use signal_hook::iterator::Signals;
use std::io::Read;
use std::os::fd::BorrowedFd;
use std::{error::Error, thread};
use std::{io, process};

use termios::{tcsetattr, Termios, ECHO, ICANON, TCSANOW};

/// Handles the Ctrl-C (SIGINT) interrupt signal by restoring terminal settings,
/// printing a message, and exiting the process with code 130.
///
/// # Arguments
///
/// * `sig` - The signal number received (expected to be SIGINT).
pub fn handle_control_c(sig: i32) {
    restore_terminal_settings();
    println!("The LC3 VM received Ctrl-C interrupt signal (= {}).", sig);
    process::exit(130);
}

/// Spawns a background thread to handle Ctrl-C (SIGINT) signals.
/// When SIGINT is received, `handle_control_c` is called.
///
/// # Returns
///
/// * `Result<(), Box<dyn Error>>` - Returns Ok on success, or an error if signal handler setup fails.
pub fn spawn_control_c_handler() -> Result<(), Box<dyn Error>> {
    let mut signals = Signals::new([SIGINT])?;
    thread::spawn(move || {
        for sig in signals.forever() {
            handle_control_c(sig);
        }
    });
    Ok(())
}

/// Disables input buffering and echo for the terminal, allowing raw input mode.
/// This is useful for interactive programs that need to process input immediately.
pub fn disable_input_buffering() {
    let mut term: Termios = Termios::from_fd(STDIN_FILENO).unwrap();
    term.c_lflag &= !(ICANON | ECHO);
    tcsetattr(STDIN_FILENO, TCSANOW, &term).unwrap();
}

/// Restores the terminal settings to enable canonical mode and echo.
/// This should be called before exiting to ensure the terminal behaves normally.
pub fn restore_terminal_settings() {
    let mut term: Termios = Termios::from_fd(STDIN_FILENO).unwrap();
    term.c_lflag |= ICANON | ECHO;
    tcsetattr(STDIN_FILENO, TCSANOW, &term).unwrap();
}

/// Takes a 16-bit value and sign extends it from a given bit position by filling all bits
/// to the left of the sign bit with the same value as the sign bit.
pub fn sign_extend(x: u16, bit_count: u16) -> u16 {
    if ((x >> (bit_count - 1)) & 1) == 1 {
        x | (0xFFFF << bit_count)
    } else {
        x
    }
}
///
/// Checks if a key has been pressed on standard input (stdin).
///
/// Returns `true` if a key is available to read, otherwise `false`.
pub fn check_key() -> bool {
    const STDIN_FILENO: i32 = 0;

    let mut readfds = FdSet::new();
    unsafe {
        readfds.insert(BorrowedFd::borrow_raw(STDIN_FILENO));
    }

    match select(None, &mut readfds, None, None, &mut TimeVal::zero()) {
        Ok(value) => value == 1,
        Err(_) => false,
    }
}

/// Reads a single byte from standard input (stdin) and returns it as a `u16`.
///
/// Panics if unable to read from stdin.
pub fn get_char() -> u16 {
    let mut buffer = [0; 1];
    io::stdin()
        .read_exact(&mut buffer)
        .expect("unable to read from STDIN");

    u16::from(buffer[0])
}
