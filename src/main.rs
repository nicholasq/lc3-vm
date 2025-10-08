mod cpu;
mod dissassembler;
mod instructions;
mod memory;
mod rom;
mod util;
mod vm;

use util::{disable_input_buffering, spawn_control_c_handler};
use vm::Vm;

use crate::{rom::Rom, util::restore_terminal_settings};

fn main() {
    let args: Vec<String> = std::env::args().collect();

    if args.len() < 2 {
        eprintln!("Usage: lc3-vm [-d] [image-file1]");
        std::process::exit(1);
    }

    let image = if args[1] == "-d" {
        std::fs::read(&args[2]).unwrap()
    } else {
        std::fs::read(&args[1]).unwrap()
    };

    if args[1] == "-d" {
        let rom = Rom::from_image(image);
        let asm_source = dissassembler::disassemble_rom(&rom).unwrap();
        let asm_file_name = if let Some(pos) = args[2].rfind('.') {
            format!("{}.asm", &args[2][..pos])
        } else {
            format!("{}.asm", &args[2])
        };

        std::fs::write(&asm_file_name, asm_source).unwrap_or_else(|err| {
            eprintln!("Failed to write to {}: {}", asm_file_name, err);
            std::process::exit(1);
        });

        println!("Assembly source written to {}", asm_file_name);
        return;
    }

    spawn_control_c_handler().unwrap();
    disable_input_buffering();

    let rom = Rom::from_image(image);
    let mut vm = Vm::new();
    vm.start(rom);
    restore_terminal_settings();
}
