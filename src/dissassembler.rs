use std::io;

use crate::{
    instructions::{self, BaseLoadOperation, BaseStoreOperation, Instruction, InstructionDecoder},
    rom::Rom,
};

pub fn disassemble_rom(rom: &Rom) -> io::Result<String> {
    let mut result = String::new();
    let mut chunks = rom.data.iter();
    let mut addr = *chunks.next().unwrap();
    for chunk in chunks {
        if let Ok(instr) = (*chunk).decode() {
            result.push_str(&format!("{:x} {}\n", addr, instr.disassemble()));
        } else if (0x20..=0x7E).contains(chunk) || 0xA == *chunk {
            let ascii_char = *chunk as u8 as char;
            if ascii_char == '\n' {
                result.push_str(&format!("{:x} .DATA '\\n'\n", addr));
            } else {
                result.push_str(&format!(
                    "{:x} .DATA 0x{:x} '{}'\n",
                    addr, chunk, ascii_char
                ));
            }
        } else {
            result.push_str(&format!("{:x} .DATA 0x{:x}\n", addr, chunk));
        }

        addr += 1;
    }

    Ok(result)
}

pub trait Disassemble {
    fn disassemble(&self) -> String;
}

impl Disassemble for Instruction {
    fn disassemble(&self) -> String {
        match self {
            Instruction::Add(add) => format!("ADD {}", add.disassemble()),
            Instruction::And(and) => format!("AND {}", and.disassemble()),
            Instruction::Jmp(jmp) => jmp.disassemble(),
            Instruction::Jsr(jsr) => jsr.disassemble(),
            Instruction::Br { n, z, p, pc_offset } => {
                let mut flags = String::new();
                if *n {
                    flags.push('n');
                }
                if *z {
                    flags.push('z');
                }
                if *p {
                    flags.push('p');
                }
                format!("BR {} 0x{:x}", flags, pc_offset)
            }
            Instruction::Ld(BaseLoadOperation {
                dest_reg,
                pc_offset,
            }) => {
                format!("LD R{}, 0x{:x}", dest_reg, pc_offset)
            }
            Instruction::Ldi(BaseLoadOperation {
                dest_reg,
                pc_offset,
            }) => {
                format!("LDI R{}, 0x{:x}", dest_reg, pc_offset)
            }
            Instruction::Ldr {
                dest_reg,
                base_reg,
                offset,
            } => {
                format!("LDR R{}, R{}, 0x{:x}", dest_reg, base_reg, offset)
            }
            Instruction::Lea(BaseLoadOperation {
                dest_reg,
                pc_offset,
            }) => {
                format!("LEA R{}, 0x{:x}", dest_reg, pc_offset)
            }
            Instruction::Not { dest_reg, src_reg } => {
                format!("NOT R{}, R{}", dest_reg, src_reg)
            }
            Instruction::Rti => "RTI".to_string(),
            Instruction::St(BaseStoreOperation { src_reg, pc_offset }) => {
                format!("ST R{}, 0x{:x}", src_reg, pc_offset)
            }
            Instruction::Sti(BaseStoreOperation { src_reg, pc_offset }) => {
                format!("STI R{}, 0x{:x}", src_reg, pc_offset)
            }
            Instruction::Str {
                src_reg,
                base_reg,
                offset,
            } => {
                format!("STR R{}, R{}, 0x{:x}", src_reg, base_reg, offset)
            }
            Instruction::Trap(trap) => {
                format!("TRAP {}", trap)
            }
        }
    }
}

impl Disassemble for instructions::BaseALOperation {
    fn disassemble(&self) -> String {
        match self {
            instructions::BaseALOperation::Immediate {
                dest_reg,
                src_reg,
                imm,
            } => {
                format!("R{}, R{}, 0x{:x}", dest_reg, src_reg, imm)
            }
            instructions::BaseALOperation::Register {
                dest_reg,
                src_reg1,
                src_reg2,
            } => {
                format!("R{}, R{}, R{}", dest_reg, src_reg1, src_reg2)
            }
        }
    }
}

impl Disassemble for instructions::Jmp {
    fn disassemble(&self) -> String {
        match self {
            instructions::Jmp::Jmp { base_reg } => {
                format!("JMP R{}", base_reg)
            }
            instructions::Jmp::Ret => "RET".to_string(),
        }
    }
}

impl Disassemble for instructions::Jsr {
    fn disassemble(&self) -> String {
        match self {
            instructions::Jsr::Jsr { pc_offset } => {
                format!("JSR 0x{:x}", pc_offset)
            }
            instructions::Jsr::Jsrr { base_reg } => {
                format!("JSRR R{}", base_reg)
            }
        }
    }
}
