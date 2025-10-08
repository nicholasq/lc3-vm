use std::cell::RefCell;
use std::io::{self, Read, Write};
use std::ops::{Index, IndexMut};
use std::rc::Rc;

use crate::instructions::{self, BaseLoadOperation, BaseStoreOperation, Instruction};
use crate::util::get_char;
use crate::{
    instructions::{ConditionFlag, InstructionDecoder, TrapCode},
    memory::{Lc3Memory, Memory, PC_START},
};

/// The main CPU structure for the LC-3 virtual machine.
///
/// The CPU contains the processor's registers, memory reference, execution state,
/// and instruction counter. It provides methods to fetch, decode, and execute
/// LC-3 instructions as part of the virtual machine's operation cycle.
///
/// The LC-3 has 10 total registers:
/// - 8 general purpose registers (R0-R7)
/// - 1 program counter (PC) register
/// - 1 condition flags (COND) register
pub struct Cpu {
    pub registers: [u16; 10],
    pub memory: Rc<RefCell<Memory>>,
    pub halted: bool,
    pub instr_count: u32,
}

impl Cpu {
    pub fn new(memory: Rc<RefCell<Memory>>) -> Self {
        let mut cpu = Cpu {
            registers: [0; 10],
            memory,
            halted: false,
            instr_count: 0,
        };

        cpu.registers[Register::Cond] = ConditionFlag::Zro as u16;
        cpu.registers[Register::PC] = PC_START;
        cpu
    }

    pub fn fetch(&mut self) -> u16 {
        let instr = self.memory.borrow_mut().read(self.registers[Register::PC]);
        self.registers[Register::PC] = self.registers[Register::PC].wrapping_add(1);
        instr
    }

    pub fn decode(&mut self, instr: u16) -> Instruction {
        let instr = instr.decode();
        match instr {
            Ok(instr) => instr,
            Err(msg) => {
                panic!("{}", msg)
            }
        }
    }

    pub fn execute(&mut self, instr: Instruction) {
        let exec_status = instr.execute(&mut self.registers, &mut self.memory.borrow_mut());
        if exec_status == ExecutionStatus::Halted {
            self.halted = true;
        }
        self.instr_count += 1;
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ExecutionStatus {
    Running,
    Halted,
}

trait Execute {
    fn execute(
        &self,
        registers: &mut [u16; REGISTER_COUNT],
        memory: &mut Memory,
    ) -> ExecutionStatus;
}

impl Execute for Instruction {
    fn execute(
        &self,
        registers: &mut [u16; REGISTER_COUNT],
        memory: &mut Memory,
    ) -> ExecutionStatus {
        match self {
            Instruction::Add(add) => {
                let (dest_reg, value) = match *add {
                    instructions::BaseALOperation::Immediate {
                        dest_reg,
                        src_reg,
                        imm,
                    } => (dest_reg, registers[src_reg as usize].wrapping_add(imm)),
                    instructions::BaseALOperation::Register {
                        dest_reg,
                        src_reg1,
                        src_reg2,
                    } => (
                        dest_reg,
                        registers[src_reg1 as usize].wrapping_add(registers[src_reg2 as usize]),
                    ),
                };
                registers[dest_reg as usize] = value;
                update_flags(registers, dest_reg);
            }
            Instruction::And(and) => {
                let (dest_reg, value) = match *and {
                    instructions::BaseALOperation::Immediate {
                        dest_reg,
                        src_reg,
                        imm,
                    } => (dest_reg, registers[src_reg as usize] & imm),
                    instructions::BaseALOperation::Register {
                        dest_reg,
                        src_reg1,
                        src_reg2,
                    } => (
                        dest_reg,
                        registers[src_reg1 as usize] & (registers[src_reg2 as usize]),
                    ),
                };
                registers[dest_reg as usize] = value;
                update_flags(registers, dest_reg);
            }
            Instruction::Br { n, z, p, pc_offset } => {
                let cond_reg = registers[Register::Cond];
                if *n && cond_reg == ConditionFlag::Neg.into()
                    || *z && cond_reg == ConditionFlag::Zro.into()
                    || *p && cond_reg == ConditionFlag::Pos.into()
                {
                    registers[Register::PC] = registers[Register::PC].wrapping_add(*pc_offset);
                }
            }
            Instruction::Jmp(jmp) => match jmp {
                instructions::Jmp::Jmp { base_reg } => {
                    registers[Register::PC] = registers[*base_reg as usize];
                }
                instructions::Jmp::Ret => {
                    registers[Register::PC] = registers[Register::R7];
                }
            },
            Instruction::Jsr(jsr) => {
                registers[Register::R7] = registers[Register::PC];
                match *jsr {
                    instructions::Jsr::Jsr { pc_offset } => {
                        registers[Register::PC] = registers[Register::PC].wrapping_add(pc_offset);
                    }
                    instructions::Jsr::Jsrr { base_reg } => {
                        registers[Register::PC] = registers[base_reg as usize];
                    }
                }
            }
            Instruction::Ld(BaseLoadOperation {
                dest_reg,
                pc_offset,
            }) => {
                let src_addr = registers[Register::PC].wrapping_add(*pc_offset);
                registers[*dest_reg as usize] = memory.read(src_addr);
                update_flags(registers, *dest_reg);
            }
            Instruction::Ldi(BaseLoadOperation {
                dest_reg,
                pc_offset,
            }) => {
                let src_addr = registers[Register::PC].wrapping_add(*pc_offset);
                let final_addr = memory.read(src_addr);
                registers[*dest_reg as usize] = memory.read(final_addr);
                update_flags(registers, *dest_reg);
            }
            Instruction::Ldr {
                dest_reg,
                base_reg,
                offset,
            } => {
                let addr = registers[*base_reg as usize].wrapping_add(*offset);
                registers[*dest_reg as usize] = memory.read(addr);
                update_flags(registers, *dest_reg);
            }
            Instruction::Lea(BaseLoadOperation {
                dest_reg,
                pc_offset,
            }) => {
                registers[*dest_reg as usize] = registers[Register::PC].wrapping_add(*pc_offset);
                update_flags(registers, *dest_reg);
            }
            Instruction::Not { dest_reg, src_reg } => {
                registers[*dest_reg as usize] = !registers[*src_reg as usize];
                update_flags(registers, *dest_reg);
            }
            Instruction::St(BaseStoreOperation { src_reg, pc_offset }) => {
                let addr = registers[Register::PC].wrapping_add(*pc_offset);
                memory.write(addr, registers[*src_reg as usize]);
            }
            Instruction::Sti(BaseStoreOperation { src_reg, pc_offset }) => {
                let addr = registers[Register::PC].wrapping_add(*pc_offset);
                let final_addr = memory.read(addr);
                memory.write(final_addr, registers[*src_reg as usize]);
            }
            Instruction::Str {
                src_reg,
                base_reg,
                offset,
            } => {
                let addr = registers[*base_reg as usize].wrapping_add(*offset);
                memory.write(addr, registers[*src_reg as usize]);
            }
            Instruction::Trap(trap) => {
                registers[Register::R7] = registers[Register::PC];

                match trap {
                    // TRAP GETC: Read a single ASCII character.
                    TrapCode::Getc => {
                        // Blocking read exactly one byte.
                        let mut buf = [0u8; 1];
                        io::stdin()
                            .read_exact(&mut buf)
                            .expect("Failed to read a character");
                        registers[Register::R0] = u16::from(buf[0]);
                    }
                    // TRAP OUT: Write the character in R0 to stdout.
                    TrapCode::Out => {
                        let ch = registers[Register::R0] as u8 as char;
                        print!("{}", ch);
                        std::io::stdout().flush().unwrap();
                    }
                    // TRAP PUTS: Write a null-terminated string from memory.
                    TrapCode::Puts => {
                        // The starting address of the string is in R0.
                        let mut addr = registers[Register::R0];
                        let mut line = String::new();
                        while memory.read(addr) != 0 {
                            // Each word contains one ASCII character.
                            let ch = memory.read(addr) as u8 as char;
                            line.push(ch);
                            addr = addr.wrapping_add(1);
                        }
                        print!("{}", line);
                        std::io::stdout().flush().unwrap();
                    }
                    // TRAP IN: Prompt for a character, echo it, then store it in R0.
                    TrapCode::In => {
                        print!("Enter a character: ");
                        let c = get_char();
                        print!("{}", c as u8 as char);
                        std::io::stdout().flush().unwrap();
                        registers[Register::R0] = c;
                        update_flags(registers, Register::R0 as u16);
                    }
                    // TRAP PUTSP: Write out a string where each word contains two characters.
                    TrapCode::Putsp => {
                        // Each word contains two ASCII characters: lower byte first, then upper byte
                        let mut addr = registers[Register::R0 as usize];
                        loop {
                            let word = memory.read(addr);
                            let char1 = (word & 0xFF) as u8;
                            if char1 == 0 {
                                break;
                            }
                            print!("{}", char1 as char);
                            let char2 = (word >> 8) as u8;
                            if char2 == 0 {
                                break;
                            }
                            print!("{}", char2 as char);
                            addr = addr.wrapping_add(1);
                        }
                        io::stdout().flush().unwrap();
                    }
                    // TRAP HALT: Print HALT and exit the program.
                    TrapCode::Halt => {
                        return ExecutionStatus::Halted;
                    }
                }
            }
            _ => panic!("Unimplemented instruction"),
        }
        ExecutionStatus::Running
    }
}

/// Updates the condition flag register based on the value in the specified register.
/// Sets the flag to Zero if the value is 0, Negative if the most significant bit is 1,
/// or Positive otherwise.
fn update_flags(registers: &mut [u16; REGISTER_COUNT], reg: u16) {
    let value = registers[reg as usize];
    if value == 0 {
        registers[Register::Cond] = ConditionFlag::Zro.into();
    } else if (value >> 15) == 1 {
        registers[Register::Cond] = ConditionFlag::Neg.into();
    } else {
        registers[Register::Cond] = ConditionFlag::Pos.into();
    }
}

/// The LC-3 has 10 registers, each 16 bits:
/// - 8 general purpose registers (R0-R7)
/// - 1 program counter (PC) register
/// - 1 condition flags (COND) register
#[derive(Copy, Clone)]
#[allow(unused)]
pub enum Register {
    /// General purpose register 0
    R0 = 0,
    /// General purpose register 1
    R1 = 1,
    /// General purpose register 2
    R2 = 2,
    /// General purpose register 3
    R3 = 3,
    /// General purpose register 4
    R4 = 4,
    /// General purpose register 5
    R5 = 5,
    /// General purpose register 6
    R6 = 6,
    /// General purpose register 7 (Some architectures use this as Stack Pointer)
    R7 = 7,
    /// Program Counter: Contains the address of the next instruction to be executed
    PC = 8,
    /// Condition Flags: Stores the status of the most recent ALU operation (Negative, Zero, or Positive)
    Cond = 9,
}

pub const REGISTER_COUNT: usize = 10;

impl Index<Register> for [u16] {
    type Output = u16;
    fn index(&self, index: Register) -> &Self::Output {
        &self[index as usize]
    }
}

impl IndexMut<Register> for [u16] {
    fn index_mut(&mut self, index: Register) -> &mut Self::Output {
        &mut self[index as usize]
    }
}

#[derive(Copy, Clone, Debug)]
pub enum MemMapRegister {
    /// - KBSR: Keyboard status register
    Kbsr = 0xFE00,
    /// - KBDR: Keyboard data register
    Kbdr = 0xFE02,
    /// - DSR: Display status register
    Dsr = 0xFE04,
    /// - DDR: Display data register
    Ddr = 0xFE06,
    /// - MCR: Machine control register
    Mcr = 0xFFFE,
}

impl PartialEq<u16> for MemMapRegister {
    fn eq(&self, other: &u16) -> bool {
        *self as u16 == *other
    }
}
