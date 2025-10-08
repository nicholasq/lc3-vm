use std::fmt::{Display, Formatter};

use crate::{cpu::Register, util::sign_extend};

/// The LC-3 instruction set consists of 16 opcodes.
/// Each instruction is 16 bits long with the first 4 bits containing the opcode.
#[derive(Clone, Copy)]
pub enum Opcode {
    /// Branch: Conditional branch based on condition flags
    /// Format: BR[n][z][p] PCoffset9
    Br = 0b0000,
    /// Add: Addition operation between registers or register and immediate
    /// Format: ADD DR, SR1, SR2 or ADD DR, SR1, imm5
    Add = 0b0001,
    /// Load: Loads a value from memory into a register
    /// Format: LD DR, PCoffset9
    Ld = 0b0010,
    /// Store: Stores a register value into memory
    /// Format: ST SR, PCoffset9
    St = 0b0011,
    /// Jump to Subroutine: Saves return address and jumps to subroutine
    /// Format: JSR PCoffset11 or JSRR BaseR
    Jsr = 0b0100,
    /// Bitwise AND: Performs AND operation between registers or register and immediate
    /// Format: AND DR, SR1, SR2 or AND DR, SR1, imm5
    And = 0b0101,
    /// Load Register: Loads a value from memory address (base + offset)
    /// Format: LDR DR, BaseR, offset6
    Ldr = 0b0110,
    /// Store Register: Stores a value to memory address (base + offset)
    /// Format: STR SR, BaseR, offset6
    Str = 0b0111,
    /// Return from Interrupt: Unused in this implementation
    Rti = 0b1000,
    /// Bitwise NOT: Performs NOT operation on register value
    /// Format: NOT DR, SR
    Not = 0b1001,
    /// Load Indirect: Loads a value using indirect addressing
    /// Format: LDI DR, PCoffset9
    Ldi = 0b1010,
    /// Store Indirect: Stores a value using indirect addressing
    /// Format: STI SR, PCoffset9
    Sti = 0b1011,
    /// Jump: Unconditional jump to address in register
    /// Format: JMP BaseR
    Jmp = 0b1100,
    /// Reserved: Unused opcode
    Res = 0b1101,
    /// Load Effective Address: Loads address calculation result into register
    /// Format: LEA DR, PCoffset9
    Lea = 0b1110,
    /// Trap: System call/OS routine
    /// Format: TRAP trapvect8
    Trap = 0b1111,
}

impl From<u16> for Opcode {
    fn from(value: u16) -> Self {
        match value {
            0 => Opcode::Br,
            1 => Opcode::Add,
            2 => Opcode::Ld,
            3 => Opcode::St,
            4 => Opcode::Jsr,
            5 => Opcode::And,
            6 => Opcode::Ldr,
            7 => Opcode::Str,
            8 => Opcode::Rti,
            9 => Opcode::Not,
            10 => Opcode::Ldi,
            11 => Opcode::Sti,
            12 => Opcode::Jmp,
            13 => Opcode::Res,
            14 => Opcode::Lea,
            15 => Opcode::Trap,
            _ => panic!("invalid opcode: 0x{:x}", value),
        }
    }
}

/// Represents a decoded LC-3 instruction.
///
/// Each variant corresponds to a specific LC-3 instruction type, holding the relevant operands and flags.
/// This enum is used to model the parsed instructions after decoding a 16-bit LC-3 opcode.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Instruction {
    Add(BaseALOperation),
    And(BaseALOperation),
    Br {
        n: bool,
        z: bool,
        p: bool,
        pc_offset: u16,
    },
    Jmp(Jmp),
    Jsr(Jsr),
    Ld(BaseLoadOperation),
    Ldi(BaseLoadOperation),
    Ldr {
        dest_reg: u16,
        base_reg: u16,
        offset: u16,
    },
    Lea(BaseLoadOperation),
    Not {
        dest_reg: u16,
        src_reg: u16,
    },
    Rti,
    St(BaseStoreOperation),
    Sti(BaseStoreOperation),
    Str {
        src_reg: u16,
        base_reg: u16,
        offset: u16,
    },
    Trap(TrapCode),
}

/// Represents a basic arithmetic or logic operation in the instruction set.
///
/// This enum distinguishes between operations that use an immediate value and those that use two source registers.
///
/// - `Immediate`: Operation with a destination register, a source register, and an immediate value.
/// - `Register`: Operation with a destination register and two source registers.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BaseALOperation {
    Immediate {
        dest_reg: u16,
        src_reg: u16,
        imm: u16,
    },
    Register {
        dest_reg: u16,
        src_reg1: u16,
        src_reg2: u16,
    },
}

/// Represents a base load operation in the instruction set.
///
/// This struct contains the destination register and the program counter offset
/// for a load operation.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct BaseLoadOperation {
    /// The destination register where the value will be loaded.
    pub dest_reg: u16,
    /// The offset from the program counter used in the operation.
    pub pc_offset: u16,
}

/// Represents a base store operation in the instruction set.
///
/// This struct contains the source register and the program counter offset
/// for a store operation.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct BaseStoreOperation {
    /// The source register containing the value to be stored.
    pub src_reg: u16,
    /// The offset from the program counter used in the operation.
    pub pc_offset: u16,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Jmp {
    Jmp { base_reg: u16 },
    Ret,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Jsr {
    Jsr { pc_offset: u16 },
    Jsrr { base_reg: u16 },
}

pub trait InstructionDecoder {
    fn decode(&self) -> Result<Instruction, String>;
}

impl InstructionDecoder for u16 {
    fn decode(&self) -> Result<Instruction, String> {
        let opcode = (self >> 12) & 0xF;
        match Opcode::from(opcode) {
            Opcode::Add => {
                let dest_reg = (self >> 9) & 0x7;
                let src_reg1 = (self >> 6) & 0x7;
                let imm_flag = (self >> 5) & 0x1;

                if imm_flag == 1 {
                    let imm = sign_extend(self & 0x1F, 5);
                    Ok(Instruction::Add(BaseALOperation::Immediate {
                        dest_reg,
                        src_reg: src_reg1,
                        imm,
                    }))
                } else {
                    let src_reg2 = self & 0x7;
                    Ok(Instruction::Add(BaseALOperation::Register {
                        dest_reg,
                        src_reg1,
                        src_reg2,
                    }))
                }
            }
            Opcode::Ldi => {
                let dest_reg = (self >> 9) & 0x7;
                let pc_offset = sign_extend(self & 0x1FF, 9);
                Ok(Instruction::Ldi(BaseLoadOperation {
                    dest_reg,
                    pc_offset,
                }))
            }
            Opcode::And => {
                let dest_reg = (self >> 9) & 0x7;
                let src_reg1 = (self >> 6) & 0x7;
                let imm_flag = (self >> 5) & 1;

                if imm_flag == 1 {
                    let imm = sign_extend(self & 0x1F, 5);
                    Ok(Instruction::And(BaseALOperation::Immediate {
                        dest_reg,
                        src_reg: src_reg1,
                        imm,
                    }))
                } else {
                    let src_reg2 = self & 0x7;
                    Ok(Instruction::And(BaseALOperation::Register {
                        dest_reg,
                        src_reg1,
                        src_reg2,
                    }))
                }
            }
            Opcode::Not => {
                let dest_reg = (self >> 9) & 0x7;
                let src_reg = (self >> 6) & 0x7;
                Ok(Instruction::Not { dest_reg, src_reg })
            }
            Opcode::Br => {
                let pc_offset = sign_extend(self & 0x1FF, 9);
                let nzp_flags = (self >> 9) & 0x7;
                if nzp_flags == 0 {
                    return Err("Invalid BR instruction. nzp_flags cannot be zero.".to_string());
                }
                Ok(Instruction::Br {
                    pc_offset,
                    n: nzp_flags & 0x4 == 4,
                    z: nzp_flags & 0x2 == 2,
                    p: nzp_flags & 0x1 == 1,
                })
            }
            Opcode::Jmp => {
                let base_reg = (self >> 6) & 0x7;
                if base_reg == Register::R7 as u16 {
                    return Ok(Instruction::Jmp(Jmp::Ret));
                }
                Ok(Instruction::Jmp(Jmp::Jmp { base_reg }))
            }
            Opcode::Jsr => {
                if (self >> 11) & 1 == 1 {
                    let pc_offset = sign_extend(self & 0x7FF, 11);
                    Ok(Instruction::Jsr(Jsr::Jsr { pc_offset }))
                } else {
                    let base_reg = (self >> 6) & 0x7;
                    Ok(Instruction::Jsr(Jsr::Jsrr { base_reg }))
                }
            }
            Opcode::Ld => {
                let dest_reg = (self >> 9) & 0x7;
                let pc_offset = sign_extend(self & 0x1FF, 9);
                Ok(Instruction::Ld(BaseLoadOperation {
                    dest_reg,
                    pc_offset,
                }))
            }
            Opcode::Ldr => {
                let dest_reg = (self >> 9) & 0x7;
                let base_reg = (self >> 6) & 0x7;
                let offset = sign_extend(self & 0x3F, 6);
                Ok(Instruction::Ldr {
                    dest_reg,
                    base_reg,
                    offset,
                })
            }
            Opcode::Lea => {
                let dest_reg = (self >> 9) & 0x7;
                let pc_offset = sign_extend(self & 0x1FF, 9);
                Ok(Instruction::Lea(BaseLoadOperation {
                    dest_reg,
                    pc_offset,
                }))
            }
            Opcode::St => {
                let src_reg = (self >> 9) & 0x7;
                let pc_offset = sign_extend(self & 0x1FF, 9);
                Ok(Instruction::St(BaseStoreOperation { src_reg, pc_offset }))
            }
            Opcode::Sti => {
                let src_reg = (self >> 9) & 0x7;
                let pc_offset = sign_extend(self & 0x1FF, 9);
                Ok(Instruction::Sti(BaseStoreOperation { src_reg, pc_offset }))
            }
            Opcode::Str => {
                let src_reg = (self >> 9) & 0x7;
                let base_reg = (self >> 6) & 0x7;
                let offset = sign_extend(self & 0x3F, 6);
                Ok(Instruction::Str {
                    src_reg,
                    base_reg,
                    offset,
                })
            }
            Opcode::Trap => {
                let trap_vect = self & 0xFF;
                let unused = self >> 8 & 0xF;
                if unused != 0 {
                    Err(format!(
                        "Invalid unused bits in TRAP instruction: {}",
                        unused
                    ))
                } else {
                    Ok(Instruction::Trap(TrapCode::from(trap_vect)))
                }
            }
            Opcode::Rti => Ok(Instruction::Rti),
            _ => Err(format!("Unsupported opcode: {}", opcode)),
        }
    }
}

/// Condition Flags indicate the status of the most recent ALU operation:
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ConditionFlag {
    /// - Pos: Indicates the result was positive
    Pos = 0x0,
    /// - Zro: Indicates the result was zero
    Zro = 0x1,
    /// - Neg: Indicates the result was negative
    Neg = 0x2,
}

impl From<ConditionFlag> for u16 {
    fn from(flag: ConditionFlag) -> Self {
        flag as u16
    }
}

/// Represents the trap codes (system calls/OS routines) available in the LC-3 instruction set.
///
/// These codes are used with the TRAP opcode to invoke specific system functions.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TrapCode {
    /// - Getc: Read a character from the keyboard
    Getc = 0x20,
    /// - Out: Write a character to the screen
    Out = 0x21,
    /// - Puts: Write a string to the screen
    Puts = 0x22,
    /// - In: Read a string from the keyboard
    In = 0x23,
    /// - Putsp: Write a string to the screen in hexadecimal
    Putsp = 0x24,
    /// - Halt: Halt the program
    Halt = 0x25,
}

impl From<u16> for TrapCode {
    fn from(value: u16) -> Self {
        match value {
            0x20 => TrapCode::Getc,
            0x21 => TrapCode::Out,
            0x22 => TrapCode::Puts,
            0x23 => TrapCode::In,
            0x24 => TrapCode::Putsp,
            0x25 => TrapCode::Halt,
            _ => panic!("invalid trapcode: 0x{:x}", value),
        }
    }
}

impl Display for TrapCode {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            TrapCode::Getc => write!(f, "Getc"),
            TrapCode::Out => write!(f, "Out"),
            TrapCode::Puts => write!(f, "Puts"),
            TrapCode::In => write!(f, "In"),
            TrapCode::Putsp => write!(f, "Putsp"),
            TrapCode::Halt => write!(f, "Halt"),
        }
    }
}
