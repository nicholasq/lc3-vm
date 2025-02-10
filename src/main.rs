use std::ops::{Index, IndexMut};

/// The LC-3 has 10 registers, each 16 bits:
/// - 8 general purpose registers (R0-R7)
/// - 1 program counter (PC) register
/// - 1 condition flags (COND) register
#[derive(Copy, Clone)]
enum Register {
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

const REGISTER_COUNT: usize = 10;

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

/// The LC-3 instruction set consists of 16 opcodes.
/// Each instruction is 16 bits long with the first 4 bits containing the opcode.
#[derive(Clone, Copy)]
enum Opcode {
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
            _ => panic!("invalid opcode"),
        }
    }
}

/// Condition Flags indicate the status of the most recent ALU operation:
#[derive(Clone, Copy)]
enum ConditionFlag {
    /// - Pos: Indicates the result was positive
    Pos = 1 << 0,
    /// - Zro: Indicates the result was zero
    Zro = 1 << 1,
    /// - Neg: Indicates the result was negative
    Neg = 1 << 2,
}

/// The maximum amount of memory supported by the VM (64K)
const MEMORY_MAX: usize = 1 << 16;
/// Starting address in memory where program execution begins (0x3000)
const PC_START: u16 = 0x3000;
/// Last valid address of memory for user programs
const END_OF_USERSPACE: u16 = 0xFDFF;

struct Vm {
    memory: [u16; MEMORY_MAX],
    registers: [u16; REGISTER_COUNT],
}

impl Vm {
    fn new() -> Vm {
        Vm {
            memory: [0; MEMORY_MAX],
            registers: [0; REGISTER_COUNT],
        }
    }

    fn load_program(&mut self, image: &[u8]) {
        // The first 2 bytes of the program image contain the address where the program should be loaded,
        // but since we always load at PC_START we skip them
        for i in 2..image.len() {
            if i % 2 == 0 {
                self.memory[PC_START as usize + (i - 2) / 2] =
                    u16::from_be_bytes([image[i], image[i + 1]]);
            }
        }
    }

    fn execute_program(&mut self) {
        loop {
            if self.registers[Register::PC] > END_OF_USERSPACE {
                break;
            }
            let instr: u16 = self.memory[self.registers[Register::PC] as usize];
            self.registers[Register::PC] += 1;
            self.execute_instruction(instr);
        }
    }

    fn execute_instruction(&mut self, instr: u16) {
        let opcode = (instr >> 12) & 0xF;
        match Opcode::from(opcode) {
            Opcode::Add => self.execute_add(instr),
            Opcode::Ldi => self.execute_ldi(instr),
            Opcode::And => self.execute_and(instr),
            Opcode::Not => self.execute_not(instr),
            Opcode::Br => self.execute_branch(instr),
            _ => panic!("Unsupported opcode: {}", opcode),
        }
    }

    fn execute_add(&mut self, instr: u16) {
        let dest_reg = (instr >> 9) & 0x7;
        let src_reg1 = (instr >> 6) & 0x7;
        let imm_flag = (instr >> 5) & 0x1;

        if imm_flag == 1 {
            let imm5 = sign_extend(instr & 0x1F, 5);
            self.registers[dest_reg as usize] =
                self.registers[src_reg1 as usize].wrapping_add(imm5);
        } else {
            let src_reg2 = instr & 0x7;
            self.registers[dest_reg as usize] =
                self.registers[src_reg1 as usize].wrapping_add(self.registers[src_reg2 as usize]);
        }
        update_flags(&mut self.registers, dest_reg);
    }

    fn execute_ldi(&mut self, instr: u16) {
        let dest = (instr >> 9) & 0x7;
        let pc_offset = sign_extend(instr & 0x1FF, 9);
        let addr = self.registers[Register::PC].wrapping_add(pc_offset);
        let final_addr = self.memory[addr as usize];

        self.registers[dest as usize] = self.memory[final_addr as usize];

        update_flags(&mut self.registers, dest);
    }

    fn execute_and(&mut self, instr: u16) {
        let dest_reg = (instr >> 9) & 0x7;
        let src_reg1 = (instr >> 6) & 0x7;
        let imm_flag = (instr >> 5) & 1;

        if imm_flag == 1 {
            let imm5 = sign_extend(instr & 0x1F, 5);
            self.registers[dest_reg as usize] = self.registers[src_reg1 as usize] & imm5;
        } else {
            let src_reg2 = instr & 0x7;
            self.registers[dest_reg as usize] =
                self.registers[src_reg1 as usize] & self.registers[src_reg2 as usize];
        }

        // Update the condition flags based on the result.
        update_flags(&mut self.registers, dest_reg);
    }

    fn execute_not(&mut self, instr: u16) {
        let dest_reg = (instr >> 9) & 0x7;
        let src_reg = (instr >> 6) & 0x7;
        self.registers[dest_reg as usize] = !self.registers[src_reg as usize];
        update_flags(&mut self.registers, dest_reg);
    }

    fn execute_branch(&mut self, instr: u16) {
        let pc_offset = sign_extend(instr & 0x1FF, 9);
        let nzp_flags = (instr >> 9) & 0x7;

        // The branch is taken if any of the set flags (nzp_flags) match with the current
        // condition flags in the Cond register (bitwise AND > 0)
        if nzp_flags & self.registers[Register::Cond] > 0 {
            self.registers[Register::PC] = self.registers[Register::PC].wrapping_add(pc_offset);
        }
    }
}

/// Takes a 16-bit value and sign extends it from a given bit position by filling all bits
/// to the left of the sign bit with the same value as the sign bit.
fn sign_extend(x: u16, bit_count: u16) -> u16 {
    if ((x >> (bit_count - 1)) & 1) == 1 {
        x | (0xFFFF << bit_count)
    } else {
        x
    }
}

/// Updates the condition flag register based on the value in the specified register.
/// Sets the flag to Zero if the value is 0, Negative if the most significant bit is 1,
/// or Positive otherwise.
fn update_flags(registers: &mut [u16; REGISTER_COUNT], reg: u16) {
    let value = registers[reg as usize];
    if value == 0 {
        registers[Register::Cond] = ConditionFlag::Zro as u16;
    } else if (value >> 15) == 1 {
        registers[Register::Cond] = ConditionFlag::Neg as u16;
    } else {
        registers[Register::Cond] = ConditionFlag::Pos as u16;
    }
}

fn main() {
    let args: Vec<String> = std::env::args().collect();

    if args.len() < 2 {
        eprintln!("Usage: lc3-vm [image-file1]");
        std::process::exit(1);
    }

    let image = std::fs::read(&args[1]).unwrap();

    let mut vm = Vm::new();
    vm.registers[Register::Cond] = ConditionFlag::Zro as u16;
    vm.registers[Register::PC] = PC_START;
    vm.load_program(&image);
    vm.execute_program();
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_add_instruction() {
        let mut vm = Vm::new();

        // Test register-register addition (ADD R2, R0, R1)
        // Format: 0001 010 000 0 00 001
        // R2 = R0 + R1
        vm.registers[Register::R0 as usize] = 5; // Set R0 = 5
        vm.registers[Register::R1 as usize] = 3; // Set R1 = 3
        vm.execute_instruction(0b0001_0100_0000_0001); // ADD R2, R0, R1
        assert_eq!(vm.registers[Register::R2 as usize], 8); // Check result
        assert_eq!(
            vm.registers[Register::Cond as usize],
            ConditionFlag::Pos as u16
        ); // Check flag

        // Test register-immediate addition (ADD R3, R0, #-2)
        // Format: 0001 011 000 1 11110
        // R3 = R0 + (-2)
        vm.registers[Register::R0 as usize] = 5; // Set R0 = 5
        vm.execute_instruction(0b0001_0110_0011_1110); // ADD R3, R0, #-2
        assert_eq!(vm.registers[Register::R3 as usize], 3); // Check result
        assert_eq!(
            vm.registers[Register::Cond as usize],
            ConditionFlag::Pos as u16
        ); // Check flag

        // Test addition resulting in zero
        vm.registers[Register::R0 as usize] = 2; // Set R0 = 2
        vm.registers[Register::R1 as usize] = -2i16 as u16; // Set R1 = -2
        vm.execute_instruction(0b0001_0100_0000_0001); // ADD R2, R0, R1
        assert_eq!(vm.registers[Register::R2 as usize], 0); // Check result
        assert_eq!(
            vm.registers[Register::Cond as usize],
            ConditionFlag::Zro as u16
        ); // Check flag

        // Test addition resulting in negative number
        vm.registers[Register::R0 as usize] = 1; // Set R0 = 1
        vm.execute_instruction(0b0001_0110_0011_1101); // ADD R3, R0, #-3
        assert_eq!(vm.registers[Register::R3 as usize], -2i16 as u16); // Check result
        assert_eq!(
            vm.registers[Register::Cond as usize],
            ConditionFlag::Neg as u16
        ); // Check flag

        // Test overflow wrapping
        vm.registers[Register::R0 as usize] = 0x7FFF; // Set R0 to maximum positive value
        vm.registers[Register::R1 as usize] = 1; // Set R1 = 1
        vm.execute_instruction(0b0001_0100_0000_0001); // ADD R2, R0, R1
        assert_eq!(vm.registers[Register::R2 as usize], 0x8000); // Should wrap to negative
        assert_eq!(
            vm.registers[Register::Cond as usize],
            ConditionFlag::Neg as u16
        ); // Check flag
    }

    #[test]
    fn test_ldi_instruction() {
        #[derive(Copy, Clone)]
        struct LdiTestCase {
            pc: u16,
            offset: u16,
            intermediate_addr: u16,
            final_value: u16,
            expected_reg: Register,
            expected_value: u16,
            expected_flag: ConditionFlag,
        }

        let test_cases = vec![
            LdiTestCase {
                pc: 0x3000,
                offset: 5,
                intermediate_addr: 0x4000,
                final_value: 42,
                expected_reg: Register::R1,
                expected_value: 42,
                expected_flag: ConditionFlag::Pos,
            },
            LdiTestCase {
                pc: 0x3005,
                offset: 0x1FD, // -3 in 9-bit two's complement
                intermediate_addr: 0x5000,
                final_value: 0,
                expected_reg: Register::R2,
                expected_value: 0,
                expected_flag: ConditionFlag::Zro,
            },
            LdiTestCase {
                pc: 0x3000,
                offset: 1,
                intermediate_addr: 0x4000,
                final_value: 0x8000,
                expected_reg: Register::R3,
                expected_value: 0x8000,
                expected_flag: ConditionFlag::Neg,
            },
            LdiTestCase {
                pc: 0x3000,
                offset: 0,
                intermediate_addr: 0x4000,
                final_value: 100,
                expected_reg: Register::R4,
                expected_value: 100,
                expected_flag: ConditionFlag::Pos,
            },
            LdiTestCase {
                pc: 0x0100,
                offset: 0x00FF, // 255 in 9-bit
                intermediate_addr: 0x0200,
                final_value: 777,
                expected_reg: Register::R5,
                expected_value: 777,
                expected_flag: ConditionFlag::Pos,
            },
            LdiTestCase {
                pc: 0x3000,
                offset: 0x180, // -128 in 9-bit two's complement
                intermediate_addr: 0x4000,
                final_value: 200,
                expected_reg: Register::R6,
                expected_value: 200,
                expected_flag: ConditionFlag::Pos,
            },
        ];

        for case in test_cases {
            let mut vm = Vm::new();
            vm.registers[Register::PC] = case.pc;
            let instruction: u16 = (0b1010 << 12) | ((case.expected_reg as u16) << 9) | case.offset;
            let addr = case.pc.wrapping_add(sign_extend(case.offset, 9));
            vm.memory[addr as usize] = case.intermediate_addr;
            vm.memory[case.intermediate_addr as usize] = case.final_value;

            vm.execute_instruction(instruction);

            assert_eq!(
                vm.registers[case.expected_reg as usize],
                case.expected_value
            );
            assert_eq!(
                vm.registers[Register::Cond as usize],
                case.expected_flag as u16
            );
        }
    }

    #[test]
    fn test_and_instruction() {
        let mut vm = Vm::new();

        // Test register-register AND
        vm.registers[Register::R0 as usize] = 0xFF00;
        vm.registers[Register::R1 as usize] = 0x0F0F;
        vm.execute_instruction(0b0101_0100_0000_0001); // AND R2, R0, R1
        assert_eq!(vm.registers[Register::R2 as usize], 0x0F00);
        assert_eq!(
            vm.registers[Register::Cond as usize],
            ConditionFlag::Pos as u16
        );

        // Test register-immediate AND
        vm.registers[Register::R0 as usize] = 0xFFFF;
        vm.execute_instruction(0b0101_0110_0010_1111); // AND R3, R0, #15 (imm5 = 15)
        assert_eq!(vm.registers[Register::R3 as usize], 15);
        assert_eq!(
            vm.registers[Register::Cond as usize],
            ConditionFlag::Pos as u16
        );

        // Test zero result
        vm.registers[Register::R0 as usize] = 0xFF00;
        vm.registers[Register::R1 as usize] = 0x00FF;
        vm.execute_instruction(0b0101_0100_0000_0001); // AND R2, R0, R1
        assert_eq!(vm.registers[Register::R2 as usize], 0);
        assert_eq!(
            vm.registers[Register::Cond as usize],
            ConditionFlag::Zro as u16
        );

        // Test negative result
        vm.registers[Register::R0 as usize] = 0x8000;
        vm.execute_instruction(0b0101_0110_0011_1111); // AND R3, R0, #-1
        assert_eq!(vm.registers[Register::R3 as usize], 0x8000);
        assert_eq!(
            vm.registers[Register::Cond as usize],
            ConditionFlag::Neg as u16
        );

        // Test with all bits set
        vm.registers[Register::R0 as usize] = 0xFFFF;
        vm.registers[Register::R1 as usize] = 0xFFFF;
        vm.execute_instruction(0b0101_0100_0000_0001); // AND R2, R0, R1
        assert_eq!(vm.registers[Register::R2 as usize], 0xFFFF);
        assert_eq!(
            vm.registers[Register::Cond as usize],
            ConditionFlag::Neg as u16
        );

        // Test with no bits set
        vm.registers[Register::R0 as usize] = 0;
        vm.registers[Register::R1 as usize] = 0xFFFF;
        vm.execute_instruction(0b0101_0100_0000_0001); // AND R2, R0, R1
        assert_eq!(vm.registers[Register::R2 as usize], 0);
        assert_eq!(
            vm.registers[Register::Cond as usize],
            ConditionFlag::Zro as u16
        );

        // Test immediate with sign extension
        vm.registers[Register::R0 as usize] = 0xFFFF;
        vm.execute_instruction(0b0101_0110_0011_0000); // AND R3, R0, #-16
        assert_eq!(vm.registers[Register::R3 as usize], 0xFFF0);
        assert_eq!(
            vm.registers[Register::Cond as usize],
            ConditionFlag::Neg as u16
        );
    }

    #[test]
    fn test_not_instruction() {
        let mut vm = Vm::new();

        // Test NOT of all zeros
        vm.registers[Register::R0 as usize] = 0x0000;
        vm.execute_instruction(0b1001_0010_0011_1111); // NOT R1, R0
        assert_eq!(vm.registers[Register::R1 as usize], 0xFFFF);
        assert_eq!(
            vm.registers[Register::Cond as usize],
            ConditionFlag::Neg as u16
        );

        // Test NOT of all ones
        vm.registers[Register::R2 as usize] = 0xFFFF;
        vm.execute_instruction(0b1001_0110_0111_1111); // NOT R3, R2
        assert_eq!(vm.registers[Register::R3 as usize], 0x0000);
        assert_eq!(
            vm.registers[Register::Cond as usize],
            ConditionFlag::Zro as u16
        );

        // Test NOT of alternating bits (0101 -> 1010)
        vm.registers[Register::R4 as usize] = 0x5555;
        vm.execute_instruction(0b1001_1011_0011_1111); // NOT R5, R4
        assert_eq!(vm.registers[Register::R5 as usize], 0xAAAA);
        assert_eq!(
            vm.registers[Register::Cond as usize],
            ConditionFlag::Neg as u16
        );

        // Test NOT of positive number
        vm.registers[Register::R0 as usize] = 0x7FFF;
        vm.execute_instruction(0b1001_0010_0011_1111); // NOT R1, R0
        assert_eq!(vm.registers[Register::R1 as usize], 0x8000);
        assert_eq!(
            vm.registers[Register::Cond as usize],
            ConditionFlag::Neg as u16
        );
    }

    #[test]
    fn test_execute_branch() {
        struct TestCase {
            initial_pc: u16,
            initial_cond: u16,
            branch_cond: u16,
            offset: i16, // signed offset
            expected_pc: u16,
        }
        let test_cases = vec![
            // Branch taken: positive offset.
            TestCase {
                initial_pc: 0x3000,
                initial_cond: ConditionFlag::Zro as u16,
                branch_cond: ConditionFlag::Zro as u16,
                offset: 5,
                expected_pc: 0x3000u16.wrapping_add(5),
            },
            // Branch not taken: flag mismatch.
            TestCase {
                initial_pc: 0x3000,
                initial_cond: ConditionFlag::Pos as u16,
                branch_cond: ConditionFlag::Zro as u16,
                offset: 10,
                expected_pc: 0x3000,
            },
            // Branch taken: negative offset.
            TestCase {
                initial_pc: 0x3005,
                initial_cond: ConditionFlag::Neg as u16,
                branch_cond: ConditionFlag::Neg as u16,
                offset: -3,
                expected_pc: 0x3005u16.wrapping_add((-3i16) as u16),
            },
            // Edge case: zero offset with matching flag.
            TestCase {
                initial_pc: 0x4000,
                initial_cond: (ConditionFlag::Pos as u16)
                    | (ConditionFlag::Neg as u16)
                    | (ConditionFlag::Zro as u16),
                branch_cond: 0b111,
                offset: 0,
                expected_pc: 0x4000,
            },
        ];
        for tc in test_cases {
            let mut vm = Vm::new();
            vm.registers[Register::PC] = tc.initial_pc;
            vm.registers[Register::Cond] = tc.initial_cond;
            // Encode the offset as 9-bit two's complement.
            let offset_encoded = (tc.offset as u16) & 0x1FF;
            // Construct branch instruction:
            // Bits 15-12: opcode (BR, 0) ; Bits 11-9: branch condition ; Bits 8-0: offset.
            let instr = (0 << 12) | ((tc.branch_cond & 0x7) << 9) | offset_encoded;
            vm.execute_branch(instr);
            assert_eq!(
                    vm.registers[Register::PC],
                    tc.expected_pc,
                    "Failure for test case: initial_pc=0x{:04X}, initial_cond=0x{:X}, branch_cond=0x{:X}, offset={}",
                    tc.initial_pc, tc.initial_cond, tc.branch_cond, tc.offset
                );
        }
    }
}
