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
#[derive(Clone, Copy, Debug)]
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
            Opcode::Jmp => self.execute_jmp(instr),
            Opcode::Jsr => self.execute_jsr(instr),
            Opcode::Ld => self.execute_load(instr),
            Opcode::Ldr => self.execute_load_reg(instr),
            Opcode::Lea => self.execute_load_eff_addr(instr),
            Opcode::St => self.execute_store(instr),
            Opcode::Sti => self.execute_sti(instr),
            Opcode::Str => self.execute_str_reg(instr),
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

    fn execute_jmp(&mut self, instr: u16) {
        let base_reg = (instr >> 6) & 0x7;
        self.registers[Register::PC] = self.registers[base_reg as usize];
    }

    fn execute_jsr(&mut self, instr: u16) {
        // Save current PC in R7 (link register)
        self.registers[Register::R7] = self.registers[Register::PC];

        // Check if using JSR (1) or JSRR (0) mode
        if (instr >> 11) & 1 == 1 {
            // JSR: PC-relative jump
            let long_pc_offset = sign_extend(instr & 0x7FF, 11);
            self.registers[Register::PC] =
                self.registers[Register::PC].wrapping_add(long_pc_offset);
        } else {
            // JSRR: Register-based jump
            let base_reg = (instr >> 6) & 0x7;
            self.registers[Register::PC] = self.registers[base_reg as usize];
        }
    }

    fn execute_load(&mut self, instr: u16) {
        let dest_reg = (instr >> 9) & 0x7;
        let pc_offset = sign_extend(instr & 0x1FF, 9);

        // Calculate memory address by adding offset to current PC
        let addr = self.registers[Register::PC].wrapping_add(pc_offset);

        // Load value from memory into destination register
        self.registers[dest_reg as usize] = self.memory[addr as usize];

        // Update condition flags based on loaded value
        update_flags(&mut self.registers, dest_reg);
    }

    fn execute_load_reg(&mut self, instr: u16) {
        let dest_reg = (instr >> 9) & 0x7;
        let base_reg = (instr >> 6) & 0x7;
        let offset = sign_extend(instr & 0x3F, 6);

        // Calculate memory address by adding offset to base register value
        let addr = self.registers[base_reg as usize].wrapping_add(offset);

        // Load value from memory into destination register
        self.registers[dest_reg as usize] = self.memory[addr as usize];

        // Update condition flags based on loaded value
        update_flags(&mut self.registers, dest_reg);
    }

    fn execute_load_eff_addr(&mut self, instr: u16) {
        let dest_reg = (instr >> 9) & 0x7;
        let pc_offset = sign_extend(instr & 0x1FF, 9);

        // Calculate effective address by adding offset to current PC
        self.registers[dest_reg as usize] = self.registers[Register::PC].wrapping_add(pc_offset);

        // Update condition flags based on calculated address
        update_flags(&mut self.registers, dest_reg);
    }

    fn execute_store(&mut self, instr: u16) {
        // Extract source register from instruction bits [11:9]
        let src_reg = (instr >> 9) & 0x7;
        // Sign-extend the 9-bit PCoffset from bits [8:0]
        let pc_offset = sign_extend(instr & 0x1FF, 9);
        // Use the current PC (which is already incremented) to compute the target address
        let addr = self.registers[Register::PC].wrapping_add(pc_offset);
        // Store the value from the source register into memory
        self.memory[addr as usize] = self.registers[src_reg as usize];
    }

    fn execute_sti(&mut self, instr: u16) {
        // Extract source register (SR) where the value to store is located.
        let src_reg = (instr >> 9) & 0x7;
        // Extract and sign extend a 9-bit PC offset.
        let pc_offset = sign_extend(instr & 0x1FF, 9);
        // Compute the intermediate address: (incremented) PC plus the offset.
        // Note: In our design the PC is already incremented after fetching.
        let intermediate_addr = self.registers[Register::PC].wrapping_add(pc_offset);
        // Look up the final target address stored in memory at that location.
        let final_addr = self.memory[intermediate_addr as usize];
        // Store the contents of the source register into memory at final_addr.
        self.memory[final_addr as usize] = self.registers[src_reg as usize];
    }

    fn execute_str_reg(&mut self, instr: u16) {
        let sr = (instr >> 9) & 0x7; // Source register whose content to store.
        let base_r = (instr >> 6) & 0x7; // Register holding base address.
        let offset6 = sign_extend(instr & 0x3F, 6); // Sign-extend the 6-bit offset.
        let addr = self.registers[base_r as usize].wrapping_add(offset6);
        self.memory[addr as usize] = self.registers[sr as usize];
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

    #[test]
    fn test_execute_jmp() {
        struct TestCase {
            name: &'static str,
            base_reg: Register,
            base_reg_value: u16,
            initial_pc: u16,
            expected_pc: u16,
        }

        let test_cases = vec![
            // Basic jump forward
            TestCase {
                name: "Basic jump forward",
                base_reg: Register::R2,
                base_reg_value: 0x3100,
                initial_pc: 0x3000,
                expected_pc: 0x3100,
            },
            // Jump backward
            TestCase {
                name: "Jump backward",
                base_reg: Register::R3,
                base_reg_value: 0x2F00,
                initial_pc: 0x3000,
                expected_pc: 0x2F00,
            },
            // RET case (using R7)
            TestCase {
                name: "RET case using R7",
                base_reg: Register::R7,
                base_reg_value: 0x3010,
                initial_pc: 0x3000,
                expected_pc: 0x3010,
            },
            // Jump to current PC location
            TestCase {
                name: "Jump to current PC",
                base_reg: Register::R4,
                base_reg_value: 0x3000,
                initial_pc: 0x3000,
                expected_pc: 0x3000,
            },
            // Jump to maximum address
            TestCase {
                name: "Jump to max address",
                base_reg: Register::R1,
                base_reg_value: 0xFFFF,
                initial_pc: 0x3000,
                expected_pc: 0xFFFF,
            },
            // Jump to start of memory
            TestCase {
                name: "Jump to start of memory",
                base_reg: Register::R5,
                base_reg_value: 0x0000,
                initial_pc: 0x3000,
                expected_pc: 0x0000,
            },
        ];

        for tc in test_cases {
            let mut vm = Vm::new();

            // Setup initial state
            vm.registers[Register::PC] = tc.initial_pc;
            vm.registers[tc.base_reg as usize] = tc.base_reg_value;

            // Construct JMP instruction
            // Format: 1100 000 BaseR 000000
            let instr: u16 = (0b1100 << 12) | ((tc.base_reg as u16 & 0x7) << 6);

            // Execute the jump
            vm.execute_jmp(instr);

            assert_eq!(
                vm.registers[Register::PC],
                tc.expected_pc,
                "Failed test case: {}. Expected PC=0x{:04X}, got PC=0x{:04X}",
                tc.name,
                tc.expected_pc,
                vm.registers[Register::PC]
            );
        }
    }

    #[test]
    fn test_execute_jsr() {
        struct TestCase {
            name: &'static str,
            initial_pc: u16,
            instruction: u16,
            base_reg: Option<(Register, u16)>, // For JSRR tests: (reg, value)
            expected_pc: u16,
            expected_r7: u16,
        }

        let test_cases = vec![
            // JSR tests (PC-relative)
            TestCase {
                name: "JSR forward",
                initial_pc: 0x3000,
                instruction: 0b0100_1000_0000_1010, // JSR with positive offset (+10)
                base_reg: None,
                expected_pc: 0x300A,
                expected_r7: 0x3000,
            },
            TestCase {
                name: "JSR backward",
                initial_pc: 0x3000,
                instruction: 0b0100_1111_1111_1000, // JSR with negative offset (-8)
                base_reg: None,
                expected_pc: 0x2FF8,
                expected_r7: 0x3000,
            },
            TestCase {
                name: "JSR maximum positive offset",
                initial_pc: 0x3000,
                instruction: 0b0100_1011_1111_1111, // JSR with max positive offset
                base_reg: None,
                expected_pc: 0x33FF,
                expected_r7: 0x3000,
            },
            TestCase {
                name: "JSR maximum negative offset",
                initial_pc: 0x3000,
                instruction: 0b0100_1100_0000_0000, // JSR with max negative offset
                base_reg: None,
                expected_pc: 0x2C00,
                expected_r7: 0x3000,
            },
            // JSRR tests (register-based)
            TestCase {
                name: "JSRR basic jump",
                initial_pc: 0x3000,
                instruction: 0b0100_0000_1000_0000, // JSRR R2
                base_reg: Some((Register::R2, 0x4000)),
                expected_pc: 0x4000,
                expected_r7: 0x3000,
            },
            TestCase {
                name: "JSRR jump to zero",
                initial_pc: 0x3000,
                instruction: 0b0100_0000_1100_0000, // JSRR R3
                base_reg: Some((Register::R3, 0x0000)),
                expected_pc: 0x0000,
                expected_r7: 0x3000,
            },
            TestCase {
                name: "JSRR jump to max address",
                initial_pc: 0x3000,
                instruction: 0b0100_0001_0000_0000, // JSRR R4
                base_reg: Some((Register::R4, 0xFFFF)),
                expected_pc: 0xFFFF,
                expected_r7: 0x3000,
            },
            TestCase {
                name: "JSRR jump to current location",
                initial_pc: 0x3000,
                instruction: 0b0100_0001_0100_0000, // JSRR R5
                base_reg: Some((Register::R5, 0x3000)),
                expected_pc: 0x3000,
                expected_r7: 0x3000,
            },
        ];

        for tc in test_cases {
            let mut vm = Vm::new();

            // Setup initial state
            vm.registers[Register::PC] = tc.initial_pc;

            // Setup base register for JSRR tests if specified
            if let Some((reg, value)) = tc.base_reg {
                vm.registers[reg as usize] = value;
            }

            // Execute the instruction
            vm.execute_jsr(tc.instruction);

            // Verify PC and R7 are correct
            assert_eq!(
                vm.registers[Register::PC],
                tc.expected_pc,
                "Failed test case '{}': PC mismatch. Expected 0x{:04X}, got 0x{:04X}",
                tc.name,
                tc.expected_pc,
                vm.registers[Register::PC]
            );

            assert_eq!(
                vm.registers[Register::R7],
                tc.expected_r7,
                "Failed test case '{}': R7 mismatch. Expected 0x{:04X}, got 0x{:04X}",
                tc.name,
                tc.expected_r7,
                vm.registers[Register::R7]
            );
        }
    }

    #[test]
    fn test_execute_load() {
        struct TestCase {
            name: &'static str,
            initial_pc: u16,
            dest_reg: Register,
            offset: i16,
            memory_value: u16,
            expected_value: u16,
            expected_flag: ConditionFlag,
        }

        let test_cases = vec![
            // Basic positive offset load
            TestCase {
                name: "Load positive value with positive offset",
                initial_pc: 0x3000,
                dest_reg: Register::R1,
                offset: 5,
                memory_value: 42,
                expected_value: 42,
                expected_flag: ConditionFlag::Pos,
            },
            // Zero value load
            TestCase {
                name: "Load zero value",
                initial_pc: 0x3000,
                dest_reg: Register::R2,
                offset: 0,
                memory_value: 0,
                expected_value: 0,
                expected_flag: ConditionFlag::Zro,
            },
            // Negative value load
            TestCase {
                name: "Load negative value",
                initial_pc: 0x3000,
                dest_reg: Register::R3,
                offset: 1,
                memory_value: 0x8000,
                expected_value: 0x8000,
                expected_flag: ConditionFlag::Neg,
            },
            // Maximum positive offset
            TestCase {
                name: "Load with maximum positive offset",
                initial_pc: 0x3000,
                dest_reg: Register::R4,
                offset: 0xFF, // Maximum positive 9-bit offset
                memory_value: 100,
                expected_value: 100,
                expected_flag: ConditionFlag::Pos,
            },
            // Maximum negative offset
            TestCase {
                name: "Load with maximum negative offset",
                initial_pc: 0x3000,
                dest_reg: Register::R5,
                offset: -256, // Maximum negative 9-bit offset
                memory_value: 50,
                expected_value: 50,
                expected_flag: ConditionFlag::Pos,
            },
            // Wrap around memory
            TestCase {
                name: "Load with memory address wrap-around",
                initial_pc: 0xFFFF,
                dest_reg: Register::R6,
                offset: 5,
                memory_value: 0x4444,
                expected_value: 0x4444,
                expected_flag: ConditionFlag::Pos,
            },
            // Edge case: maximum unsigned 16-bit value
            TestCase {
                name: "Load maximum unsigned value",
                initial_pc: 0x3000,
                dest_reg: Register::R7,
                offset: 10,
                memory_value: 0xFFFF,
                expected_value: 0xFFFF,
                expected_flag: ConditionFlag::Neg,
            },
        ];

        for tc in test_cases {
            let mut vm = Vm::new();

            // Setup initial state
            vm.registers[Register::PC] = tc.initial_pc;

            // Setup memory value at target address
            let target_addr = tc.initial_pc.wrapping_add(tc.offset as u16);
            vm.memory[target_addr as usize] = tc.memory_value;

            // Construct LD instruction
            // Format: 0010 DR PCoffset9
            let instruction =
                (0b0010 << 12) | ((tc.dest_reg as u16 & 0x7) << 9) | (tc.offset as u16 & 0x1FF);

            // Execute the load
            vm.execute_load(instruction);

            // Verify loaded value
            assert_eq!(
                vm.registers[tc.dest_reg as usize], tc.expected_value,
                "Failed test case '{}': Register value mismatch",
                tc.name
            );

            // Verify condition flag
            assert_eq!(
                vm.registers[Register::Cond],
                tc.expected_flag as u16,
                "Failed test case '{}': Condition flag mismatch",
                tc.name
            );
        }
    }

    #[test]
    fn test_execute_load_reg() {
        struct TestCase {
            name: &'static str,
            dest_reg: Register,
            base_reg: Register,
            base_value: u16,
            offset: i8, // 6-bit signed offset
            memory_value: u16,
            expected_value: u16,
            expected_flag: ConditionFlag,
        }

        let test_cases = vec![
            // Basic positive offset load
            TestCase {
                name: "Load with positive offset",
                dest_reg: Register::R1,
                base_reg: Register::R2,
                base_value: 0x3000,
                offset: 5,
                memory_value: 42,
                expected_value: 42,
                expected_flag: ConditionFlag::Pos,
            },
            // Negative offset load
            TestCase {
                name: "Load with negative offset",
                dest_reg: Register::R3,
                base_reg: Register::R4,
                base_value: 0x3100,
                offset: -5,
                memory_value: 0x8000,
                expected_value: 0x8000,
                expected_flag: ConditionFlag::Neg,
            },
            // Zero offset load
            TestCase {
                name: "Load with zero offset",
                dest_reg: Register::R5,
                base_reg: Register::R6,
                base_value: 0x3200,
                offset: 0,
                memory_value: 0,
                expected_value: 0,
                expected_flag: ConditionFlag::Zro,
            },
            // Maximum positive offset (31)
            TestCase {
                name: "Load with maximum positive offset",
                dest_reg: Register::R0,
                base_reg: Register::R1,
                base_value: 0x3000,
                offset: 31,
                memory_value: 100,
                expected_value: 100,
                expected_flag: ConditionFlag::Pos,
            },
            // Maximum negative offset (-32)
            TestCase {
                name: "Load with maximum negative offset",
                dest_reg: Register::R2,
                base_reg: Register::R3,
                base_value: 0x3300,
                offset: -32,
                memory_value: 50,
                expected_value: 50,
                expected_flag: ConditionFlag::Pos,
            },
            // Memory address wrap-around
            TestCase {
                name: "Load with address wrap-around",
                dest_reg: Register::R4,
                base_reg: Register::R5,
                base_value: 0xFFFF,
                offset: 5,
                memory_value: 0x4444,
                expected_value: 0x4444,
                expected_flag: ConditionFlag::Pos,
            },
            // Same register for base and destination
            TestCase {
                name: "Load using same register for base and destination",
                dest_reg: Register::R6,
                base_reg: Register::R6,
                base_value: 0x3400,
                offset: 10,
                memory_value: 0x2000,
                expected_value: 0x2000,
                expected_flag: ConditionFlag::Pos,
            },
            // Edge case with maximum unsigned value
            TestCase {
                name: "Load maximum unsigned value",
                dest_reg: Register::R7,
                base_reg: Register::R0,
                base_value: 0x3500,
                offset: 15,
                memory_value: 0xFFFF,
                expected_value: 0xFFFF,
                expected_flag: ConditionFlag::Neg,
            },
        ];

        for tc in test_cases {
            let mut vm = Vm::new();

            // Setup base register value
            vm.registers[tc.base_reg as usize] = tc.base_value;

            // Setup memory value at target address
            let target_addr = tc.base_value.wrapping_add(tc.offset as u16);
            vm.memory[target_addr as usize] = tc.memory_value;

            // Construct LDR instruction
            // Format: 0110 DR BaseR offset6
            let instruction = (0b0110 << 12)
                | ((tc.dest_reg as u16 & 0x7) << 9)
                | ((tc.base_reg as u16 & 0x7) << 6)
                | (tc.offset as u16 & 0x3F);

            // Execute the load register instruction
            vm.execute_load_reg(instruction);

            // Verify loaded value
            assert_eq!(
                vm.registers[tc.dest_reg as usize], tc.expected_value,
                "Failed test case '{}': Register value mismatch",
                tc.name
            );

            // Verify condition flag
            assert_eq!(
                vm.registers[Register::Cond],
                tc.expected_flag as u16,
                "Failed test case '{}': Condition flag mismatch",
                tc.name
            );
        }
    }

    #[test]
    fn test_execute_load_eff_addr() {
        struct TestCase {
            name: &'static str,
            initial_pc: u16,
            dest_reg: Register,
            offset: i16,
            expected_addr: u16,
            expected_flag: ConditionFlag,
        }

        let test_cases = vec![
            // Basic positive offset
            TestCase {
                name: "Positive offset calculation",
                initial_pc: 0x3000,
                dest_reg: Register::R1,
                offset: 0x80,
                expected_addr: 0x3080,
                expected_flag: ConditionFlag::Pos,
            },
            // Zero offset
            TestCase {
                name: "Zero offset calculation",
                initial_pc: 0x3000,
                dest_reg: Register::R2,
                offset: 0,
                expected_addr: 0x3000,
                expected_flag: ConditionFlag::Pos,
            },
            // Negative offset
            TestCase {
                name: "Negative offset calculation",
                initial_pc: 0x3000,
                dest_reg: Register::R3,
                offset: -256,
                expected_addr: 0x2F00,
                expected_flag: ConditionFlag::Pos,
            },
            // Wrap around to zero
            TestCase {
                name: "Address wrap to zero",
                initial_pc: 0xFFFF,
                dest_reg: Register::R6,
                offset: 1,
                expected_addr: 0x0000,
                expected_flag: ConditionFlag::Zro,
            },
            // Wrap around to negative value
            TestCase {
                name: "Address wrap to negative value",
                initial_pc: 0x7FFF,
                dest_reg: Register::R7,
                offset: 1,
                expected_addr: 0x8000,
                expected_flag: ConditionFlag::Neg,
            },
        ];

        for tc in test_cases {
            let mut vm = Vm::new();

            // Setup initial state
            vm.registers[Register::PC] = tc.initial_pc;

            // Construct LEA instruction
            // Format: 1110 DR PCoffset9
            let instruction =
                (0b1110 << 12) | ((tc.dest_reg as u16 & 0x7) << 9) | (tc.offset as u16 & 0x1FF);

            // Execute the LEA instruction
            vm.execute_load_eff_addr(instruction);

            // Verify calculated address
            assert_eq!(
                vm.registers[tc.dest_reg as usize],
                tc.expected_addr,
                "Failed test case '{}': Address calculation mismatch. Expected 0x{:04X}, got 0x{:04X}",
                tc.name,
                tc.expected_addr,
                vm.registers[tc.dest_reg as usize]
            );

            // Verify condition flag
            assert_eq!(
                vm.registers[Register::Cond],
                tc.expected_flag as u16,
                "Failed test case '{}': Condition flag mismatch. Expected {:?}, got flag 0x{:04X}",
                tc.name,
                tc.expected_flag,
                vm.registers[Register::Cond]
            );
        }
    }

    #[test]
    fn test_execute_store() {
        // Define a struct to hold various test parameters.
        struct TestCase {
            name: &'static str,
            initial_pc: u16,
            src_reg: Register,
            offset: i16,
            register_value: u16, // value that will be stored
            expected_memory_value: u16,
        }

        let test_cases = vec![
            // Basic test: store a positive value.
            TestCase {
                name: "Store positive value",
                initial_pc: 0x3000,
                src_reg: Register::R1,
                offset: 5,
                register_value: 42,
                expected_memory_value: 42,
            },
            // Test storing a zero value.
            TestCase {
                name: "Store zero value",
                initial_pc: 0x3000,
                src_reg: Register::R2,
                offset: 0,
                register_value: 0,
                expected_memory_value: 0,
            },
            // Test storing a negative value (using two's complement).
            TestCase {
                name: "Store negative value",
                initial_pc: 0x3000,
                src_reg: Register::R3,
                offset: 1,
                register_value: 0x8000, // negative as seen in LC-3
                expected_memory_value: 0x8000,
            },
            // Test with maximum positive offset.
            TestCase {
                name: "Store with maximum positive offset",
                initial_pc: 0x3000,
                src_reg: Register::R4,
                offset: 0xFF, // maximum positive 9-bit offset
                register_value: 100,
                expected_memory_value: 100,
            },
            // Test with maximum negative offset.
            TestCase {
                name: "Store with maximum negative offset",
                initial_pc: 0x3000,
                src_reg: Register::R5,
                offset: -256, // maximum negative 9-bit offset when sign-extended
                register_value: 55,
                expected_memory_value: 55,
            },
            // Test wrap-around of memory addresses.
            TestCase {
                name: "Store with wrap-around memory address",
                initial_pc: 0xFFFF,
                src_reg: Register::R6,
                offset: 5,
                register_value: 0x4444,
                expected_memory_value: 0x4444,
            },
            // Edge case: Store maximum unsigned 16-bit value.
            TestCase {
                name: "Store maximum unsigned value",
                initial_pc: 0x3000,
                src_reg: Register::R7,
                offset: 10,
                register_value: 0xFFFF,
                expected_memory_value: 0xFFFF,
            },
        ];

        for tc in test_cases {
            let mut vm = Vm::new();
            // Set the initial PC and configure the register that will supply the stored value.
            vm.registers[Register::PC] = tc.initial_pc;
            vm.registers[tc.src_reg as usize] = tc.register_value;

            // Build the instruction in the format:
            // Bits [15:12]: opcode (ST = 0011)
            // Bits [11:9]: source register (SR)
            // Bits [8:0]: PCoffset9
            let instruction: u16 =
                (0b0011 << 12) | ((tc.src_reg as u16 & 0x7) << 9) | ((tc.offset as u16) & 0x1FF);

            // Execute the store instruction.
            vm.execute_store(instruction);

            // Compute where the store should occur.
            let expected_addr = tc.initial_pc.wrapping_add(sign_extend(tc.offset as u16, 9));
            // Verify that the correct memory location now holds the expected value.
            assert_eq!(
                vm.memory[expected_addr as usize], tc.expected_memory_value,
                "Failed test case '{}': memory[0x{:04X}] expected 0x{:04X} but found 0x{:04X}",
                tc.name, expected_addr, tc.expected_memory_value, vm.memory[expected_addr as usize]
            );
        }
    }

    #[test]
    fn test_execute_sti() {
        struct TestCase {
            name: &'static str,
            initial_pc: u16,
            src_reg: Register,
            offset: i16,
            src_value: u16,
            intermediate_memory_value: u16,
            // The final memory location, which gets set to src_value.
            expected_final_memory_value: u16,
        }

        let test_cases = vec![
            // Basic test: Positive offset.
            TestCase {
                name: "STI basic positive offset",
                initial_pc: 0x3000,
                src_reg: Register::R0,
                offset: 5,
                src_value: 123,
                intermediate_memory_value: 0x4000,
                expected_final_memory_value: 123,
            },
            // Test with zero offset.
            TestCase {
                name: "STI zero offset",
                initial_pc: 0x3000,
                src_reg: Register::R1,
                offset: 0,
                src_value: 0xABCD,
                intermediate_memory_value: 0x5000,
                expected_final_memory_value: 0xABCD,
            },
            // Test with negative offset (e.g., offset = -3)
            TestCase {
                name: "STI negative offset",
                initial_pc: 0x3005,
                src_reg: Register::R2,
                offset: -3,
                src_value: 0xFFFF,
                intermediate_memory_value: 0x6000,
                expected_final_memory_value: 0xFFFF,
            },
            // Edge case: wrap-around with PC high address.
            TestCase {
                name: "STI wrap-around PC",
                initial_pc: 0xFFFF,
                src_reg: Register::R3,
                offset: 5, // Will wrap via wrapping_add
                src_value: 0x3333,
                intermediate_memory_value: 0x0002,
                expected_final_memory_value: 0x3333,
            },
            // Test storing zero value.
            TestCase {
                name: "STI store zero",
                initial_pc: 0x3000,
                src_reg: Register::R4,
                offset: 10,
                src_value: 0,
                intermediate_memory_value: 0x7000,
                expected_final_memory_value: 0,
            },
        ];

        for tc in test_cases {
            let mut vm = Vm::new();
            // Set the VM's PC according to the test case.
            vm.registers[Register::PC] = tc.initial_pc;
            // Place the value in the source register.
            vm.registers[tc.src_reg as usize] = tc.src_value;
            // Compute the intermediate address: (PC + sign-extended offset)
            let intermediate_addr = tc.initial_pc.wrapping_add(tc.offset as u16);
            // Write the intermediate memory value that holds the final target address.
            vm.memory[intermediate_addr as usize] = tc.intermediate_memory_value;
            // Make sure the final memory location is cleared (for clarity)
            vm.memory[tc.intermediate_memory_value as usize] = 0;

            // Construct the STI instruction:
            // Format: 1011 SR PCoffset9
            // Bits 15-12: 1011  (STI opcode)
            // Bits 11-9: source register.
            // Bits 8-0:   PCoffset9 (lower 9 bits of the offset, after sign extension on decoding)
            let instruction =
                (0b1011 << 12) | (((tc.src_reg as u16) & 0x7) << 9) | ((tc.offset as u16) & 0x1FF);

            // Execute the STI instruction.
            vm.execute_sti(instruction);

            // Check that memory at the computed final address has the source value.
            assert_eq!(
                vm.memory[tc.intermediate_memory_value as usize], tc.expected_final_memory_value,
                "Test case '{}' failed: memory[final_addr] mismatch",
                tc.name,
            );
        }
    }

    #[test]
    fn test_execute_str_reg() {
        struct TestCase {
            name: &'static str,
            base_value: u16,    // Value in BaseR register.
            sr_value: u16,      // Value in SR register.
            offset: i16,        // Offset (6-bit signed value).
            base_reg: Register, // Base register (the register whose content is used as base).
            sr_reg: Register,   // SR register (the register whose content is stored).
            expected_addr: u16, // Expected memory address (base_value + offset).
        }

        let test_cases = vec![
            TestCase {
                name: "Store with positive offset",
                base_value: 0x3000,
                sr_value: 1234,
                offset: 5,
                base_reg: Register::R2,
                sr_reg: Register::R4,
                expected_addr: 0x3000 + 5,
            },
            TestCase {
                name: "Store with zero offset",
                base_value: 0x4000,
                sr_value: 0xABCD,
                offset: 0,
                base_reg: Register::R3,
                sr_reg: Register::R5,
                expected_addr: 0x4000,
            },
            TestCase {
                name: "Store with negative offset",
                base_value: 0x5000,
                sr_value: 0x1234,
                offset: -3,
                base_reg: Register::R6,
                sr_reg: Register::R7,
                expected_addr: 0x5000u16.wrapping_add((-3i16) as u16),
            },
            TestCase {
                name: "Store with wrap-around address",
                base_value: 0xFFFE,
                sr_value: 0x0F0F,
                offset: 5, // This addition wraps around: 0xFFFE + 5 = 0x0003 (mod 2^16)
                base_reg: Register::R0,
                sr_reg: Register::R1,
                expected_addr: 0xFFFEu16.wrapping_add(5),
            },
        ];

        for tc in test_cases {
            let mut vm = Vm::new();
            // Setup the base register with the base value.
            vm.registers[tc.base_reg as usize] = tc.base_value;
            // Setup the source register with the value to be stored.
            vm.registers[tc.sr_reg as usize] = tc.sr_value;

            // Build the STR instruction.
            // Encoding: 0111 (opcode) then bits[11:9] = SR, bits[8:6] = BaseR, and bits[5:0] = offset6.
            let instr: u16 = (0b0111 << 12)
                | ((tc.sr_reg as u16 & 0x7) << 9)
                | ((tc.base_reg as u16 & 0x7) << 6)
                | ((tc.offset as u16) & 0x3F);

            // Execute the STORE register instruction.
            vm.execute_str_reg(instr);

            // Check that the memory at expected address is set to the SR value.
            assert_eq!(
                vm.memory[tc.expected_addr as usize], tc.sr_value,
                "Failed test case '{}': Expected memory[0x{:04X}] to be 0x{:04X}",
                tc.name, tc.expected_addr, tc.sr_value
            );
        }
    }
}
