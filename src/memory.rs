use crate::cpu::MemMapRegister;
use crate::util::{check_key, get_char};

/// The maximum amount of memory supported by the VM (64K)
pub const MEMORY_MAX: usize = 1 << 16;
/// Starting address in memory where program execution begins (0x3000)
pub const PC_START: u16 = 0x3000;

/// Represents the main memory of the system.
///
/// The `Memory` struct contains a fixed-size array of 16-bit words,
/// which can be used to store program data and instructions.
pub struct Memory {
    pub mem: [u16; MEMORY_MAX],
}

/// Trait representing the memory interface for an LC-3 virtual machine.
///
/// Provides methods to read from and write to memory at a given address.
pub trait Lc3Memory {
    fn read(&mut self, addr: u16) -> u16;
    fn write(&mut self, addr: u16, val: u16);
}

impl Memory {
    pub fn new() -> Self {
        Memory {
            mem: [0; MEMORY_MAX],
        }
    }
}

impl Lc3Memory for Memory {
    fn read(&mut self, addr: u16) -> u16 {
        if MemMapRegister::Kbsr == addr {
            let value = if check_key() { 1 << 15 } else { 0 };
            self.mem[MemMapRegister::Kbsr as usize] = value;
            if value != 0 {
                self.mem[MemMapRegister::Kbdr as usize] = get_char()
            }
            value
        } else if MemMapRegister::Kbdr == addr {
            let char = self.mem[MemMapRegister::Kbdr as usize];
            self.mem[MemMapRegister::Kbsr as usize] = 0;
            char
        } else if MemMapRegister::Dsr == addr {
            unimplemented!("Display status register read not implemented");
        } else if MemMapRegister::Ddr == addr {
            let value = self.mem[MemMapRegister::Ddr as usize];
            print!("{}", (value & 0xFF) as u8 as char);
            value
        } else if MemMapRegister::Mcr == addr {
            unimplemented!("Machine control register read not implemented");
        } else {
            self.mem[addr as usize]
        }
    }

    fn write(&mut self, addr: u16, val: u16) {
        self.mem[addr as usize] = val;
    }
}
