use crate::cpu::Cpu;
use crate::memory::{Lc3Memory, Memory};
use crate::rom::Rom;
use std::cell::RefCell;
use std::rc::Rc;

/// Represents the virtual machine (VM) responsible for executing LC-3 programs.
///
/// The `Vm` struct contains the memory and registers required for program execution.
/// - `memory`: A fixed-size array representing the VM's memory space, capable of holding up to 64K words.
/// - `registers`: A fixed-size array representing the VM's registers, including general-purpose registers and special-purpose ones like the program counter (PC) and condition flags.
/// - `debug`: A boolean flag indicating whether to enable debug mode, which provides detailed execution information.
pub struct Vm {
    pub memory: Rc<RefCell<Memory>>,
    cpu: Cpu,
}

impl Vm {
    pub fn new() -> Self {
        let memory = Rc::new(RefCell::new(Memory::new()));
        let cpu = Cpu::new(Rc::clone(&memory));
        Vm { memory, cpu }
    }

    pub fn start(&mut self, rom: Rom) {
        {
            let mut memory = self.memory.borrow_mut();
            let mut chunks = rom.data.iter();
            let mut addr = *chunks.next().unwrap();
            for chunk in chunks {
                memory.write(addr, *chunk);
                addr += 1;
            }
        }

        while !self.cpu.halted {
            let opcode = self.cpu.fetch();
            let instr = self.cpu.decode(opcode);
            self.cpu.execute(instr);
        }
    }
}
