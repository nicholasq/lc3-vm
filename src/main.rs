const MEMORY_MAX: usize = 1 << 16;
const MEMORY: [u16; MEMORY_MAX] = [0; MEMORY_MAX];

enum Register {
    R0 = 0,
    R1,
    R2,
    R3,
    R4,
    R5,
    R6,
    R7,
    PC,
    Cond,
}

const REGISTER_COUNT: usize = 10;
const REGISTERS: [u8; REGISTER_COUNT] = [0; REGISTER_COUNT];

enum Opcode {
    Br = 0, // branch
    Add,    // add
    Ld,     // load
    St,     // store
    Jsr,    // jump register
    And,    // bitwise and
    Ldr,    // load register
    Str,    // store register
    Rti,    // unused
    Not,    // bitwise not
    Ldi,    // load indirect
    Sti,    // store indirect
    Jmp,    // jump
    Res,    // reserved (unused)
    Lea,    // load effective address
    Trap,   // execute trap
}

enum ConditionFlag {
    Pos = 1 << 0, // P
    Zro = 1 << 1, // Z
    Neg = 1 << 2, // N
}

fn main() {
    println!("Hello, world!");
}
