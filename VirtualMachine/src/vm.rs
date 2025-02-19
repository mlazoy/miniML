use crate::bytecode::{self, Bytecode, Opcode};
use crate::heap::{Heap, Word};
use std::io;
use std::io::Read;
use std::time::Instant;

pub const STACK_SIZE: usize = 1 << 14;
pub const HEAP_SIZE: usize = 1 << 20;

/// The VM struct
pub struct VM {
    pub bytecode: Bytecode,
    stack: [Word; STACK_SIZE], // Fixed-size stack of words
    stack_ptr: usize,          // Stack pointer. Points to the next free slot in the stack.
    ip: usize,                 // Instruction pointer
    heap: Heap,                // The heap
}

impl VM {
    /// Create a new `VM` with the given bytecode
    pub fn new(bytecode: Bytecode) -> Self {
        VM {
            bytecode,
            stack: [Word::from_int(0); STACK_SIZE], // Initialize stack with zeroes
            stack_ptr: 0,
            ip: 0,
            heap: Heap::new(HEAP_SIZE), // The heap
        }
    }

    #[cfg(debug_assertions)]
    fn print_state(&self) {
        print!("Stack: ");
        for i in 0..self.stack_ptr {
            print!("| {:?} ", self.stack[i]);
        }
        println!("|");

        let opcode: Option<Opcode> = Opcode::from_u8(self.bytecode.instructions[self.ip]);

        println!("IP 0x{:X}: {:?}", self.ip, opcode);
    }

    #[cfg(not(debug_assertions))]
    fn print_state(&self) {}

    #[inline(always)]
    fn fetch_byte(&mut self) -> u8 {
        if self.ip >= self.bytecode.instructions.len() {
            panic!("Instruction pointer out of bounds");
        } else {
            let next = self.bytecode.instructions[self.ip];
            self.ip += 1;
            //return next byte
            next
        }
    }

    #[inline(always)]
    fn fetch_half_word(&mut self) -> u16 {
        if self.ip + 2 > self.bytecode.instructions.len() {
            panic!("Instruction pointer out of bounds");
        } else {
            let low = self.bytecode.instructions[self.ip];
            let high = self.bytecode.instructions[self.ip+1];
            let res = (high as u16) << 8 | low as u16;
            self.ip += 2;
            //return next 2 bytes packed
            res
        }
    }

    #[inline(always)]
    fn fetch_word(&mut self) -> u32 {
        if self.ip + 4 > self.bytecode.instructions.len() {
            panic!("Instruction pointer out of bounds");
        } else {
            let low1 = self.bytecode.instructions[self.ip];
            let high1 = self.bytecode.instructions[self.ip+1];
            let low2 = self.bytecode.instructions[self.ip+2];
            let high2 = self.bytecode.instructions[self.ip+3];
            let res = (high2 as u32) << 24 | (low2 as u32) << 16 | 
                            (high1 as u32) << 8 | low1 as u32;
            self.ip += 4;
            //return next 4 bytes packed
            res  
        }
    }

    #[inline(always)]
    fn jump(&mut self, addr:usize) {
        if addr >= self.bytecode.instructions.len() {
            panic!("Instruction pointer out of bounds.\n");
        } else {
            self.ip = addr;
        }
    }

    // pop and pop_2 don't resize stack internally for efficiency
    // e.g  push + pop yield to 1 total update

    #[inline(always)]
    fn pop(&self) -> Word {
        if self.stack_ptr == 0 {
            panic!("Stack Underflow; Empty stack\n");
        } else {
            let top = self.stack[self.stack_ptr-1];
            // return byte
            top
        }
    }

    #[inline(always)]
    fn pop_2(&self) -> (Word, Word) {
        if self.stack_ptr <= 1 {
            panic!("Stack Underflow; stacksize: 1.\n");
        } else {
            let b = self.stack[self.stack_ptr-1];
            let a = self.stack[self.stack_ptr-2];
            // return 2 top bytes
            (a, b) // order here ??
        }
    }

    #[inline(always)]
    fn deep_pop(&self, i:usize) -> Word { 
        if i >= self.stack_ptr {  // cannot access higher addresses of sp
            panic!("Segmentation fault; stacksize:{}, requested depth:{}\n",
                    self.stack_ptr, i);
        } else {
            let item = self.stack[self.stack_ptr - i - 1];
            // return elem
            item
        }
    }

    fn pop_n(&self, n:usize, offs:usize) -> Vec<Word> {
        if self.stack_ptr < (offs + n - 1) {  // 1 global check
            panic!("Segmentation fault; stacksize:{}, attempted to pop {} items with offset {}\n",
                    self.stack_ptr, n, offs);
        } else {
            let mut items:Vec<Word> = Vec::with_capacity(n);
            for i in 0..n {
                items.push(self.stack[self.stack_ptr-offs-i]);
            }
            items.reverse();
            //items.iter().for_each(|item| println!("{:?}", item));
            items
        }
    }

    #[inline(always)]
    fn push(&mut self, val:Word, offset:usize) {
        if offset > self.stack_ptr { // maybe redundant cause resize_st checks this
            panic!("Stack Overflow; stacksize:{}, attempted to push with offset:{}\n",
                    self.stack_ptr, offset);
        } else {
            self.stack[self.stack_ptr - offset] = val;
        }
    }

    #[inline(always)]
    fn resize_st(&mut self, n:usize, inc:bool) {
        if inc {
            if self.stack_ptr + n < STACK_SIZE {
                self.stack_ptr += n;
            } else {
                panic!("Stack Overflow; stacksize:{}, attempted to resize by +{}.\n",
                self.stack_ptr, n);
            }
        } else {
            if self.stack_ptr >= n {
                self.stack_ptr -= n;
            } else {
                panic!("Segmentation fault; stacksize:{}, attempted to resize by -{}.\n",
                self.stack_ptr, n);
            }
        }
    }

    // scans roots & returns the heap address of the newly allocated item if gc run successfully
    fn trigger_gc(&mut self) -> bool { 
        println!("Running garbadge collection...\n");
        let mut roots:Vec<Word> = Vec::new();

        for item in self.stack.iter() {
            if item.is_pointer() {
                roots.push(*item)
            } 
        }
        // for debugging
        //roots.iter().for_each(|item| println!("{:?}", item));
        println!("Roots found: {}\n", roots.len());

        if self.heap.realloc(&mut roots) {
            // update heap pointers in stack
            let mut roots_ptr = 0;
            for item in self.stack.iter_mut() {
                if item.is_pointer() {
                    *item = roots[roots_ptr];
                    roots_ptr += 1;
                } 
            }
        true 
        } else { false }
    }

    pub fn run(&mut self) {
        // start timer 
        let start_time = Instant::now();
        loop {
            self.print_state(); // just for debugging
            //fetch ip
            let opcode: Option<Opcode> = Opcode::from_u8(self.fetch_byte());

            let op = match opcode {
                None => panic!("Illegal insrtuction.\n"),
                Some(isa_op) => { isa_op }
            };
                match op {
                    Opcode::Halt => break,       //end of program

                    Opcode::Jump => {
                        let addr = self.fetch_half_word();
                        self.jump(addr.into());
                    }

                    Opcode::Jnz => {
                        let top = self.pop();
                        self.resize_st(1,false);
                        let addr = self.fetch_half_word(); // need to consume no matter what
                        if top.to_int() != 0 {
                            self.jump(addr.into());
                        } 
                    }

                    Opcode::Jumpi => {
                        let top = self.pop();
                        self.resize_st(1,false);
                        self.jump(top.to_int() as usize);
                    }

                    Opcode::Dup => {
                        let i = self.fetch_byte() as usize;
                        let stack_elem = self.deep_pop(i);
                        self.push(stack_elem, 0);
                        self.resize_st(1,true);
                    }

                    Opcode::Swap => {
                        let i = self.fetch_byte() as usize;
                        let top = self.pop();
                        let stack_elem  = self.deep_pop(i);
                        //println!("swapping: {} with {}", top.to_int(), stack_elem.to_int());
                        // after swap sp is same
                        self.push(stack_elem,1);
                        self.push(top, i+1);
                    }

                    Opcode::Drop => {
                        self.resize_st(1,false);
                    }

                    Opcode::Push1 => {
                        let byte = self.fetch_byte();
                        self.push(Word::from_int(byte.into()), 0);
                        self.resize_st(1,true); 
                    }

                    Opcode::Push2 => {
                        let half_word = self.fetch_half_word();
                        self.push(Word::from_int(half_word.into()), 0);
                        self.resize_st(1, true);
                    }

                    Opcode::Push4 =>  {
                        let word = self.fetch_word();
                        self.push(Word::from_int(word as i32), 0);
                        self.resize_st(1,true);
                    }

                    Opcode::Add => {
                        let (op1, op2) = self.pop_2();
                        let res = op1.to_int() + op2.to_int();
                        // update sp & push with offs 1
                        self.resize_st(1,false);
                        self.push(Word::from_int(res),1); 
                    }

                    Opcode::Sub => {
                        let (op1, op2) = self.pop_2();
                        let res = op1.to_int() - op2.to_int();
                        // update sp & push with offs 1
                        self.resize_st(1,false);
                        self.push(Word::from_int(res),1); 
                    }

                    Opcode::Mul => {
                        let (op1, op2) = self.pop_2();
                        let res = op1.to_int() * op2.to_int();
                        // update sp & push with offs 1
                        self.resize_st(1,false);
                        self.push(Word::from_int(res),1); 
                    }

                    Opcode::Div => {
                        let (op1, op2) = self.pop_2();
                        if op2.to_int() == 0 {
                            panic!("Division by zero.\n");
                        }
                        let res = op1.to_int() / op2.to_int();
                        // update sp & push with offs 1
                        self.resize_st(1,false);
                        self.push(Word::from_int(res),1); 

                    }

                    Opcode::Mod => {
                        let (op1, op2) = self.pop_2();
                        if op2.to_int() == 0 {
                            panic!("Division by zero.\n");
                        }
                        let res = op1.to_int() % op2.to_int();
                        // update sp & push with offs 1
                        self.resize_st(1,false);
                        self.push(Word::from_int(res),1); 
                    }

                    Opcode::Eq => {
                        let (op1, op2) = self.pop_2();
                        let res = op1.to_int() == op2.to_int();
                        // update sp & push with offs 1
                        self.resize_st(1,false);
                        self.push(Word::from_int(res.into()),1); 
                    }

                    Opcode::Ne => {
                        let (op1, op2) = self.pop_2();
                        let res = op1.to_int() != op2.to_int();
                        // update sp & push with offs 1
                        self.resize_st(1,false);
                        self.push(Word::from_int(res.into()),1); 
                    }

                    Opcode::Lt => {
                        let (op1, op2) = self.pop_2();
                        let res = op1.to_int() < op2.to_int();
                        // update sp & push with offs 1
                        self.resize_st(1,false);
                        self.push(Word::from_int(res.into()),1); 
                    }

                    Opcode::Gt => {
                        let (op1, op2) = self.pop_2();
                        let res = op1.to_int() > op2.to_int();
                        // update sp & push with offs 1
                        self.resize_st(1,false);
                        self.push(Word::from_int(res.into()),1); 
                    }

                    Opcode::Le => {
                        let (op1, op2) = self.pop_2();
                        let res = op1.to_int() <= op2.to_int();
                        // update sp & push with offs 1
                        self.resize_st(1,false);
                        self.push(Word::from_int(res.into()),1); 
                    }

                    Opcode::Ge => {
                        let (op1, op2) = self.pop_2();
                        let res = op1.to_int() >= op2.to_int();
                        // update sp & push with offs 1
                        self.resize_st(1,false);
                        self.push(Word::from_int(res.into()),1); 
                    }

                    Opcode::Not => {
                        let uop = self.pop();
                        let res = !uop.to_int();
                        self.push(Word::from_int(res.into()),1);
                        // don't update sp 

                    }

                    Opcode::And => {
                        let (op1, op2) = self.pop_2();
                        let res = op1.to_int() & op2.to_int();
                        // update sp & push with offs 1
                        self.resize_st(1,false);
                        self.push(Word::from_int(res.into()),1); 
                    }

                    Opcode::Or => {
                        let (op1, op2) = self.pop_2();
                        let res = op1.to_int() | op2.to_int();
                        // update sp & push with offs 1
                        self.resize_st(1,false);
                        self.push(Word::from_int(res.into()),1); 
                    }

                    Opcode::Input => {
                        let mut buffer: [u8; 1] = [0; 1]; // A buffer to store one byte
                        io::stdin()
                            .read_exact(&mut buffer)
                            .expect("Failed to read input\n");
                        let ascii_val = buffer[0] as i32;
                        self.push(Word::from_int(ascii_val),0);
                        self.resize_st(1,true); 
                    }

                    Opcode::Output => {
                        let top = self.pop();
                        self.resize_st(1,false);
                        print!("{}", top.to_int() as u8 as char);
                    }

                    Opcode::Alloc => {
                        let (n_word, tag_word) = self.pop_2(); //returns top second
                        let n = n_word.to_int() as usize; 
                        let tag = tag_word.to_int() as u8; 
                        //println!("popping {} items\n", n);
                        let fields:Vec<Word> = self.pop_n(n,3);
                        let alloca = self.heap.alloc(n,tag,&fields);
                        let heap_addr = match alloca {
                            None => {
                                if self.trigger_gc() {   // run gc and try again
                                    let new_alloca = self.heap.alloc(n,tag,&fields);
                                    match new_alloca {
                                        None => panic!("Failed to allocate heap memory.\n"),
                                        Some(addr) => addr
                                    }
                                } else {
                                    panic!("Failed to allocate heap memory.\n");
                                }
                            }
                            Some(addr) => addr
                        };
                        self.resize_st(n+1,false); // sp: -= (n+1)
                        // push address of block on top (offset 1)
                        self.push(Word::from_pointer(heap_addr),1);
                        self.heap.print_heap(); // just for debugging
                    }

                    Opcode::Load => {
                        let addr = self.pop();
                        let i = self.fetch_word() as usize;
                        //println!("Loading from block:{}, offset:{}\n", addr.to_int(), i);
                        self.heap.print_heap(); // just for debugging
                        let val = self.heap.get_item(addr,i);
                        self.push(val, 1);
                        // sp stays same but offs -1
                    }

                    Opcode::Clock => {
                        let curr_time = Instant::now();
                        let elapsed = (curr_time - start_time).as_micros() as f64 / 1_000_000.0; // Convert to seconds with microsecond precision
                        println!("{:.4}", elapsed);
                    }
                }
        }
    }
}
