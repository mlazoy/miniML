use std::{alloc::realloc, fmt::{self, Debug}, os::unix::net::UnixStream};

#[derive(Clone, Copy)]
pub struct Word {
    w: i32,
}

impl Word {
    pub fn from_pointer(ptr: usize) -> Word {
        Word {
            w: (ptr as i32) << 1 | 0,
        }
    }

    pub fn from_int(int: i32) -> Word {
        Word { w: int << 1 | 1 }
    }

    pub fn to_pointer(self) -> usize {
        (self.w >> 1) as usize
    }

    pub fn to_int(self) -> i32 {
        self.w >> 1
    }

    pub fn is_pointer(self) -> bool {
        (self.w & 1) == 0
    }
}

impl Debug for Word {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.is_pointer() {
            write!(f, "Ptr({})", self.to_pointer())
        } else {
            write!(f, "Int({})", self.to_int())
        }
    }
}

pub struct Heap {
    pub heap: Box<[Word]>,
    // FILL IN HERE
    next_free_slot: usize,
    semi_space_size: usize,
    from_base_ptr: usize,
    to_base_ptr: usize
}

impl Heap {
    pub fn new(total_words: usize) -> Self {
        let vec = vec![Word { w: 0 }; total_words];
        let memory = vec.into_boxed_slice();

        Heap {
            heap: memory,
            // FILL IN HERE
            next_free_slot:0,
            semi_space_size: total_words >> 1,      // half words
            from_base_ptr:0,                        //begin with empty 'from' space
            to_base_ptr: total_words >> 1,          //same as semi_space_size
        }
    }

    // helpers for Cheney's GC
    fn in_from_space_(&self, _addr: usize) -> bool {
        _addr >= self.from_base_ptr && _addr < self.from_base_ptr + self.semi_space_size
    }

    fn in_to_space(&self, _addr: usize) -> bool {
        _addr >= self.to_base_ptr && _addr < self.to_base_ptr + self.semi_space_size
    }

    fn swap_spaces(&mut self) {
        let swap = self.from_base_ptr;
        self.from_base_ptr = self.to_base_ptr;
        self.to_base_ptr = swap;
    }

    fn move_block(&mut self, block:Word) -> Option<Word> { // returns the new location
        let old_addr = block.to_pointer();
        let header = self.heap[old_addr];
        if header.is_pointer() && self.in_to_space(header.to_pointer()) { //is fw ptr
            return Some(header);
        }
        let blocksize = ((header.to_int() >> 9) & 0x7FFFFF) as usize;
        if self.next_free_slot + blocksize >= self.to_base_ptr + self.semi_space_size {
            panic!("Not enough space; 'to' size: {}, requested moving {} objects from 'from'\n", 
            (self.next_free_slot - self.to_base_ptr), blocksize);
        }
        let new_base_addr = self.next_free_slot;
        for i in 0..(blocksize + 1) {
            self.heap[new_base_addr + i] = self.heap[old_addr + i];
        }

        self.next_free_slot += blocksize + 1;

        //create the fw ptr
        self.heap[old_addr] = Word::from_pointer(new_base_addr);

        Some(Word::from_pointer(new_base_addr))
    }

    pub fn realloc(&mut self, roots: &mut [Word]) -> bool { //returns true if successful
        self.print_heap(); // check heap before gc fro debugging only
        self.next_free_slot = self.to_base_ptr; 
        // 1. copy objects from 'from' space to 'to' space
        for root in roots.iter_mut() {
            if self.in_from_space_(root.to_pointer()) {
                match self.move_block(*root){ // copy block if needed and get new location
                    Some(new_root) => *root = new_root,
                    None => () 
                }
            }
        }
        // 2. scan 'to' space for updating fw ptrs
        let mut scan_ptr = self.to_base_ptr;
        while scan_ptr < self.next_free_slot {
            let header = self.heap[scan_ptr];
            let blocksize = ((header.to_int() >> 9) & 0x7FFFFF) as usize;
            for i in 1..blocksize+1 {
                let field = self.heap[scan_ptr + i];
                if field.is_pointer() && self.in_from_space_(field.to_pointer()) { 
                    match self.move_block(field){
                        Some(new_addr) => self.heap[scan_ptr + i] = new_addr,
                        None => () // already copied
                    }
                }
            }
            scan_ptr += blocksize + 1;
        }

        // 3. prepare for next round
        self.swap_spaces();
        println!("Freed {} blocks.\n", self.semi_space_size - (self.next_free_slot - self.from_base_ptr - 1));
        self.print_heap(); // check heap after gc fro debugging only
        if self.next_free_slot < self.from_base_ptr + self.semi_space_size {
            true
        } else {
            println!("'to' is full; size : {}.\n", self.next_free_slot- self.from_base_ptr);
            false
        }

    }


    // allocate a new block
    pub fn alloc(&mut self, _size: usize, _tag: u8, _words: &[Word]) -> Option<usize> {
        if self.next_free_slot + _size >= self.from_base_ptr + self.semi_space_size { 
            return None // call GC from vm.rs when None is returned
        } 
        let header = (_size << 9) & 0x7FFFFF | ((_tag as usize) & 0xFF);
        //println!("Allocating new block with header: {}", header);
        let ret = self.next_free_slot;
        self.heap[ret] = Word::from_int(header as i32);
        for i in 1.._size+1 {
            self.heap[ret+i] = _words[i-1];
        }
        self.next_free_slot += _size+1;
        // return header block
        Some(ret)
    }

    // return a stored value
    pub fn get_item(&self, addr:Word, offset:usize) -> Word {
        if !addr.is_pointer() || addr.to_pointer() >= self.heap.len() {
            panic!("Segmentation fault; address out of bounds.\n");
        } 
        let header = self.heap[addr.to_pointer()];
        //println!("Accessing block with header:{}", header.to_pointer());
        let block_sz = header.to_int() as usize >> 8;
        if offset > block_sz {
            panic!("Segmentation fault; block offset out of bounds; offset:{}, blocksize:{}\n",
                    offset, block_sz);
        } 
        let index = addr.to_pointer() + offset;
        // return value at index
        self.heap[index]
    }

    #[cfg(debug_assertions)]
    pub fn print_heap (&self) {
        print!("Heap: ");
        for i in self.from_base_ptr..self.next_free_slot {
            print!("$ {:?} ", self.heap[i]);
        }
        println!("$");
    }

    #[cfg(not(debug_assertions))]
    pub fn print_heap(&self) {}


    #[cfg(debug_assertions)]
    fn print_debug_msg(msg:&str) {
        println!("[DEBUG]: {}", msg);
    }

    #[cfg(not(debug_assertions))]
    fn print_debug_msg(&self) {}
    
    }


