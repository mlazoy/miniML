#!/bin/bash 

# Build the MiniML project
cargo build

dir_path="examples/"
res_file="examples/results.out"

rm -f $res_file && touch $res_file

for name in app calls fact fib fold foo list_gc list_gc2 list_sum; do 
    	echo -ne "\nExecuting "${name}".ml\n" >> $res_file
	cargo run --release "${dir_path}${name}.ml.bin" >> $res_file
done

name=read_list
inp_file="examples/read_list_input.txt"
echo -ne "\nExecuting "${name}".ml\n" >> $res_file
cargo run --release "${dir_path}${name}.ml.bin" < $inp_file >> $res_file