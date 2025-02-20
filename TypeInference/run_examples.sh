#!/bin/bash 

# Build the MiniML project
cabal build exe:miniML
cabal build lib:miniML

dir_path="examples/pass/"
res_file="examples/results.out"

rm -f $res_file && touch $res_file

for name in bool fact fib fold fst_poly fst fun head hof ite map map1 mapTuple mapTuple1 mapTuple2 poly sum; do 
    	echo -ne "\nRunning "${name}".ml\n" >> $res_file
	cabal run miniML -- --type-inf "${dir_path}${name}.ml" >> $res_file
done

