#!/bin/bash

cabal build exe:miniML
cabal build lib:miniML
cabal build test

# Run the test suite 100 times
for i in {1..100}; do
  echo "Run #$i:"
  output=$(cabal run test)
  echo "$output"

  if ! echo "$output" | grep -q "All 3 tests passed"; then
    echo "Error: Test run #$i did not pass as expected."
    exit 1
  fi
done

echo "All 100 runs produced the expected output."
