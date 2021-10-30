#!/bin/sh

current_directory=$(pwd)
count=0
mkdir CWE_BUILD
pushd CWE_BUILD

for entry in "$current_directory"/CWE122*
do
    echo "making $entry.bc"
    wllvm $entry $current_directory/io.c -o $entry.o -DINCLUDEMAIN
done

popd 
