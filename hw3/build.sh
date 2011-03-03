#!/bin/bash

llvm-gcc -emit-llvm -Wa,-disable-opt -O0 -c $1.c 
llvm-2.8/Debug/bin/llvm-dis $1.o
llvm-2.8/Debug/bin/opt -adce $1.o -o $1.lldce
llvm-2.8/Debug/bin/opt --load llvm-2.8/Debug/lib/DCE.so -DCE $1.o -o $1.mydce
llvm-2.8/Debug/bin/llvm-dis $1.mydce
llvm-2.8/Debug/bin/llvm-dis $1.lldce
