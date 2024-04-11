# L4 Pointer

opt -load=/home/mok/project/L4pointer/build/lib/libEpsilon.so -mpav -enable-new-pm=0 INPUT.bc -o out.bc

./runspec --config=wllvm.cfg --action=build --tune=base mcf

bzip, mcf, sjeong, specrand, ldm


400.perlbench - FRAMER
401.bzip2 O - FRAMER - L4
403.gcc - FRAMER
429.mcf O - FRAMER - L4
433.milc
445.gobmk
456.hmmer - FRAMER
458.sjeng O - FRAMER - L4
462.libquantum O 
464.h264ref --> 에러 고처서 llvm commit 도전해보기 
470.lbm
482.sphinx3
998.specrand O - L4
999.specrand 

bzip :  ./out ../data/all/input/input.combined 200 > bzip2.ref.combined 2> bzip2.ref.combined.err
mcf  : ./out ../data/train/input/inp.in > mcf.ref.out 2> mcf.ref.er
 set args -jit-kind=mcjit out.dbg.ll  ../data/train/input/inp.in
sjeng: ./sjeng_base.wllvm ../data/ref/input/ref.txt
milc : ./out < ../data/test/input/su3imp.in
sendMTFValues


$gdb lli
(gdb) set args -jit-kind=mcjit out.dbg.ll
(gdb) break hello.ll:25 # set breakpoint at line 25 in hello.ll
(gdb) run
# To do list 
# 

BitcodeReader 가 Opaque pointer 를 못읽음