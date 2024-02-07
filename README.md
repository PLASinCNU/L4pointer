# L4 Pointer

opt -load=/home/mok/project/L4pointer/build/lib/libEpsilon.so -mpav -enable-new-pm=0 INPUT.bc -o out.bc

./runspec --config=wllvm.cfg --action=build --tune=base mcf

bzip, mcf, sjeong, specrand, ldm


400.perlbench - FRAMER
401.bzip2 O - FRAMER
403.gcc - FRAMER
429.mcf O - FRAMER
433.milc
445.gobmk
456.hmmer - FRAMER
458.sjeng O - FRAMER 
462.libquantum O 
464.h264ref 
470.lbm
482.sphinx3
998.specrand O
999.specrand 

bzip :  ./out ../data/all/input/input.combined 200 > bzip2.ref.combined 2> bzip2.ref.combined.err
mcf  : ./out ../data/train/input/inp.in > mcf.ref.out 2> mcf.ref.er
sjeng: ./sjeng_base.wllvm ../data/ref/input/ref.txt
sendMTFValues

# To do list 
# 