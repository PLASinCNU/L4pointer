#ifndef _ADDRSPACE_
#define _ADDRSPACE_

#include <llvm/Support/CommandLine.h>
#include <llvm/IR/Module.h> // because <llvm/IR/Type.h> fails on LLVM 3.8.0
#include <llvm/Support/raw_ostream.h>

#define TAG_SHIFT       48 //(getAddressSpaceBits()) //48 bit
#define TAG_BITS        16 //(PointerBits - getAddressSpaceBits())  //64 - 48 bit
#define TAG_MASK_LOW    ((1ULL << 7) - 1)
#define TAG_MASK_HIGH   (TAG_MASK_LOW << TAG_SHIFT)

#define BOUND_SHIFT     (TAG_SHIFT)
#define BOUND_BITS      (OverflowBit ? (TAG_BITS - 1) : TAG_BITS)
#define BOUND_MASK_LOW  (~((1ULL << 8) | (1ULL <<15)))
#define BOUND_MASK_HIGH (BOUND_MASK_LOW << BOUND_SHIFT)
#define TAG_CLEAN_BIT 0x8080FFFFFFFFFFFF //Size is 64 bit, 


inline bool isPtrIntTy(llvm::Type *Ty) {
    return Ty->isIntegerTy(64);
}

#endif