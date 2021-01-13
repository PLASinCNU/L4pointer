#ifndef _REMP_
#define _REMP_

#include <llvm/Pass.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/Instruction.h>
#include <llvm/ADT/DenseMap.h>
#include <llvm/ADT/TinyPtrVector.h>
#include "util.h"
#include "AddressSpace.h"

using namespace llvm;

class ReinterpretedPointers : public FunctionPass {

public:
    typedef TinyPtrVector<Instruction*> UserListT;

    static char ID;
    ReinterpretedPointers() : FunctionPass(ID) {};

    bool hasNullTagUsers(Instruction *I) {
        return NullTagUsers.count(I) > 0;
    }

    const UserListT &getNullTagUsers(Instruction *I) {
        return NullTagUsers[I];
    }

private:
    DenseMap<Instruction*, UserListT> NullTagUsers;

    bool runOnFunction(Function &F) override;
    void getAnalysisUsage(AnalysisUsage &AU) const override;
    void addNullTagUser(Instruction *PtrInt, Instruction *User);
};

#endif /* _REINTERPRETED_POINTERS_H */
