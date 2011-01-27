#include "llvm/Pass.h"
#include "llvm/BasicBlock.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Instruction.h"
#include "llvm/Instructions.h"
#include "llvm/Constants.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"

#include <ostream>

using namespace llvm;

namespace
{

  struct LocalOpts : public BasicBlockPass
  {
    static char ID;
    LocalOpts() : BasicBlockPass(ID) {}

    void propagateConstant(Instruction *i, Value * val) {
      i->replaceAllUsesWith(val);
    }

    virtual bool runOnBasicBlock(BasicBlock &bb) {
      bool modified = false;
      // Iterate over instructions
      for (BasicBlock::iterator i = bb.begin(), e = bb.end(); i != e; ++i)
      {
        Value* L; Value* R;
        if (i->getNumOperands() == 2) {
          L = i->getOperand(0);
          R = i->getOperand(1);
        }

              errs() << *i << "\n";
        switch (i->getOpcode()) {
          default:
            break;
          case Instruction::Store:
            //Constant Propagation
            //If a constant is being stored into a variable, find the place where it is being loaded into a register, and replace all uses of the register with the constant.
            {
              Value * ptr = cast<StoreInst>(i)->getPointerOperand();
              Value * val = cast<StoreInst>(i)->getValueOperand();
              if (isa<Constant>(*val)) {
                errs() << "Constant\n";
                for (Value::use_iterator u = ptr->use_begin(); u != ptr->use_end(); ++u) {
                  if (LoadInst *l = dyn_cast<LoadInst>(*u)) {
                    propagateConstant(l, val);
                    modified = true;
                  }

                }
              }
            }
            break;
          case Instruction::Add:
            // Algebraic identities
            if (ConstantInt *LC = dyn_cast<ConstantInt>(L)) {
              if (LC->isZero()) {
                ReplaceInstWithValue(i->getParent()->getInstList(), i, R);
                modified = true;
              } else if (ConstantInt *RC = dyn_cast<ConstantInt>(R)) {
                APInt result = LC->getValue() + RC->getValue();
                i->replaceAllUsesWith(Constant::getIntegerValue(LC->getType(), result));
                modified = true;
              }
            } else if (ConstantInt *RC = dyn_cast<ConstantInt>(R)) {
              if (RC->isZero()) {
                ReplaceInstWithValue(i->getParent()->getInstList(), i, L);
                modified = true;
              }
            }
            break;
          case Instruction::FAdd:
          case Instruction::Sub:
          case Instruction::FSub:
          case Instruction::Mul:
          case Instruction::FMul:
          case Instruction::UDiv:
          case Instruction::SDiv:
          case Instruction::FDiv:
          case Instruction::URem:
          case Instruction::SRem:
          case Instruction::FRem:
          case Instruction::Shl:						
          case Instruction::LShr:						
          case Instruction::AShr:					
          case Instruction::And:					
          case Instruction::Or:

            break;

          case Instruction::Xor:

            break;
        }
        //errs() << *i << "\n";
      }
      return modified;
    }
  };

  char LocalOpts::ID = 0;
  static RegisterPass<LocalOpts> x("LocalOpts", "LocalOpts", false, false);
}


Value* evalBinaryOp(unsigned op, Value* left, Value* right) {
  switch op {
    case Instruction::Add:
	  return ConstantInt::get(left->Type, 
							  dyn_cast<ConstantInt*>(left)->getValue() + 
							  dyn_cast<ConstantInt*>(right)->getValue());
    case Instruction::Sub:
  }
}
