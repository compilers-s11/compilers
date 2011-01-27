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

    bool constIdentities (unsigned opcode, Value *L, Value * R, uint64_t *identity, uint64_t *zero, Value * &retval) {
      if (ConstantInt *LC = dyn_cast<ConstantInt>(L)) {
        if (identity && LC->equalsInt(*identity)) {
          retval = L;
          return true;
        } else if (zero && (LC->equalsInt(*zero))) {
          retval = Constant::getIntegerValue(LC->getType(), APInt(LC->getBitWidth(), *zero));
          return true;
        } else if (ConstantInt *RC = dyn_cast<ConstantInt>(R)) {
          APInt result = LC->getValue() + RC->getValue();
          retval = Constant::getIntegerValue(LC->getType(), result);
          return true;
        }
      } else if (ConstantInt *RC = dyn_cast<ConstantInt>(R)) {
        if (identity && RC->equalsInt(*identity)) {
          retval = L;
          return true;
        } else if (zero && (RC->equalsInt(*zero))) {
          retval = Constant::getIntegerValue(RC->getType(), APInt(RC->getBitWidth(), *zero));
          return true;
        }
      }
      return false;
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
        unsigned op = i->getOpCode();
        switch (op) {
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
            {
              Value * val;
              uint64_t zero = 0;
              if (constIdentities((unsigned)Instruction::Add, L, R, &zero, NULL, val)) {
                i->replaceAllUsesWith(val);
                modified = true;
              } else if (ConstantInt* LC = dyn_cast<ConstantInt>(L)
                         && ConstantInt* RC = dyn_cast<ConstantInt>(R)) {
                ConstantInt* result = evalBinaryIntOp(op, LC, RC);
                i->replaceAllUsesWith(val);
              }
            }
            break;
          case Instruction::FAdd:
          case Instruction::Sub:
            // Algebraic identities
            {
              Value * val;
              uint64_t zero = 0;
              if (constIdentities((unsigned)Instruction::Sub, L, R, &zero, NULL, val)) {
                i->replaceAllUsesWith(val);
                modified = true;
              }
            }
            break;
          case Instruction::FSub:
          case Instruction::Mul:
            // Algebraic identities
            {
              Value * val;
              uint64_t zero = 0;
              uint64_t one = 1;
              if (constIdentities((unsigned)Instruction::Sub, L, R, &one, &zero, val)) {
                i->replaceAllUsesWith(val);
                modified = true;
              }
            }
            break;
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
    case Instruction::Sub:
    case Instruction::Mul:
    case Instruction::UDiv:
    case Instruction::SDiv:
    case Instruction::URem:
    case Instruction::SRem:
    case Instruction::Shl:
    case Instruction::LShr:
    case Instruction::AShr:
    case Instruction::And:
    case Instruction::Or:
    case Instruction::Xor:
      return evalBinaryIntOp(op, 
        dyn_cast<ConstantInt>(left), 
        dyn_cast<ConstantInt>(right));
      
    case Instruction::FAdd:
    case Instruction::FSub:
    case Instruction::FMul:
    case Instruction::FDiv:
    case Instruction::FRem:
      return evalBinaryFloatOp(op, 
        dyn_cast<ConstantFP>(left), 
        dyn_cast<ConstantFP>(right));
  }
}

ConstantInt* evalBinaryIntOp(unsigned op, Value* left_v, Value* right_v) {
  switch op {
    case Instruction::Add:
      return ConstantInt::get(left->getType(), 
        left->getValue() + right->getValue());
    case Instruction::Sub:
      return ConstantInt::get(left->getType(), 
        left->getValue() - right->getValue());
    case Instruction::Mul:
      return ConstantInt::get(left->getType(), 
        left->getValue() * right->getValue());
    case Instruction::UDiv:
      return ConstantInt::get(left->getType(), 
        left->getValue().udiv(right->getValue());
    case Instruction::SDiv:
      return ConstantInt::get(left->getType(), 
        left->getValue().sdiv(right->getValue());
    case Instruction::URem:
      return ConstantInt::get(left->getType(), 
        left->getValue().urem(right->getValue());
    case Instruction::SRem:
      return ConstantInt::get(left->getType(), 
        left->getValue().srem(right->getValue());
    case Instruction::Shl:
      return ConstantInt::get(left->getType(), 
        left->getValue().shl(right->getValue());
    case Instruction::LShr:
      return ConstantInt::get(left->getType(), 
        left->getValue().lshr(right->getValue());
    case Instruction::AShr:
      return ConstantInt::get(left->getType(), 
        left->getValue().ashr(right->getValue());
    case Instruction::And:
      return ConstantInt::get(left->getType(), 
        left->getValue() & right->getValue());
    case Instruction::Or:
      return ConstantInt::get(left->getType(), 
        left->getValue() | right->getValue());
    case Instsruction::Xor:
      return ConstantInt::get(left->getType(), 
        left->getValue() ^ right->getValue());
    }
}

APFloat::roundingMode rMode = APFloat::roundingMode::rmNearestTiesToEven;

ConstantFP* evalBinaryFloatOp(unsigned op, ConstantFP* left, ConstantFP* right) {
  switch (op) {
    case Instruction::FAdd:
      return ConstantFP::get(left->getContext(), 
        left->getValue().add(right->getValue(), rMode));
    case Instruction::FSub:
      return ConstantFP::get(left->getContext(), 
        left->getValue().subtract(right->getValue(), rMode));
    case Instruction::FMul:
      return ConstantFP::get(left->getContext(), 
        left->getValue().multiply(right->getValue(), rMode));
    case Instruction::FDiv:
      return ConstantFP::get(left->getContext(), 
        left->getValue().divide(right->getValue(), rMode));
    case Instruction::FRem:
      return ConstantFP::get(left->getContext(), 
        left->getValue().remainder(right->getValue(), rMode));
  }
}
