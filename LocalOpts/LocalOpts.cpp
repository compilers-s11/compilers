#include "llvm/Pass.h"
#include "llvm/BasicBlock.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Instruction.h"
#include "llvm/Instructions.h"
#include "llvm/Constants.h"
#include "llvm/ADT/APFloat.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"

#include <ostream>

using namespace llvm;

APFloat::roundingMode rMode = APFloat::rmNearestTiesToEven;
namespace
{
    template<class C, class AP>
    bool valEquals (C *L, AP* R);

    template<>
      bool valEquals (ConstantInt *L, APInt *R) {return L->getValue().eq(*R);}
    template<>
      bool valEquals (ConstantFP *L, APFloat *R) {return L->getValueAPF().compare(*R) == APFloat::cmpEqual;}

  struct LocalOpts : public BasicBlockPass
  {
    static char ID;
    LocalOpts() : BasicBlockPass(ID) {}
   
    void propagateConstant(Instruction *i, Value * val) {
      i->replaceAllUsesWith(val);
    }

    template<class C, class AP>
    Value * constIdentity (Value *L, Value * R, AP *identity, AP *zero) {
      if (C *LC = dyn_cast<C>(L)) {
        if (identity && valEquals<C,AP>(LC,identity)) {
          return R;
        } else if (zero && valEquals<C,AP>(LC,zero)) {
          return C::get(LC->getContext(), *zero);
        }
      } 
      return NULL;
    }
      
    template<class C, class AP>
    Value * commIdentities (Value *L, Value * R, AP *identity, AP *zero) {
      if (Value * changedVal = constIdentity<C,AP>(L,R,identity,zero)) {
        return changedVal;
      } else if (Value * changedVal = constIdentity<C,AP>(R,L,identity,zero)) {
        return changedVal;
      } else {
        return NULL;
      }
    }
   
   template<class C>
   Value * selfInverse (Value *L, Value *R, C * zero) {
      if (cast<Instruction>(L)->isIdenticalTo(cast<Instruction>(R))) {
        return zero;
      } else return NULL;
    }


    ConstantInt* evalBinaryIntOp(unsigned op, ConstantInt * left, ConstantInt * right) {
      switch (op) {
        case Instruction::Add:
          return ConstantInt::get(left->getContext(), 
            left->getValue() + right->getValue());
        case Instruction::Sub:
          return ConstantInt::get(left->getContext(), 
            left->getValue() - right->getValue());
        case Instruction::Mul:
          return ConstantInt::get(left->getContext(), 
            left->getValue() * right->getValue());
        case Instruction::UDiv:
          return ConstantInt::get(left->getContext(), 
            left->getValue().udiv(right->getValue()));
        case Instruction::SDiv:
          return ConstantInt::get(left->getContext(), 
            left->getValue().sdiv(right->getValue()));
        case Instruction::URem:
          return ConstantInt::get(left->getContext(), 
            left->getValue().urem(right->getValue()));
        case Instruction::SRem:
          return ConstantInt::get(left->getContext(), 
            left->getValue().srem(right->getValue()));
        case Instruction::Shl:
          return ConstantInt::get(left->getContext(), 
            left->getValue().shl(right->getValue()));
        case Instruction::LShr:
          return ConstantInt::get(left->getContext(), 
            left->getValue().lshr(right->getValue()));
        case Instruction::AShr:
          return ConstantInt::get(left->getContext(), 
            left->getValue().ashr(right->getValue()));
        case Instruction::And:
          return ConstantInt::get(left->getContext(), 
            left->getValue() & right->getValue());
        case Instruction::Or:
          return ConstantInt::get(left->getContext(), 
            left->getValue() | right->getValue());
        case Instruction::Xor:
          return ConstantInt::get(left->getContext(), 
            left->getValue() ^ right->getValue());
        }
    }

    ConstantFP* evalBinaryFloatOp(unsigned op, ConstantFP* left, ConstantFP* right) {
      APFloat lhs = left->getValueAPF();
      APFloat rhs = right->getValueAPF();
      switch (op) {
        case Instruction::FAdd:
            lhs.add(rhs, rMode);
        case Instruction::FSub:
            lhs.subtract(rhs, rMode);
        case Instruction::FMul:
            lhs.multiply(rhs, rMode);
        case Instruction::FDiv:
            lhs.divide(rhs, rMode);
        case Instruction::FRem:
            lhs.remainder(rhs);
      }
      return ConstantFP::get(left->getContext(), lhs);
    }

    Value* evalBinaryOp(unsigned op, Value* left, Value* right) {
      switch (op) {
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
          return left;
      }
    }

    virtual bool runOnBasicBlock(BasicBlock &bb) {
      bool modified = false;
      bool iModified;
      // Iterate over instructions
      for (BasicBlock::iterator i = bb.begin(), e = bb.end(); i != e; ++i)
      {
        iModified = false;
        Value* L; Value* R;
        if (i->getNumOperands() == 2) {
          L = i->getOperand(0);
          R = i->getOperand(1);
        }

        // These constants are useful for many of the identies that follow
        APInt zeroAPI; APInt oneAPI;
        APFloat zeroAPF = APFloat((float)0);
        APFloat oneAPF = APFloat((float)1);
        if (const IntegerType * ity = dyn_cast<IntegerType>(i->getType())) {
          zeroAPI = APInt(ity->getBitWidth(), 0);
          oneAPI = APInt(ity->getBitWidth(), 1);
        }

        unsigned op = i->getOpcode();
        // Algebraic identities & constant propagation
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
                    modified = iModified = true;
                  }
                }
              }
            }
            break;
          case Instruction::Add:
            // Algebraic identities
            {
              if (Value * changedVal = commIdentities<ConstantInt,APInt>(L, R, &zeroAPI, NULL)) {
                i->replaceAllUsesWith(changedVal);
                modified = iModified = true;
              }
            }
            break;
          case Instruction::FAdd:
            {
              if (Value * changedVal = commIdentities<ConstantFP,APFloat>(L, R, &zeroAPF, NULL)) {
                i->replaceAllUsesWith(changedVal);
                modified = iModified = true;
              }
            }
            break;
          case Instruction::Sub:
            // Algebraic identities
            {
              ConstantInt * zeroCI = ConstantInt::get(L->getContext(), zeroAPI);
              if (Value * changedVal = selfInverse<ConstantInt>(L, R, zeroCI)) {
                i->replaceAllUsesWith(changedVal);
                modified = iModified = true;
              } else if (Value * changedVal = commIdentities<ConstantInt,APInt>(L, R, &zeroAPI, NULL)) {
                i->replaceAllUsesWith(changedVal);
                modified = iModified = true;
              }
            }
            break;
          case Instruction::FSub:
            {
              ConstantFP * zeroCF = ConstantFP::get(L->getContext(), zeroAPF);
              if (Value * changedVal = selfInverse<ConstantFP>(L, R, zeroCF)) {
                i->replaceAllUsesWith(changedVal);
                modified = iModified = true;
              } else if (Value * changedVal = commIdentities<ConstantFP,APFloat>(L, R, &zeroAPF, NULL)) {
                i->replaceAllUsesWith(changedVal);
                modified = iModified = true;
              }
            }
            break;
          case Instruction::Mul:
            {
              if (Value * changedVal = commIdentities<ConstantInt,APInt>(L, R, &oneAPI, &zeroAPI)) {
                i->replaceAllUsesWith(changedVal);
                modified = iModified = true;
              }
            }
            break;
          case Instruction::FMul:
            {
              if (Value * changedVal = commIdentities<ConstantFP,APFloat>(L, R, &oneAPF, &zeroAPF)) {
                i->replaceAllUsesWith(changedVal);
                modified = iModified = true;
              }
            }
            break;
          case Instruction::UDiv:
          case Instruction::SDiv:
            {
              ConstantInt * oneCI = ConstantInt::get(L->getContext(), oneAPI);
              if (Value * changedVal = selfInverse(L, R, oneCI)) {
                i->replaceAllUsesWith(changedVal);
                modified = iModified = true;
              }
              break;
            }
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
        
        // Constant folding
        if (!iModified) {
          if (i->getNumOperands() == 2 && isa<Constant>(L) && isa<Constant>(R)) {
            Value * result = evalBinaryOp(op, L, R);
            i->replaceAllUsesWith(result);
            modified = iModified = true;
          }
        }
        
        // Strength reduction
        if (!iModified) {
          switch (op) {
            case Instruction::Mul:
              // multiplication by power of 2
              if (ConstantInt* LC = dyn_cast<ConstantInt>(L)) {
                const APInt left = LC->getValue();
                if (left.isPowerOf2()) {
                  unsigned lg = left.logBase2();
                  BinaryOperator* newInst = BinaryOperator::Create(
                    Instruction::Shl, 
                    R, ConstantInt::get(LC->getType(), lg, false));
                  ReplaceInstWithInst(i->getParent()->getInstList(), i, newInst);
                  modified = iModified = true;
                  i = newInst;
                }
              } else if (ConstantInt* RC = dyn_cast<ConstantInt>(R)) {
                const APInt right = RC->getValue();
                if (right.isPowerOf2()) {                  
                  unsigned lg = right.logBase2();
                  BinaryOperator* newInst = BinaryOperator::Create(
                    Instruction::Shl,
                    L, ConstantInt::get(RC->getType(), lg, false));
                  i->getParent()->getInstList().insertAfter(i, newInst);
                  i->replaceAllUsesWith(newInst);
                  //i++;
                  //i->getParent()->getInstList().remove(i);
      //            i->replaceAllUsesWith(newInst);
                  //ReplaceInstWithInst(i->getParent()->getInstList(), i, newInst);
                  modified = iModified = true;
                  }
              }
          }
        }
      }
      
      return modified;
    }
  };

  char LocalOpts::ID = 0;
  static RegisterPass<LocalOpts> x("LocalOpts", "LocalOpts", false, false);
}
