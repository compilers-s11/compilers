#include "llvm/Pass.h"
#include "llvm/BasicBlock.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Instruction.h"
#include "llvm/Instructions.h"
#include "llvm/Constants.h"
#include "llvm/ADT/APFloat.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/ADT/BitVector.h"
#include "llvm/ADT/ValueMap.h"
#include "llvm/Support/CFG.h"
#include "llvm/Support/InstIterator.h"
#include "llvm/Assembly/Writer.h"

#include "dataflow.cpp"

#include <ostream>

using namespace llvm;

namespace
{
    struct ReachingDefinitions : public Dataflow<true>, public FunctionPass
    {
        static char ID;

        ReachingDefinitions() : Dataflow<true>(), FunctionPass(ID) {
          index = new ValueMap<Instruction*, int>();
          r_index = new std::vector<Instruction*>();
          printMap = new ValueMap<Instruction*, BitVector*>();
        }

        ValueMap<Instruction*, int> *index;
        std::vector<Instruction*> *r_index;
        int maxIndex;

        ValueMap<Instruction*, BitVector*> *printMap;


        virtual void meet(BitVector *op1, const BitVector *op2) {
          *op1 |= *op2;
        }

        virtual void getBoundaryCondition(BitVector *entry) {
          entry = new BitVector(maxIndex,0);
        }

        bool isDefinition(Instruction *ii) {
          return (!(isa<TerminatorInst>(ii) || isa<StoreInst>(ii) || (isa<CallInst>(ii) && cast<CallInst>(ii)->getCalledFunction()->getReturnType()->isVoidTy())));
        }

        BitVector* initialInteriorPoint(BasicBlock& bb) {
          return new BitVector(maxIndex+1,false);
        }

        virtual bool runOnFunction(Function &F) {
          maxIndex = 0;

          //TODO Add space for arguments and global variabes
          for (inst_iterator ii = inst_begin(&F), ie = inst_end(&F); ii != ie; ii++) {
            if (isDefinition(&*ii)) {
              (*index)[&*ii] = maxIndex;
              r_index->push_back(&*ii);
              maxIndex++;
            }
            (*printMap)[&*ii] = new BitVector();
          }
          maxIndex--;

          top = new BitVector(maxIndex+1, false);
          Dataflow<true>::runOnFunction(F);

          displayResults(F);

          return false;
        }

        virtual void displayResults(Function &F) {
          for (Function::iterator bi = F.begin(), be = F.end(); bi != be; bi++) {
            for (BasicBlock::iterator ii = bi->begin(), ie = bi->end(); ii != ie; ii++) {
              printBV((*printMap)[&*ii]);
              errs() << "\t"<< *ii << "\n";
            }

            if (succ_begin(&*bi) == succ_end(&*bi)) {
              printBV((*out)[&*bi]);
            }
            errs() << "\n\n";
          }
        }

        virtual void printBV(BitVector * bv) {
          errs() << "{ ";
          for (int i = 0; i <= maxIndex; i++) {
            if ((*bv)[i]) {
              WriteAsOperand(errs(), (*r_index)[i], false);
              errs() << " ";
            }
          }
          errs() <<"}\n";
        }
     
        virtual BitVector* transfer(BasicBlock &bb) {
          BitVector * result = new BitVector(*(*in)[&bb]);

          for (BasicBlock::iterator ii = bb.begin(), ie = bb.end(); ii != ie; ii++) {
            *((*printMap)[&*ii]) = *result;
            if (isDefinition(&*ii))
              (*result)[(*index)[&*ii]] = true;
          }

          return result;
        }
    };

    char ReachingDefinitions::ID = 0;
    static RegisterPass<ReachingDefinitions> x("ReachingDefinitions", "ReachingDefinitions", false, false);
}

