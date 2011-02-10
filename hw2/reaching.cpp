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


        //A bidirectional map from defintions to their index in the BitVectors for in and out
        ValueMap<Instruction*, int> *index;
        std::vector<Instruction*> *r_index;
        int maxIndex;

        /*Stores the reaching definitions at the program point just before an instruction. 
        Used only because we need to print the reaching definitions at every program point, 
        and in[b] and out[b] are not enough to accomplish this*/
        ValueMap<Instruction*, BitVector*> *printMap;


        
        virtual void meet(BitVector *op1, const BitVector *op2) {
          *op1 |= *op2; //Take the union of the two sets
        }

        virtual void getBoundaryCondition(BitVector *entry) {
          entry = new BitVector(maxIndex+1,false); //empty set
        }

        bool isDefinition(Instruction *ii) {
          // All other types of instructions are definitions
          return (!(isa<TerminatorInst>(ii) || isa<StoreInst>(ii) || (isa<CallInst>(ii) && cast<CallInst>(ii)->getCalledFunction()->getReturnType()->isVoidTy())));
        }

        BitVector* initialInteriorPoint(BasicBlock& bb) {
          return new BitVector(maxIndex+1,false); //empty set
        }

        virtual bool runOnFunction(Function &F) {
          maxIndex = 0;

          //TODO Add space for arguments and global variabes
          // Establish a bidirectional map from definitions to an index into BitVectors.
          for (inst_iterator ii = inst_begin(&F), ie = inst_end(&F); ii != ie; ii++) {
            if (isDefinition(&*ii)) {
              (*index)[&*ii] = maxIndex;
              r_index->push_back(&*ii);
              maxIndex++;
            }
            (*printMap)[&*ii] = new BitVector();
          }
          maxIndex--;

          top = new BitVector(maxIndex+1, false); //empty set
          Dataflow<true>::runOnFunction(F); //run the analysis

          displayResults(F);

          return false;
        }

        // Display the bytecode annotated with the reaching definitions at each point
        virtual void displayResults(Function &F) {
          for (Function::iterator bi = F.begin(), be = F.end(); bi != be; bi++) {
            errs() << bi->getName() << "\n"; << "\n"; //Display labels for basic blocks
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

        /* prints out a BitVector by looking up the corresponding definitions in r_index. 
        In SSA, every variable has a unique definition, so this function simply displays 
        the variable name instead of the entire definition*/
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
     
        //The transfer function
        virtual BitVector* transfer(BasicBlock &bb) {
          BitVector * result = new BitVector(*(*in)[&bb]);

          for (BasicBlock::iterator ii = bb.begin(), ie = bb.end(); ii != ie; ii++) {
            //The printMap is updated with the current in set of this instruction
            *((*printMap)[&*ii]) = *result;

            //If this instruction is a definition, set its bit to true
            if (isDefinition(&*ii))
              (*result)[(*index)[&*ii]] = true;
          }

          return result;
        }
    };

    char ReachingDefinitions::ID = 0;
    static RegisterPass<ReachingDefinitions> x("ReachingDefinitions", "ReachingDefinitions", false, false);
}

