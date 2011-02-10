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
    struct Liveness : public Dataflow<false>, public FunctionPass
    {
        static char ID;

        Liveness() : Dataflow<false>(), FunctionPass(ID) {
          index = new ValueMap<Value*, int>();
          r_index = new std::vector<Value*>();
          instIn = new ValueMap<Instruction*, BitVector*>();
        }

        // map from instructions/argument to their index in the bitvector
        ValueMap<Value*, int> *index;
        
        // map from index in bitvector back to instruction/argument
        std::vector<Value*> *r_index;
        
        // convenience
        int numTotal;
        int numArgs;

        // map from instructions to bitvector corresponding to program point BEFORE that instruction
        ValueMap<Instruction*, BitVector*> *instIn;

        virtual void meet(BitVector *op1, const BitVector *op2) {
          // union
          *op1 |= *op2;
        }

        virtual void getBoundaryCondition(BitVector *entry) {
          // out[b] = empty set if no successors
          *entry = BitVector(numTotal, false);
        }
        
        bool isDefinition(Instruction *ii) {
          return (!(isa<TerminatorInst>(ii) || isa<StoreInst>(ii) || (isa<CallInst>(ii) && cast<CallInst>(ii)->getCalledFunction()->getReturnType()->isVoidTy())));
        }

        BitVector* initialInteriorPoint(BasicBlock& bb) {
          // in[b] = empty set initially
          return new BitVector(numTotal, false);
        }

        virtual bool runOnFunction(Function &F) {
          numTotal = 0;
          numArgs = 0;
          
          errs() << "A\n";
          // add function arguments to maps
          for (Function::arg_iterator ai = F.arg_begin(), ae = F.arg_end(); ai != ae; ai++) {
            (*index)[&*ai] = numArgs;
            r_index->push_back(&*ai);
            numArgs++;
          }
          numTotal = numArgs; 
          
          errs() << "B\n";
          // add definitions to maps
          for (inst_iterator ii = inst_begin(&F), ie = inst_end(&F); ii != ie; ii++) {
            if (isDefinition(&*ii)) {
              (*index)[&*ii] = numTotal;
              r_index->push_back(&*ii);
              numTotal++;
            }
          }
          
          errs() << "C\n";
          // initialize instIn
          for (inst_iterator ii = inst_begin(&F), ie = inst_end(&F); ii != ie; ii++) {
            (*instIn)[&*ii] = new BitVector(numTotal, false);
          }
          top = new BitVector(numTotal, false);
          
          errs() << "D\n";
          // run data flow 
          Dataflow<false>::runOnFunction(F);
         
          errs() << "E\n";
          // print out instructions with reaching variables between each instruction 
          displayResults(F);
          
          // didn't modify nothing 
          return false;
        }
        
        virtual BitVector* transfer(BasicBlock& bb) {
          // we iterate over instructions in reverse beginning with out[bb]
          BitVector* next = (*out)[&bb];
          // temporary variables for convenience
          BitVector* instVec = next; // for empty blocks
          Instruction* inst;

          BasicBlock::iterator ii = --(bb.end()), ib = bb.begin();
          while (true) {
            
            // begin with liveness below
            inst = &*ii;
            instVec = (*instIn)[inst];            
            *instVec = *next;
            
            // if this instruction is a new definition, remove it
            if (isDefinition(inst))
              (*instVec)[(*index)[inst]] = false;
                            
            // add the arguments
            User::op_iterator OI, OE;
            for (OI = inst->op_begin(), OE=inst->op_end(); OI != OE; ++OI) {
              if (isa<Instruction>(*OI) || isa<Argument>(*OI)) {
                (*instVec)[(*index)[*OI]] = true;
              }
            }
            
            next = instVec;

            if (ii == ib) break;
            --ii;
          }
          
          instVec = new BitVector(*instVec);
          for (ii = bb.begin(), ib = bb.end(); ii != ib; ++ii) {
            // if it is a phi node remove the incoming value too
            if (isa<PHINode>(inst)) {
              PHINode* phiInst = cast<PHINode>(inst);
              unsigned numIncomingValues = phiInst->getNumIncomingValues();
              errs() << "PHI" << numIncomingValues << "\n";
              for (unsigned i=0; i < numIncomingValues; ++i) {
                Value* v = phiInst->getIncomingValue(i);
                if (isa<Instruction>(v) || isa<Argument>(v))
                {
                  WriteAsOperand(errs(), v, false);
                  errs() << (*instVec)[(*index)[v]];
                  (*instVec)[(*index)[v]] = false;
                }
              }
            }
          }
          return instVec;
          // return a copy of the first instruction's pre-condition to fold into in[bb]
        }
        
        virtual void displayResults(Function &F) {
          // iterate over basic blocks
          Function::iterator bi = F.begin(), be = (F.end());
          for (; bi != be; bi++) {            
          
            // iterate over remaining instructions except very first one
            BasicBlock::iterator ii = bi->begin(), ie = (bi->end());
            errs() << "\t" << *ii << "\n";
            for (ii++; ii != ie; ii++) {
              if (!isa<PHINode>(*(++ii))) {
                --ii;
                printBV( (*instIn)[&*ii] );
              } else --ii;
              errs() << "\t" << *ii << "\n";
            }
            
            // display in[bb]
            //if (!isa<PHINode>(*(bi->begin())))
              printBV( (*out)[&*bi] );

            errs() << "\n\n\n";
          }
          // ...unless there are no more blocks
          printBV( (*out)[&*(--be)] );
        }
        
        virtual void printBV(BitVector *bv) {
          errs() << "{ ";
          for (int i=0; i < numTotal; i++) {
            if ( (*bv)[i] ) {
              WriteAsOperand(errs(), (*r_index)[i], false);
              errs() << " ";
            }
          }
          errs() << "}\n";
        }
    
    };

    char Liveness::ID = 0;
    static RegisterPass<Liveness> x("Liveness", "Liveness", false, false);
}

