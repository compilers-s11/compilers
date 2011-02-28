/** CMU 15-745: Optimizing Compilers
    Spring 2011
    Salil Joshi and Cyrus Omar
 **/
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
    struct FVA : public Dataflow<false>, public FunctionPass
    {
        static char ID;

        FVA() : Dataflow<false>(), FunctionPass(ID) {
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
          *op1 &= *op2;
        }

        virtual void getBoundaryCondition(BitVector *entry) {
          // out[b] = start with everything faint 
          *entry = BitVector(numTotal, true);
        }
        
        bool isDefinition(Instruction *ii) {
          return (!(isa<TerminatorInst>(ii) || isa<StoreInst>(ii) || (isa<CallInst>(ii) && cast<CallInst>(ii)->getCalledFunction()->getReturnType()->isVoidTy())));
        }

        bool isEliminableDef(Instruction *ii) {
          return (!(isa<TerminatorInst>(ii) || isa<StoreInst>(ii) || isa<CallInst>(ii)));
        }

        BitVector* initialInteriorPoint(BasicBlock& bb) {
          // in[b] = everything is faint initially
          return new BitVector(numTotal, true);
        }

        virtual bool runOnFunction(Function &F) {
          numTotal = 0;
          numArgs = 0;
          
          // add function arguments to maps
          for (Function::arg_iterator ai = F.arg_begin(), ae = F.arg_end(); ai != ae; ai++) {
            (*index)[&*ai] = numArgs;
            r_index->push_back(&*ai);
            numArgs++;
          }
          numTotal = numArgs; 
          
          // add definitions to maps
          for (inst_iterator ii = inst_begin(&F), ie = inst_end(&F); ii != ie; ii++) {
            if (isDefinition(&*ii)) {
              (*index)[&*ii] = numTotal;
              r_index->push_back(&*ii);
              numTotal++;
            }
          }
          
          // initialize instIn
          for (inst_iterator ii = inst_begin(&F), ie = inst_end(&F); ii != ie; ii++) {
            (*instIn)[&*ii] = new BitVector(numTotal, true); //TODO true orfalse
          }
          top = new BitVector(numTotal, true);
          
          // run data flow 
          Dataflow<false>::runOnFunction(F);

          DCE(F);
         

          // didn't modify nothing 
          return true;
        }
        
        virtual BitVector* transfer(BasicBlock& bb) {
          // we iterate over instructions in reverse beginning with out[bb]
          BitVector* next = new BitVector(*((*out)[&bb]));
          
          // temporary variables for convenience
          BitVector* instVec = next; // for empty blocks
          Instruction* inst;

          // add local phi-captured nodes to out          
       //   for (BasicBlock::iterator ii = bb.begin(), ib = bb.end(); ii != ib; ++ii) {
       //     if (isa<PHINode>(*ii)) {
       //       PHINode* phiInst = cast<PHINode>(&*ii);
       //       unsigned idx = phiInst->  getBasicBlockIndex (&bb);
       //       if (idx < phiInst->getNumIncomingValues()){
       //         Value* v = phiInst -> getIncomingValue(idx);
       //         if (isa<Instruction>(v) || isa<Argument>(v))
       //         {
       //           (*next)[(*index)[v]] = true;
       //         }
       //       }
       //     }
       //   }

          // go through instructions in reverse
          BasicBlock::iterator ii = --(bb.end()), ib = bb.begin();
          while (true) {
            
            // inherit data from next instruction
            inst = &*ii;
            instVec = (*instIn)[inst];            
            *instVec = *next;
            
            // if this instruction is a new definition, remove it
            //if (isDefinition(inst))
            //  (*instVec)[(*index)[inst]] = true;
            //
                            
            // add the arguments, unless it is a phi node
            //if (!isa<PHINode>(*ii)) {
            User::op_iterator OI, OE;
            for (OI = inst->op_begin(), OE=inst->op_end(); OI != OE; ++OI) {
              if (isa<Instruction>(*OI) || isa<Argument>(*OI)) {
                if (isa<CallInst>(inst)|| isa<TerminatorInst>(inst) 
                    || (!(*instVec)[(*index)[inst]])
                    || isa<StoreInst>(inst)) {
                    (*instVec)[(*index)[*OI]] = false;
                }
              }
            }
                
            if (isa<CallInst>(inst) || isa<InvokeInst>(inst)) {
              (*instVec)[(*index)[inst]] = false;
            }
            //}
            next = instVec;

            if (ii == ib) break;
            --ii;
          }
          
          // remove the phi nodes from in 
          instVec = new BitVector(*instVec);
       //   for (BasicBlock::iterator ii = bb.begin(), ib = bb.end(); ii != ib; ++ii) {
       //     if (isa<PHINode>(*ii)) {
       //       PHINode* phiInst = cast<PHINode>(&*ii);
       //       unsigned idx = phiInst->  getBasicBlockIndex (&bb);
       //       if (idx < phiInst->getNumIncomingValues()){
       //         Value* v = phiInst -> getIncomingValue(idx);
       //         if (isa<Instruction>(v) || isa<Argument>(v))
       //         {
       //           (*next)[(*index)[v]] = false;
       //         }
       //       }
       //     }
       //   }
          return instVec;
        }

        virtual void DCE(Function &F) {
          BitVector *d = (*in)[&(F.getEntryBlock())];
          for (inst_iterator ii = inst_begin(F), ie = inst_end(F); ii != ie; ii++) {
            if (isEliminableDef(&*ii)) {
              if ((*d)[(*index)[&*ii]]) {
                inst_iterator j = ii;
                ++ii;
                j->eraseFromParent();
                --ii;
              }
            }
          }
        }
        
        virtual void displayResults(Function &F) {
          // iterate over basic blocks
          Function::iterator bi = F.begin(), be = (F.end());
          printBV( (*out)[&*bi] ); // entry node
          for (; bi != be; ) {            
            errs() << bi->getName() << ":\n"; //Display labels for basic blocks
          
            // iterate over remaining instructions except very first one
            BasicBlock::iterator ii = bi->begin(), ie = (bi->end());
            errs() << "\t" << *ii << "\n";
            for (ii++; ii != ie; ii++) {
              if (!isa<PHINode>(*(ii))) {
                printBV( (*instIn)[&*ii] );
              }
              errs() << "\t" << *ii << "\n";
            }
            
            // display in[bb]
            ++bi;
            
            if (bi != be && !isa<PHINode>(*((bi)->begin())))
              printBV( (*out)[&*bi] );

            errs() << "\n";
          }
          printBV( (*out)[&*(--bi)] );
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

    char FVA::ID = 0;
    static RegisterPass<FVA> x("FVA", "FVA", false, false);
}

