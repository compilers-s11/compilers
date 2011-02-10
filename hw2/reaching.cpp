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
          index = new ValueMap<Value*, int>();
          r_index = new std::vector<Value*>();
          instOut = new ValueMap<Instruction*, BitVector*>();
        }

        // map from instructions/argument to their index in the bitvector
        ValueMap<Value*, int> *index;
        
        // map from index in bitvector back to instruction/argument
        std::vector<Value*> *r_index;
        
        // convenience
        int numTotal;
        int numArgs;

		    // map from instructions to bitvector corresponding to program point AFTER that instruction
        ValueMap<Instruction*, BitVector*> *instOut;

        virtual void meet(BitVector *op1, const BitVector *op2) {
        	// union
          *op1 |= *op2;
        }

        virtual void getBoundaryCondition(BitVector *entry) {
        	// in[b] = just the arguments if no predecessors / entry node
          *entry = BitVector(numTotal, false);
         	for (int i=0; i < numArgs; ++i) {
         		(*entry)[i] = true;
         	} 	
        }
        
        bool isDefinition(Instruction *ii) {
          return (!(isa<TerminatorInst>(ii) || isa<StoreInst>(ii) || (isa<CallInst>(ii) && cast<CallInst>(ii)->getCalledFunction()->getReturnType()->isVoidTy())));
        }

        BitVector* initialInteriorPoint(BasicBlock& bb) {
        	// out[b] = empty set initially
          return new BitVector(numTotal, false);
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
         
          // initialize instOut
          for (inst_iterator ii = inst_begin(&F), ie = inst_end(&F); ii != ie; ii++) {
            (*instOut)[&*ii] = new BitVector(numTotal, false);
          }
        	top = new BitVector(numTotal, false);
        	
          // run data flow 
        	Dataflow<true>::runOnFunction(F);
         
          // print out instructions with reaching variables between each instruction 
        	displayResults(F);
        	
          // didn't modify nothing 
        	return false;
        }
        
        virtual BitVector* transfer(BasicBlock& bb) {
          // we iterate over instructions beginning with in[bb]
          BitVector* prev = (*in)[&bb];
          
          // temporary variables for convenience
          BitVector* instVec = prev; // for empty blocks
          Instruction* inst;

          for (BasicBlock::iterator ii = bb.begin(), ie = bb.end(); ii != ie; ii++) {
            // begin with previous reaching definitions
            inst = &*ii;
            instVec = (*instOut)[inst];            
            *instVec = *prev;
            
            // if this instruction is a new definition, add it
            if (isDefinition(inst))
              (*instVec)[(*index)[inst]] = true;
            
            prev = instVec;
          }
          
          // return a copy of the final instruction's post-condition to put in out[bb]
          return new BitVector(*instVec);
        }
        
        virtual void displayResults(Function &F) {
          // iterate over basic blocks
          Function::iterator bi = F.begin(), be = (F.end());
          for (; bi != be; bi++) {
            // display in[bb]
            if (!isa<PHINode>(*(bi->begin())))
              printBV( (*in)[&*bi] );
            
            // iterate over remaining instructions except very last one
            // we don't print out[i] for the last one because we should actually print out the
            // result of the meet operator at those points, i.e. in[next block]...              
            BasicBlock::iterator ii = bi->begin(), ie = --(bi->end());
            for (; ii != ie; ii++) {
              errs() << "\t" << *ii << "\n";
              if (!isa<PHINode>(*(++ii))) {
                --ii;
                printBV( (*instOut)[&*ii] );
              } else --ii;
              
            }
            errs() << "\t" << *(ii) << "\n";
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

    char ReachingDefinitions::ID = 0;
    static RegisterPass<ReachingDefinitions> x("ReachingDefinitions", "ReachingDefinitions", false, false);
}

