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

#include <ostream>

using namespace llvm;

namespace
{
    template<bool forward>
    struct Dataflow 
    {
        Dataflow() {
          in = new DomainMap();
          out = new DomainMap();
        }
     
        // transfer function
        // meet operator
        // initial 
     	typedef ValueMap<BasicBlock*, BitVector*> DomainMap;
     	DomainMap *in;
     	DomainMap *out;
     	BitVector *top;
     	
        virtual bool runOnFunction(Function &f) {
            bool modified = false;
            
            BasicBlock & entry = f.getEntryBlock();
            
            for (Function::iterator bi = f.begin(), be = f.end(); bi != be; bi++) {
                if (forward) {
                  (*out)[&(*bi)] = initialInteriorPoint(*bi);
                  (*in)[&(*bi)] = new BitVector(*top);
                } else {
                  (*in)[&(*bi)] = initialInteriorPoint(*bi);
                  (*out)[&(*bi)] = new BitVector(*top);
                }
            }
            
            getBoundaryCondition((*in)[&entry]);
    	
    		bool changed = true;
    		ValueMap<BasicBlock*, bool> *visited = new ValueMap<BasicBlock*, bool>();
    		while (changed) {
    			for (Function::iterator bb = f.begin(), be = f.end(); bb != be; bb++) {
    				(*visited)[&(*bb)] = false;
    			}

		    	if (forward) {
    				changed = reversePostOrder(&f.getEntryBlock(), *visited);
    			} else {
    				changed = postOrder(&f.getEntryBlock(), *visited);
    			}
    		}

            return modified;
        }

        virtual void getAnalysisUsage(AnalysisUsage &AU) const
        {
          AU.setPreservesAll();
        }
              

        ~Dataflow() {
          for (DomainMap::iterator i = in->begin(), ie = in->end(); i != ie; i++) {
            delete i->second;
          }
          for (DomainMap::iterator i = out->begin(), ie = out->end(); i != ie; i++) {
            delete i->second;
          }
          delete top;
        }
        
        // curNode is a pointer now because otherwise you have to keep &ing it.. but visited is still a refernce... gaaah
        virtual bool reversePostOrder(BasicBlock* curNode, ValueMap<BasicBlock*, bool>& visited) {
        	visited[curNode] = true;
        	bool changed = false;

        	// apply meet operator over predecessors
        	pred_iterator PI = pred_begin(curNode), PE = pred_end(curNode);
        	if (PI != PE) {
        		// fold meet over out[ predecessors	]
    			*(*in)[curNode] = *(*out)[*PI];
        		for (PI++; PI != PE; PI++) {
        			meet((*in)[curNode], (*out)[*PI]);
        		}
        	} // (otherwise entry)
        	
        	// apply transfer function
        	BitVector* newOut = transfer(*curNode);
        	if (*newOut != *(*out)[curNode]) {
        		changed = true;
        		// copy new value
        		*(*out)[curNode] = *newOut;
        	}
    		delete newOut;
    		
    		// recurse on successors
    		for (succ_iterator SI = succ_begin(curNode), SE = succ_end(curNode); SI != SE; SI++) {
    			if (!visited[*SI])
    				changed |= reversePostOrder(*SI, visited);
    		}
        	
        	return changed;
        }
        
        virtual bool postOrder(BasicBlock* curNode, ValueMap<BasicBlock*, bool>& visited) {
        	visited[curNode] = true;
        	bool changed = false;

    		// recurse on successors
    		for (succ_iterator SI = succ_begin(curNode), SE = succ_end(curNode); SI != SE; SI++) {
    			if (!visited[*SI])
    				changed |= postOrder(*SI, visited);
    		}
        	
        	// apply meet operator over predecessors
        	succ_iterator SI = succ_begin(curNode), SE = succ_end(curNode);
        	if (SI != SE) {
        		// fold meet over in[ successors ]
    			*(*out)[curNode] = *(*in)[*SI];
        		for (SI++; SI != SE; SI++) {
        			meet((*out)[curNode], (*in)[*SI]);
        		}
        	} else {
        		getBoundaryCondition((*out)[curNode]);
        	}
        	
        	// apply transfer function
        	BitVector* newIn = transfer(*curNode);
        	if (*newIn != *(*in)[curNode]) {
        		changed = true;
        		// copy new value
        		*(*in)[curNode] = *newIn;
        	}
    		delete newIn;

        	return changed;
        }
        
        virtual void getBoundaryCondition(BitVector*) = 0;
        virtual void meet(BitVector*, const BitVector*) = 0;
        virtual BitVector * initialInteriorPoint(BasicBlock&) = 0;
        virtual BitVector* transfer(BasicBlock &) = 0;
    };

//    char Dataflow::ID = 0;
//    static RegisterPass<Dataflow> x("Dataflow", "Dataflow", false, false);
}

