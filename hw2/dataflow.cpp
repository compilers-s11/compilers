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
    template<bool forward=true>
    struct Dataflow : public FunctionPass
    {
        static char ID;
        Dataflow() : FunctionPass(ID), in(DomainMap()), out(DomainMap()) {
		        
        }
     
        // transfer function
        // meet operator
        // initial 
     	typedef ValueMap<BasicBlock*, BitVector*> DomainMap;
     	DomainMap in;
     	DomainMap out;
     	BitVector top;
     	
        virtual bool runOnFunction(Function &f) {
            bool modified = false;
            
            size_t numBlocks = f.size();
            BasicBlock & entry = f.getEntryBlock();
            
            for (Function::iterator bi = f.begin(), be = f.end(); bi != be; bi++) {
            	in[&(*bi)] = new BitVector(top);
            	out[&(*bi)] = new BitVector(top);
            }
            
            getBoundaryCondition(in[&entry]);
    	
    		bool changed = true;
    		ValueMap<BasicBlock*, bool> visited = ValueMap<BasicBlock*, bool>();
    		while (changed) {
    			for (Function::iterator bb = f.begin(), be = f.end(); bb != be; bb++) {
    				visited[&(*bb)] = false;
    			}

		    	if (forward) {
    				changed = reversePostOrder(f.getEntryBlock(), visited);
    			} else {
    				changed = postOrder(f.getEntryBlock(), visited);
    			}
    		}

                // TODO: free memory. Not sure what hasto be freed anymore.
		    
            return modified;
        }
        
        // curNode is a pointer now because otherwise you have to keep &ing it.. but visited is still a refernce... gaaah
        virtual bool reversePostOrder(BasicBlock* curNode, ValueMap<BasicBlock*, bool>& visited) {
        	visited[curNode] = true;
        	bool changed = false;

        	// apply meet operator over predecessors
        	pred_iterator PI = pred_begin(curNode), PE = pred_end(curNode);
        	if (PI != PE) {
        		// fold meet over out[ predecessors	]
    			*in[curNode] = *out[*PI];
        		for (PI++; PI != PE; PI++) {
        			meet(in[curNode], out[*PI]);
        		}
        	} // (otherwise entry)
        	
        	// apply transfer function
        	BitVector* newOut = transfer(*curNode);
        	if (*newOut != *out[curNode]) {
        		changed = true;
        		// copy new value
        		*out[curNode] = *newOut;
        	}
    		delete newOut;
    		
    		// recurse on successors
    		for (succ_iterator SI = succ_begin(curNode), SE = succ_end(curNode); SI != SE; SI++) {
    			if (!visited[*SI])
    				changed |= reversePostOrder(*SI);
    		}
        	
        	return changed;
        }
        
        virtual bool postOrder(BasicBlock* curNode, ValueMap<BasicBlock*, bool>& visited) {
        	visited[curNode] = true;
        	bool changed = false;

    		// recurse on successors
    		for (succ_iterator SI = succ_begin(curNode), SE = succ_end(curNode); SI != SE; SI++) {
    			if (!visited[*SI])
    				changed |= reversePostOrder(*SI);
    		}
        	
        	// apply meet operator over predecessors
        	succ_iterator SI = succ_begin(curNode), SE = succ_end(curNode);
        	if (SI != SE) {
        		// fold meet over in[ successors ]
    			*out[curNode] = *in[*SI];
        		for (SI++; SI != SE; SI++) {
        			meet(out[curNode], in[*SI]);
        		}
        	} else {
        		getBoundaryCondition(out[curNode]);
        	}
        	
        	// apply transfer function
        	BitVector* newIn = transfer(*curNode);
        	if (*newIn != *in[curNode]) {
        		changed = true;
        		// copy new value
        		*in[curNode] = *newIn;
        	}
    		delete newIn;

        	return changed;
        }
        
        virtual void getBoundaryCondition(BitVector*) = 0;
        virtual void meet(BitVector*, BitVector*) = 0;
        virtual BitVector* transfer(const BasicBlock &) = 0;
    };

//    char Dataflow::ID = 0;
//    static RegisterPass<Dataflow> x("Dataflow", "Dataflow", false, false);
}

