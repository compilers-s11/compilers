#include "llvm/Pass.h"
#include "llvm/BasicBlock.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Instruction.h"
#include "llvm/Instructions.h"
#include "llvm/Constants.h"
#include "llvm/ADT/APFloat.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/BitVector.h"
#include "llvm/ValueMap.h"
#include "llvm/Support/CFG.h"

#include <ostream>

using namespace llvm;

namespace
{
	template<bool forward=true>
    struct Dataflow : public FunctionPass
    {
        static char ID;
        Dataflow() : FunctionPass(ID) {
	        
		        
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
            const BasicBlock & entry = f.getEntryBlock();
            
            in = new DomainMap();
            out = new DomainMap();
            for (int i=0; i < numBlocks; ++i) {
            	in[i] = new BitVector(top);
            	out[i] = new BitVector(top);
            }
            
            getBoundaryCondition(in[entry]);
    	
    		bool changed = true;
    		ValueMap<BasicBlock*, bool>* visited = new ValueMap<BasicBlock*, bool>();
    		while (changed) {
    			for (iterator bb = f.begin(), be = f.end(); bb != be; bb++) {
    				visited[&*bb] = false;
    			}

		    	if (forward) {
    				changed = reversePostOrder(f.getEntryBlock(), *visited);
    			} else {
    				changed = postOrder(f.getEntryBlock(), *visited);
    			}
    		}
    	    	
	    
		    // TODO: free memory
		    
            return modified;
        }
        
        virtual bool reversePostOrder(const BasicBlock & curNode, ValueMap<BasicBlock*, bool>& visited) {
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
        	BitVector* newOut = transfer(curNode);
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
        
        virtual bool reversePostOrder(const BasicBlock & curNode, ValueMap<BasicBlock*, bool>& visited) {
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
        			meet(out[curNode], in[*PI]);
        		}
        	} else {
        		getBoundaryCondition(out[curNode]);
        	}
        	
        	// apply transfer function
        	BitVector* newIn = transfer(curNode);
        	if (*newIn != *in[curNode]) {
        		changed = true;
        		// copy new value
        		*in[curNode] = *newIn;
        	}
    		delete newIn;

        	return changed;
        }
        
        virtual getBoundaryCondition(BitVector*) = 0;
        virtual void meet(BitVector*, BitVector*) = 0;
        virtual BitVector* transfer(const BasicBlock &) = 0;
    };

    char LocalOpts::ID = 0;
    static RegisterPass<LocalOpts> x("Dataflow", "Dataflow", false, false);
}

