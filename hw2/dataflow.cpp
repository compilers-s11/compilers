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
     
     	typedef ValueMap<BasicBlock*, BitVector*> DomainMap;
     	
     	// in[b] where b is a basic block
     	DomainMap *in;
     	
     	// out[b] where out is a basic block
     	DomainMap *out;
     	
		// bitvector such that meet(x, top) = x
		// must be specified by subclass
     	BitVector *top;
     	
        ~Dataflow() {
        	for (DomainMap::iterator i = in->begin(), ie = in->end(); i != ie; i++) {
            	delete i->second;
        	}
        	for (DomainMap::iterator i = out->begin(), ie = out->end(); i != ie; i++) {
            	delete i->second;
          	}
          	delete top;
        }
     	
        virtual bool runOnFunction(Function &f) {
            BasicBlock& entry = f.getEntryBlock();
            
            // initialize in and out
            for (Function::iterator bi = f.begin(), be = f.end(); bi != be; bi++) {
                if (forward) {
                	/* Forward flow means we need to first apply meet with out[b]
                	   for all incoming blocks, b.
                	   
                	   With loops, out[b] may not always have been generated already,
                	   so we need initial interior points. */
                	(*out)[&(*bi)] = initialInteriorPoint(*bi);
                	
                	/* just a dummy bitvector of the same length as top,
                	   it will never be read before being written to */
                	(*in)[&(*bi)] = new BitVector(*top);
                } else {
                	// opposite logic for reverse flow
                	(*in)[&(*bi)] = initialInteriorPoint(*bi);
                	(*out)[&(*bi)] = new BitVector(*top);
                	
                	// there isn't a unique exit node so we apply the boundary condition
                	// when we reach a node with no successors in the loop below...
                }
            }

            if (forward)            
              // boundary conditions for entry node
              getBoundaryCondition((*in)[&entry]);         

            
            // iteration-level change detection
        		bool changed = true;
        		
        		// need a map to track whether a block has already been visited in an iteration
        		ValueMap<BasicBlock*, bool> *visited = new ValueMap<BasicBlock*, bool>();
        		
        		while (changed) {
        			// initialize visited to false
        			for (Function::iterator bb = f.begin(), be = f.end(); bb != be; bb++) {
        				(*visited)[&(*bb)] = false;
        			}
    			
    		    	if (forward) {
        				changed = reversePostOrder(&entry, *visited);
        			} else {
        				changed = postOrder(&entry, *visited);
        			}
        		}

            return false;
        }

        virtual void getAnalysisUsage(AnalysisUsage &AU) const
        {
        	AU.setPreservesAll();
        }
        
        // curNode is a pointer now because otherwise you have to keep &ing it.. but visited is still a refernce... gaaah
        virtual bool reversePostOrder(BasicBlock* curNode, ValueMap<BasicBlock*, bool>& visited) {
        	visited[curNode] = true;
        	bool changed = false;

        	pred_iterator PI = pred_begin(curNode), 
        	              PE = pred_end(curNode);
        	if (PI != PE) {
        		// begin with a copy of out[first predecessor]
    			*(*in)[curNode] = *(*out)[*PI];  
        		
        		// fold meet over predecessors
        		for (PI++; PI != PE; PI++) {
        			meet((*in)[curNode], (*out)[*PI]);
        		}
        	} // (otherwise entry node, in[entry] already set above)
        	
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
        	
        	succ_iterator SI = succ_begin(curNode), SE = succ_end(curNode);
        	if (SI != SE) {
        		// begin with a copy of in[first successor]
    			*(*out)[curNode] = *(*in)[*SI];
    			
	        	// fold meet operator over successors
        		for (SI++; SI != SE; SI++) {
        			meet((*out)[curNode], (*in)[*SI]);
        		}
        	} else {
        		// boundary condition when it is an exit block
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
        virtual BitVector* transfer(BasicBlock&) = 0;
    };
}

