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
    struct DCE : public Dataflow<false>, public FunctionPass
    {
        static char ID;

        DCE() : Dataflow<false>(), FunctionPass(ID) {
          index = new std::map<Value*, int>();
          r_index = new std::vector<Value*>();
          instIn = new ValueMap<Instruction*, BitVector*>();
        }

        // Map from instructions/argument to their index in the bitvector
        std::map<Value*, int> *index;
        
        // Map from index in bitvector back to instruction/argument
        std::vector<Value*> *r_index;
        
        // convenience
        int numTotal;
        int numArgs;

        // map from instructions to bitvector corresponding to program point BEFORE that instruction
        ValueMap<Instruction*, BitVector*> *instIn;

        virtual void meet(BitVector *op1, const BitVector *op2) {
          // intersection
          *op1 &= *op2;
        }

        virtual void getBoundaryCondition(BitVector *entry) {
          // out[b] = start with everything faint 
          *entry = BitVector(numTotal, true);
        }
        

        // An instruction is defines a variable iff its type is not void
        bool isDefinition(Instruction *ii) {
          return (!ii->getType()->isVoidTy());
        }

        // Terminators and Calls can never be removed from the function due to possible side effects
        // Stores can sometimes be removed, but they form a special case in the function Eliminate
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
          
          // Add function arguments to maps
          for (Function::arg_iterator ai = F.arg_begin(), ae = F.arg_end(); ai != ae; ai++) {
            (*index)[&*ai] = numArgs;
            r_index->push_back(&*ai);
            numArgs++;
          }
          numTotal = numArgs; 

          
          // Add definitions to maps
          for (inst_iterator ii = inst_begin(&F), ie = inst_end(&F); ii != ie; ii++) {
            if (isDefinition(&*ii)) {
              (*index)[&*ii] = numTotal;
              r_index->push_back(&*ii);
              numTotal++;
            }
          }
          
          // Initialize instIn
          for (inst_iterator ii = inst_begin(&F), ie = inst_end(&F); ii != ie; ii++) {
            (*instIn)[&*ii] = new BitVector(numTotal, true); //TODO true orfalse
          }
          top = new BitVector(numTotal, true);
          
          // Run data flow 
          Dataflow<false>::runOnFunction(F);

          // Eliminate returns true if any instruction was removed
          return Eliminate(F);
        }
        
        virtual BitVector* transfer(BasicBlock& bb) {
          // We iterate over instructions in reverse beginning with out[bb]
          BitVector* next = new BitVector(*((*out)[&bb]));
          
          // Temporary variables for convenience
          BitVector* instVec = next; // for empty blocks
          Instruction* inst;


          // Go through instructions in reverse
          BasicBlock::iterator ii = --(bb.end()), ib = bb.begin();
          while (true) {
            
            // Inherit data from next instruction
            inst = &*ii;
            instVec = (*instIn)[inst];            
            *instVec = *next;
            
            if (!isa<StoreInst>(inst) && (isa<CallInst>(inst)|| isa<TerminatorInst>(inst) 
                || (!(*instVec)[(*index)[inst]]))) {
              // This instruction is either a call, terminator, or some instruction with a non-faint LHS
              // In this case, we must mark all variables used in the instruction as non-faint
              // For function calls, the arguments to the function are not faint (and the function call cannot be eliminated) even if its return value is never used because the function might have side effects.
              User::op_iterator OI, OE;
              for (OI = inst->op_begin(), OE=inst->op_end(); OI != OE; ++OI) {
                if (isa<Instruction>(*OI) || isa<Argument>(*OI)) {
                  (*instVec)[(*index)[*OI]] = false;
                }
              }
            } else if (isa<StoreInst>(inst)) {
              // For stores, mark stored value as not-faint iff the destination of a store is locally allocated and not-faint, OR if it is a global/argument
              // In case of stores to a global/argument, the stored value can never be faint since it may be used outside the function.
              StoreInst* si = cast<StoreInst>(inst);
              Value * addr = si->getPointerOperand();

              if (isa<AllocaInst>(addr) && !(*instVec)[(*index)[addr]]) {
                Value * val = si->getValueOperand();
                if (isa<Instruction>(val) || isa<Argument>(val))
                  (*instVec)[(*index)[val]] = false;
              }
            }
            next = instVec;

            if (ii == ib) break;
            --ii;
          }
          
          instVec = new BitVector(*instVec);
          return instVec;
        }

        // Dead Code Elimination. Removes all instructions that create/store to faint variables
        // Do not remove:
        // - Function Calls
        // - Stores to global variables or arguments
        // Such instructions cannot be removed as they might have side effects
        virtual bool Eliminate(Function &F) {
          //did we actually change anything? LLVM needs this info
          bool modified = false; 

          //assumes the FVA analysis has already been completed
          BitVector *faint = (*in)[&(F.getEntryBlock())];

          //Iterate over all instructions in the function, and remove ones that define faint variables
          inst_iterator ii = inst_begin(F);

          while (ii != inst_end(F)) {
            if (isEliminableDef(&*ii) && ((*faint)[(*index)[&*ii]])) {
              // Instruction is not a function call, terminator or store
              inst_iterator j = ii;
              ++ii;
              j->eraseFromParent();
              modified = true;
            } else if (isa<StoreInst>(&*ii)) {
              Value * addr = cast<StoreInst>(&*ii)->getPointerOperand();
              if (isa<AllocaInst>(addr) && (*faint)[(*index)[addr]]) {
                //make sure store is to a variable allocated within this function
                inst_iterator j = ii;
                ++ii;
                j->eraseFromParent();
                modified = true;
              } else {
                //Do not remove stores to a global variable or arguments
                ++ii;
              }
            } else {
              //Do not remove function calls/terminators.
              ++ii;
            }
          }

          return modified;
        }
    };

    char DCE::ID = 0;
    static RegisterPass<DCE> x("DCE", "DCE", false, false);
}

