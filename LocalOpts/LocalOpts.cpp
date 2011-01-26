#include "llvm/Pass.h"
#include "llvm/BasicBlock.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Instruction.h"
#include "llvm/Constants.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"

#include <ostream>

using namespace llvm;

namespace
{

	struct LocalOpts : public BasicBlockPass
	{
		static char ID;
		LocalOpts() : BasicBlockPass(ID) {}
		
		virtual bool runOnBasicBlock(BasicBlock &bb) {
			bool modified = false;
			// Iterate over instructions
			for (BasicBlock::iterator i = bb.begin(), e = bb.end(); i != e; ++i)
			{
				Value* L = i->getOperand(0);
				Value* R = i->getOperand(1);

			    switch (i->getOpcode()) {
					default:
						
						break;
					case Instruction::Add:
						// Algebraic identities
						if (ConstantInt *LC = dyn_cast<ConstantInt>(L)) {
							if (LC->isZero()) {
								ReplaceInstWithValue(i->getParent()->getInstList(), i, R);
								modified = true;
							}
						}
						break;
					case Instruction::FAdd:
					case Instruction::Sub:
					case Instruction::FSub:
					case Instruction::Mul:
					case Instruction::FMul:
					case Instruction::UDiv:
					case Instruction::SDiv:
					case Instruction::FDiv:
					case Instruction::URem:
					case Instruction::SRem:
					case Instruction::FRem:
					case Instruction::Shl:						
					case Instruction::LShr:						
					case Instruction::AShr:					
					case Instruction::And:					
					case Instruction::Or:
						
						break;
						
					case Instruction::Xor:
						
						break;
			    }
				//errs() << *i << "\n";
			}
			return modified;
		}
	};
	
	char LocalOpts::ID = 0;
	static RegisterPass<LocalOpts> x("LocalOpts", "LocalOpts", false, false);
}
