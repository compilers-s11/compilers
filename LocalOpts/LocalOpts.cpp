#include "llvm/Pass.h"
#include "llvm/BasicBlock.h"
#include "llvm/Support/raw_ostream.h"

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
				errs() << *i << "\n";
			}
			return modified;
		}
	};
	
	char LocalOpts::ID = 0;
	static RegisterPass<LocalOpts> x("LocalOpts", "LocalOpts", false, false);
}
