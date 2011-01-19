#include "llvm/Pass.h"
#include "llvm/Function.h"
#include "llvm/Module.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Support/CallSite.h"

#include <ostream>
#include <fstream>
#include <iostream>

using namespace llvm;

namespace
{

  struct FInfo {
    StringRef name;
    size_t args;
    size_t blocks;
    size_t insts;
    int calls;
  };

class FunctionInfo : public ModulePass
{
  //output the function information to a file
  void printFunctionInfo(Module& M)
  {
    std::string name = M.getModuleIdentifier() + ".finfo";
    std::ofstream file(name.c_str());

  }
  
public:
	static char ID;

	FunctionInfo() :
	  ModulePass(ID)
	{
	}

	~FunctionInfo()
	{
	}

  // We don't modify the program, so we preserve all analyses
  virtual void getAnalysisUsage(AnalysisUsage &AU) const
  {
    AU.setPreservesAll();
  }
	
  virtual bool runOnFunction(Function &F)
  {
    FInfo info;
    //implement this
    info.name = F.getName();
    info.args = F.arg_size();

    info.calls = 0;
    for (Value::use_iterator U = F.use_begin(); U != F.use_end(); ++U) {
      if (Instruction *I = dyn_cast<Instruction>(*U)) {
        CallSite CS(I);
        if (CS.getCalledValue() == &F) {
          info.calls++;
//          errs() << "Used in: " << *I << "\n";
        }
      }
    }

    info.blocks = F.size();
    info.insts = 0;
    for (Function::iterator B = F.begin(); B != F.end(); ++B) {
      info.insts += B->size();
    }

    errs() << info.name << "\t" << info.args << "\t" << info.calls << "\t" << info.blocks << "\t" << info.insts << "\n";
    return false;
  }
  
  virtual bool runOnModule(Module& M)
  {
    errs() << "Name\t#Args\t#Calls\t#Blocks\t#Insts\n";
    for (Module::iterator MI = M.begin(), ME = M.end(); MI != ME; ++MI)
      {
	runOnFunction(*MI);
      }
    printFunctionInfo(M);
    return false;
  }
};

char FunctionInfo::ID = 0;
RegisterPass<FunctionInfo> X("function-info", "15745: Functions Information");
}
