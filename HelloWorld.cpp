#include "llvm/Pass.h"
#include "llvm/Passes/PassBuilder.h"
#include "llvm/Passes/PassPlugin.h"
#include "llvm/Support/raw_ostream.h"

// Ref.: https://stackoverflow.com/questions/21708209/get-predecessors-for-basicblock-in-llvm
// Get a BB's predecessors
#include "llvm/IR/CFG.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/ADT/BitVector.h" // set operation
#include "llvm/ADT/DenseMap.h" // mapping expression to bitvector position
#include <map> // DenseMap is hard to use...

using namespace llvm;

namespace {

void print_value(Value v) {
	if (v.hasName())
		errs() << v.getName();
	else
		errs() << v;
}
void print_bitvector(BitVector bv) {
	int n = bv.size();
	for(int i=0;i<n;i++) {
		errs() << bv[i];
	}
	errs() << "\n";
}

struct Expression {
	Value* dest;
	unsigned opcode;
	SmallVector<Value*, 4> operands;

	// https://stackoverflow.com/questions/7204283/how-can-i-use-a-struct-as-key-in-a-stdmap
	bool operator<(const Expression &x) const {
		if (x.dest != dest)
			return (x.dest < dest);
		if (x.opcode != opcode) 
			return (x.opcode < opcode);
		if (x.operands.size() != operands.size()) 
			return (x.operands.size() < operands.size());

		int n = x.operands.size();
		for(int i=0; i<n; i++) {
			if (x.operands[i] != operands[i])
				return (x.operands[i] < operands[i]);
		}
		return false;
	}
	bool operator==(const Expression &x) const {
		if (x.dest != dest)
			return false;
		if (x.opcode != opcode) 
			return false;
		if (x.operands.size() != operands.size()) 
			return false;

		int n = x.operands.size();
		for(int i=0; i<n; i++) {
			if (x.operands[i] != operands[i])
				return false;
		}
		return true;
	}
};


// Ref. https://www.cs.toronto.edu/~pekhimenko/courses/cscd70-w18/docs/Tutorial%202%20-%20Intro%20to%20LLVM%20(Cont).pdf
// User-Use-Usee Design:
// Important: class hierarchies - Value -> User -> Instruction
// An User keeps track of a list of Values that it uses as Operands
Expression InstrToExpr(Instruction* I) {
	// https://llvm.org/doxygen/classllvm_1_1Instruction.html
	errs() << *I << "\n";
	Expression expr;
	expr.dest = I; // the destination valu is the instruction itself
	expr.opcode = I->getOpcode();

	// errs() << expr.dest << " = " << " " << I->getOpcodeName() << " ";

	// https://stackoverflow.com/questions/44946645/traversal-of-llvm-operands
	for(auto iter = I->op_begin(); iter != I->op_end(); ++iter) {
		Value* op = *iter;
		expr.operands.push_back(op);
		// errs() << "operand:";
		// print_value(*op);
		// errs() << " ";
	}
	// errs() << "\n";

	// for(auto iter = I->user_begin(); iter != I->user_end(); ++iter) {
		// Value* user = *iter;
		// errs() << "user:";
		// print_value(*user);
		// errs() << " ";
	// }
	// errs() << "\n";

	return expr;
}


struct BasicBlockInfo {
	BasicBlock* B;
	SmallVector<Expression> exprs;
	// preds: for(BasicBlock *pred : predecessors(&B))
	// succs: for(BasicBlock *succ : successors(&B))

	BitVector Exprs;
	BitVector DEExpr;
	BitVector UEExpr;
	BitVector ExprKill;
	BitVector AvailOut;
	BitVector AvailIn;
	BitVector AntOut;
	BitVector AntIn;

	bool operator==(const BasicBlockInfo &x) const {
		return (B == x.B);
	}
	bool operator<(const BasicBlockInfo &x) const {
		return (B < x.B);
	}

};

template <typename Iterator>
void scanBlockAndMark(BitVector &target, int set_value, \
	Iterator b_begin, Iterator b_end,\
	std::map<Expression, unsigned int> exprmap) {

	int n = exprmap.size();
	BitVector defined;
	defined.resize(n);
	defined.clear();

	for(auto it = b_begin; it != b_end; it++) {
		Instruction &I = *it;
		errs() << I << "\n";

		Expression I_expr = InstrToExpr(&I);
		if (exprmap.find(I_expr) != exprmap.end()) {
			defined[exprmap[I_expr]] = 1;
		}
		errs() << "defined:"; print_bitvector(defined);

		for(auto &op: I.operands()) {
			Expression op_expr = InstrToExpr(dyn_cast<Instruction>(op));
			auto it = exprmap.find(op_expr);
			if (it == exprmap.end())
				continue;
			unsigned bit = it->second;
			if (defined[bit])
				target[bit] = set_value;
		}
	}
}
void setExpr(BasicBlockInfo* bbinfo, std::map<Expression, unsigned int> exprmap) {
	int n = exprmap.size();

	// ExprKill: = Definition
	bbinfo->ExprKill.clear();
	for(int i=0;i<n;i++) {
		bbinfo->ExprKill[i] = bbinfo->Exprs[i];
	}

	// DEExpr:
	// the expression is evaluated AFTER (re)definition within the same block, 
	// and its operands are not redefined afterwards

	/* 	For each instruction:
			record that this expr is defined (eg. %1 = %2 + %3 --> defined[%1]=1)
			for each operand : instruction
				if operand has been defined: mark as YES // evaluated

		For each instruction in reverse order:
			record that this expr is defined (eg. %1 = %2 + %3 --> defined[%1]=1)
			for each operand : instruction
				if operand has been defined: mark as NO
	*/
	bbinfo->DEExpr.resize(n);
	bbinfo->DEExpr.clear();
	scanBlockAndMark(bbinfo->DEExpr, 1, bbinfo->B->begin(), bbinfo->B->end(), exprmap);
	scanBlockAndMark(bbinfo->DEExpr, 0, bbinfo->B->rbegin(), bbinfo->B->rend(), exprmap);
	errs() << "DEExpr: ";
	print_bitvector(bbinfo->DEExpr);

	// UEExpr: reverse
	bbinfo->UEExpr.resize(n);
	bbinfo->UEExpr.clear();
	scanBlockAndMark(bbinfo->UEExpr, 1, bbinfo->B->rbegin(), bbinfo->B->rend(), exprmap);
	scanBlockAndMark(bbinfo->UEExpr, 0, bbinfo->B->begin(), bbinfo->B->end(), exprmap);
	errs() << "UEExpr: ";
	print_bitvector(bbinfo->UEExpr);
}


struct HelloWorldPass : public PassInfoMixin<HelloWorldPass> {

	// SmallVector<BasicBlockInfo, 8> blocks;
	unsigned int exprmap_n = 0;
	std::map<Expression, unsigned int> exprmap;
	SmallVector<Expression, 128> inv_exprmap;
	std::map<unsigned, BasicBlockInfo> blockmap;

	void init() {
		exprmap_n = 0;
		exprmap.clear();
		inv_exprmap.clear();
		// blocks.clear();
		blockmap.clear();
	}

	void buildBlockInfo(BasicBlock &B) {
		BasicBlockInfo bbinfo;
    	bbinfo.B = &B;
    	// bbinfo.n_pred = 0;
    	// bbinfo.n_succ = 0;

    	// for(BasicBlock *pred : predecessors(&B)) {
    	// 	bbinfo.n_pred++;
    	// 	bbinfo.preds.push_back(pred);
    	// }
    	// for(BasicBlock *succ : successors(&B)) {
    	// 	bbinfo.n_succ++;
    	// 	bbinfo.succs.push_back(succ);
    	// }
    	int i = 0;
    	for (auto &I : B) {
    		Expression expr = InstrToExpr(&I);
    		bbinfo.exprs.push_back(expr);

    		if (exprmap.find(expr) == exprmap.end()) {
    			exprmap.insert(std::make_pair(expr, exprmap_n++));
    			inv_exprmap.push_back(expr);
    		}
    	}
    	blockmap.insert(std::make_pair(i++, bbinfo));
    	// blocks.push_back(bbinfo);
	}

	void buildInfos(Function &F) {

		// first pass: build CFG and collect global expressions
		unsigned int i = 0;
	    for (auto &B : F) {
	    	// errs() << "> basic block " << B << "\n";

	    }

	    // second pass: build bitvectors
	    int n = i;
	    for (int i=0; i<n; i++) {
	    	errs() << "Check:" << *(blockmap[i].B) << ", i=" << i << "\n";

	    	blockmap[i].Exprs.resize(exprmap_n);
	    	blockmap[i].Exprs.reset();

	    	for (auto &expr : blockmap[i].exprs) {	
	    		unsigned idx = exprmap[expr];
	    		blockmap[i].Exprs[idx]=1;
	    		// errs() << idx << *(expr.I) <<  "\t" << "\n";
	    	}
	    	// for(int j=0;j<exprmap_n;j++) {
	    	// 	errs() << blockmap[i].Exprs[j];
	    	// }
	    	// errs() << "\n";
	    }

	}

    PreservedAnalyses run(Module &M, ModuleAnalysisManager &AM) {
    	
        for (auto &F : M) {
        	errs() << F.getName() << " " << F.size() << "\n";

        	init();
        	buildInfos(F);
        }
        return PreservedAnalyses::all();
    }
};

}

extern "C" LLVM_ATTRIBUTE_WEAK ::llvm::PassPluginLibraryInfo
llvmGetPassPluginInfo() {
    return {
        .APIVersion = LLVM_PLUGIN_API_VERSION,
        .PluginName = "HelloWorld pass",
        .PluginVersion = "v0.1",
        .RegisterPassBuilderCallbacks = [](PassBuilder &PB) {
            PB.registerPipelineStartEPCallback(
                [](ModulePassManager &MPM, OptimizationLevel Level) {
                    MPM.addPass(HelloWorldPass());
                });
        }
    };
}