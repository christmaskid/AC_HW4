// This project is greatly aided by ChatGPT for LLVM syntax usage. 
// You can see the process here at this link: 
// https://chatgpt.com/share/67585d68-91e4-8003-b8bc-14576da175ad

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
#include "llvm/ADT/DepthFirstIterator.h"
#include "llvm/ADT/PostOrderIterator.h"
#include <map> // DenseMap is hard to use...

typedef std::pair<llvm::BasicBlock*, llvm::BasicBlock*> BBpair;

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
	errs() <<" ("<<n<< ")\n";
}

struct Expression {
	Instruction* I;
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
	// errs() << *I << "\n";
	Expression expr;
	expr.I = I;
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
	std::map<unsigned, Expression*> idx2expr;
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

	BitVector LaterIn;
	BitVector Delete;


	bool operator==(const BasicBlockInfo &x) const {
		return (B == x.B);
	}
	bool operator<(const BasicBlockInfo &x) const {
		return (B < x.B);
	}

};

void initBasicBlockInfoBitVector(BasicBlockInfo* b, unsigned n) {
	b->Exprs.resize(n);
	b->Exprs.reset();
	b->ExprKill.resize(n);
	b->ExprKill.reset();
	b->DEExpr.resize(n);
	b->DEExpr.reset();
	b->UEExpr.resize(n);
	b->UEExpr.reset();

	b->AvailOut.resize(n);
	b->AvailOut.reset();
	b->AvailIn.resize(n);
	b->AvailIn.reset();
	b->AntOut.resize(n);
	b->AntOut.reset();
	b->AntIn.resize(n);
	b->AntIn.reset();

	b->LaterIn.resize(n);
	b->LaterIn.reset();
	b->Delete.resize(n);
	b->Delete.reset();
}

void printBasicBlockInfo(BasicBlockInfo* bbinfo) {
	errs() << "> Block:\t";
	errs() << *(bbinfo->B);
	errs() << "ExprKill:\t";
	print_bitvector(bbinfo->ExprKill);
	errs() << "DEExpr:\t\t";
	print_bitvector(bbinfo->DEExpr);
	errs() << "UEExpr:\t\t";
	print_bitvector(bbinfo->UEExpr);

	errs() << "AvailOut:\t";
	print_bitvector(bbinfo->AvailOut);
	errs() << "AvailIn:\t";
	print_bitvector(bbinfo->AvailIn);
	errs() << "AntOut:\t\t";
	print_bitvector(bbinfo->AntOut);
	errs() << "AntIn:\t\t";
	print_bitvector(bbinfo->AntIn);

	errs() << "LaterIn:\t";
	print_bitvector(bbinfo->LaterIn);
	errs() << "Delete:\t\t";
	print_bitvector(bbinfo->Delete);
}

template <typename Iterator>
void scanBlockAndMark(BitVector &target, int set_value, \
	Iterator b_begin, Iterator b_end,\
	std::map<Expression, unsigned int> exprmap) {

	int n = exprmap.size();
	// errs() << n << "\n";
	BitVector defined;
	defined.resize(n);
	defined.reset();

	for(auto it = b_begin; it != b_end; it++) {
		Instruction &I = *it;
		// errs() << I << "\n";

		Expression I_expr = InstrToExpr(&I);
		if (exprmap.find(I_expr) != exprmap.end()) {
			unsigned bit = exprmap[I_expr];
			// errs() << bit << "\n";
			defined[bit] = 1;
		}
		// errs() << "defined:"; print_bitvector(defined);

		for(auto &op: I.operands()) {
			// Expression op_expr = InstrToExpr(dyn_cast<Instruction>(op)); // wrong!!
			// auto it = exprmap.find(op_expr);
			// if (it == exprmap.end())
			// 	continue;
			// unsigned bit = it->second;

			unsigned bit = -1;
			for(auto& it : exprmap) {
				Expression expr_ = it.first;
				if (expr_.dest == op) {
					bit = exprmap[expr_];
					break;
				}
			}
			if (bit!=-1 && defined[bit])
				target[bit] = set_value;
		}
	}
}
void buildExprKill(BasicBlockInfo* bbinfo, std::map<Expression, unsigned int> exprmap) {
	int n = exprmap.size();
	// BitVectors shall be initialized

	// ExprKill: = Definition
	for(int i=0;i<n;i++) {
		bbinfo->ExprKill[i] = bbinfo->Exprs[i];
	}

	// DEExpr:
	// the expression is evaluated AFTER (re)definition within the same block, 
	// and its operands are not redefined afterwards

	/* 	For each instruction:
			record that this expr is defined (eg. %1 = %2 + %3 --> defined[%1]=1)s
			for each operand : instruction
				if operand has been defined: mark as YES // evaluated

		For each instruction in reverse order:
			record that this expr is defined (eg. %1 = %2 + %3 --> defined[%1]=1)
			for each operand : instruction
				if operand has been defined: mark as NO
	*/
	scanBlockAndMark(bbinfo->DEExpr, 1, bbinfo->B->begin(), bbinfo->B->end(), exprmap);
	scanBlockAndMark(bbinfo->DEExpr, 0, bbinfo->B->rbegin(), bbinfo->B->rend(), exprmap);

	// UEExpr: reverse
	scanBlockAndMark(bbinfo->UEExpr, 1, bbinfo->B->rbegin(), bbinfo->B->rend(), exprmap);
	scanBlockAndMark(bbinfo->UEExpr, 0, bbinfo->B->begin(), bbinfo->B->end(), exprmap);
}


void print_edges(SmallVector<BBpair, 8> edges) {
	for(auto &pair : edges) {
		errs() << "(";
		pair.first->printAsOperand(errs(), false);
		errs() << ",";
		pair.second->printAsOperand(errs(), false);
		errs() << ") ";
	}
	errs() << "\n";
}

struct EdgeInfo {
	BBpair edge;
	BasicBlock* start;
	BasicBlock* end;

	BitVector Earliest;
	BitVector Later;
	BitVector Insert;

	BasicBlock* InsertBlock;

	bool operator==(const EdgeInfo &x) const {
		return (edge == x.edge);
	}
	bool operator<(const EdgeInfo &x) const {
		return (edge < x.edge);
	}
};
void initEdgeInfoBitVector(EdgeInfo* edgeinfo, BBpair pair, unsigned n) {
	edgeinfo->start = pair.first;
	edgeinfo->end = pair.second;

	edgeinfo->Earliest.resize(n);
	edgeinfo->Earliest.reset();

	edgeinfo->Later.resize(n);
	edgeinfo->Later.reset();
	edgeinfo->Insert.resize(n);
	edgeinfo->Insert.reset();

	edgeinfo->InsertBlock = NULL;
}

void printEdgeInfo(EdgeInfo* edgeinfo) {
	errs() << "(";
	edgeinfo->edge.first->printAsOperand(errs(), false);
	errs() << ",";
	edgeinfo->edge.second->printAsOperand(errs(), false);
	errs() << ")\n";

	errs() << "Earliest:\t";
	print_bitvector(edgeinfo->Earliest);
	errs() << "Later:\t\t";
	print_bitvector(edgeinfo->Later);
	errs() << "\n";
}

struct HelloWorldPass : public PassInfoMixin<HelloWorldPass> {

	// Expression related stuff
	unsigned int exprmap_n = 0;
	std::map<Expression, unsigned int> exprmap;
	SmallVector<Expression, 128> inv_exprmap;

	// CFG related stuff
	std::map<BasicBlock*, BasicBlockInfo> blockmap;
	SmallVector<BBpair, 8> edges;
	std::map<BBpair*, EdgeInfo> edgemap;
	SmallVector<BasicBlock*, 16> RRPOlist;

	void buildRRPOiter(BasicBlock* B, SmallVector<BasicBlock*, 16> &worklist, \
		std::map <BasicBlock*, bool> &visited) {

		if (!succ_empty(B)) {
			for(BasicBlock* succ : successors(B)) {
				// build edges at the same time
				edges.push_back(std::make_pair(B, succ));

				if (!visited[succ]) {
					visited[succ] = true;
					buildRRPOiter(succ, worklist, visited);
				}
			}
		}
		worklist.push_back(B);
	}

	void buildTraversalInfo(Function* F, SmallVector<BasicBlock*, 16> &worklist) {
		std::map <BasicBlock*, bool> visited;
		visited.clear();
		for(auto &B : *F) {
			visited[&B] = false;
		}

		BasicBlock* entryBlock = &(F->getEntryBlock());
		visited[entryBlock] = true;
		buildRRPOiter(entryBlock, worklist, visited);
	}

	void init(Function *F) {
		exprmap_n = 0;
		exprmap.clear();
		inv_exprmap.clear();
		// blocks.clear();
		blockmap.clear();
		RRPOlist.clear();

		buildTraversalInfo(F, RRPOlist);
	}

	// forward flow problem
	void buildAvailExpr(Function* F) {
		errs() << "Reverse postorder traversal on "<<F->getName()<<"\n";
		BasicBlock* entryBlock = &(F->getEntryBlock());
		for(auto B : ReversePostOrderTraversal<BasicBlock*>(entryBlock)) {
			B->printAsOperand(errs(), false);
			errs() << " ";

			BitVector negExprkill = blockmap[B].ExprKill;
			negExprkill.flip();
			// blockmap[B].AvailOut = blockmap[B].DEExpr | (blockmap[B].AvailIn & negExprkill);
			blockmap[B].AvailOut = blockmap[B].AvailIn;
			blockmap[B].AvailOut &= negExprkill;
			blockmap[B].AvailOut |= blockmap[B].DEExpr;

			blockmap[B].AvailIn.reset();
			if (!pred_empty(B)) {
				blockmap[B].AvailIn.flip();
				for(BasicBlock *pred : predecessors(B)) {
					blockmap[B].AvailIn &= blockmap[pred].AvailOut;
				}
			}
		}
		errs() << "\n";
	}

	// backward flow problem
	void buildAnticiExpr(Function* F) {
		// skip external functions
		if (F->isDeclaration())
			return;

		if (F->empty()) {
			errs() << "No entry block found.\n";
			return;
		}
		errs() << "Reverse postorder traversal on reversed "<<F->getName()<<"\n";

		BasicBlock* entryBlock = &(F->getEntryBlock());
		for(auto B : RRPOlist) {
			B->printAsOperand(errs(), false);
			errs() << " ";

			BitVector negExprkill = blockmap[B].ExprKill;
			negExprkill.flip();
			// blockmap[B].AntIn = blockmap[B].UEExpr | (blockmap[B].AntOut & negExprkill);
			blockmap[B].AntIn = blockmap[B].AntOut;
			blockmap[B].AntIn &= negExprkill;
			blockmap[B].AntIn |= blockmap[B].UEExpr;

			blockmap[B].AntOut.reset();
			if (!succ_empty(B)) {
				blockmap[B].AntOut.flip(); // initialize with all expressions
				for(BasicBlock *succ: successors(B)) {
					blockmap[B].AntOut &= blockmap[succ].AntIn;
				}
			}
		}
		errs() << "\n";
	}


	void buildEarliest() {
		for (auto &edge : edges) {
			EdgeInfo* edgeinfo = &(edgemap[&edge]);
			BasicBlock* i = edgeinfo->start;
			BasicBlock* j = edgeinfo->end;

			BitVector negAvailOut_i = blockmap[i].AvailOut;
			negAvailOut_i.flip();
			BitVector negAntOut_i = blockmap[i].AntOut;
			negAntOut_i.flip();
			
			// Earliest(i,j) = AntIn(j) & !(AvailOut(i)) & (ExprKill(i) + !AntOut(i))
			edgeinfo->Earliest |= blockmap[i].ExprKill;
			edgeinfo->Earliest |= negAntOut_i;
			edgeinfo->Earliest &= blockmap[i].AntIn;
			edgeinfo->Earliest &= negAvailOut_i;
		}
	}

	// Forward flow
	void buildLater(Function &F) {
		BasicBlock* entryBlock = &(F.getEntryBlock());
		for(auto B : ReversePostOrderTraversal<BasicBlock*>(entryBlock)) {
			if (pred_empty(B)) continue;

			blockmap[B].LaterIn.reset();
			blockmap[B].LaterIn.flip();

			for(BasicBlock* pred : predecessors(B)) {
				BBpair pair = std::make_pair(B, pred);
				EdgeInfo* edgeinfo = &(edgemap[&pair]);
				BasicBlockInfo* bbinfo = &(blockmap[B]);
				
				// Later(i,j) = Earliest(i,j) + (LaterIn(i) & UEExpr(i)) for i in pred(j)
				edgeinfo->Later = bbinfo->LaterIn;
				edgeinfo->Later &= bbinfo->UEExpr;
				edgeinfo->Later |= edgeinfo->Earliest;

				bbinfo->LaterIn &= edgeinfo->Later;

			}
		}
	}

	void buildInsertDelete(Function &F) {
		for(auto &edge: edges) {
			EdgeInfo* edgeinfo = &(edgemap[&edge]);
			// Insert(i,j) = Later(i,j) & !(LaterIn(j))
			edgeinfo->Insert.reset();
			edgeinfo->Insert |= edgeinfo->Later;
			BitVector negLaterIn_j = blockmap[edgeinfo->end].LaterIn;
			negLaterIn_j.flip();
			edgeinfo->Insert &= negLaterIn_j;

			// Delete(i) = UEExpr(i) & !(LaterIn(i))
			BasicBlock* i = edgeinfo->start;
			blockmap[i].Delete.reset();
			if (i != &(F.getEntryBlock())) {
				blockmap[i].Delete.reset();
				blockmap[i].Delete |= blockmap[i].UEExpr;
				BitVector negLaterIn_i = blockmap[i].LaterIn;
				negLaterIn_i.flip();
				blockmap[i].Delete &= negLaterIn_i;
			}
		}
	}

	void buildInfos(Function &F) {
		// first pass: build CFG and collect global expressions
	    for (auto &B : F) {
	    	errs() << "> basic block " << B << "\n";
			BasicBlockInfo bbinfo;
	    	bbinfo.B = &B;

	    	for (auto &I : B) {
	    		Expression expr = InstrToExpr(&I);
	    		bbinfo.exprs.push_back(expr);

	    		if (exprmap.find(expr) == exprmap.end()) {
	    			exprmap.insert(std::make_pair(expr, exprmap_n++));
	    			inv_exprmap.push_back(expr);
	    		}
	    	}
	    	blockmap.insert(std::make_pair(&B, bbinfo));

	    }
	    errs() << "N = " << exprmap_n << "\n";

	    // second pass: build bitvectors
	    for(auto &B : F) {
	    	initBasicBlockInfoBitVector(&(blockmap[&B]), exprmap_n);

	    	for (auto &expr : blockmap[&B].exprs) {	
	    		unsigned idx = exprmap[expr];
	    		blockmap[&B].Exprs[idx]=1;
	    		blockmap[&B].idx2expr[idx] = &expr;
	    	}
	    	// print_bitvector(blockmap[&B].Exprs);
	    }

	    for(auto &B : F)
	    	buildExprKill(&(blockmap[&B]), exprmap);
	    buildAvailExpr(&F);
	    buildAnticiExpr(&F);

	    // Edges
		for(auto &edge : edges) {
			EdgeInfo edgeinfo;
			edgeinfo.edge = edge;
			initEdgeInfoBitVector(&edgeinfo, edge, exprmap_n);
			edgemap[&edge] = edgeinfo;
		}
	    buildEarliest();
	    buildLater(F);

	    // Code motion
	    buildInsertDelete(F);

	    for(auto &B : F) {
	    	printBasicBlockInfo(&(blockmap[&B]));
	    }
		for(auto &edge : edges) {
			printEdgeInfo(&(edgemap[&edge]));
		}
	}

	void rewriteInsert(Function* F) {
		for(auto &edge : edges) {
			EdgeInfo* edgeinfo = &(edgemap[&edge]);
			BasicBlock* i = edgeinfo->start;
			BasicBlock* j = edgeinfo->end;

			IRBuilder<> builder_i(i);

			for(int idx = 0; idx < exprmap_n; idx++) {
				if (!edgeinfo->Insert[idx]) continue;
				Expression* expr = &(inv_exprmap[idx]);
				Instruction* cloned_instr = expr->I->clone();

				if (succ_size(i)==1) {
					// insert the expression at the end of block i
					cloned_instr->insertInto(i, i->end());
				}
				else if(pred_size(j)==1) {
					// insert the expression at the entry of block j
					cloned_instr->insertBefore(i->begin());
				}
				else {
					// split the edge (i,j) by creating a new block in between
					LLVMContext &Context = F->getContext();
					BasicBlock* newBlock = BasicBlock::Create(Context, "new_block", F);

					i->getTerminator()->replaceUsesOfWith(j, newBlock);
					BranchInst::Create(j, newBlock);
					cloned_instr->insertBefore(newBlock->begin());
				}
			}
		}
	}
	void rewriteDelete(Function* F) {
		for(auto &B : *F) {
			BasicBlockInfo* bbinfo = &(blockmap[&B]);
			for(int idx=0; idx<exprmap_n; idx++) {
				if (!bbinfo->Delete[idx]) continue;
				Instruction* I = bbinfo->idx2expr[idx]->I;
				// remove the expression
				I->eraseFromParent();
			}
		}
	}

	void codeMotion(Function* F) {
		rewriteInsert(F);
		rewriteDelete(F);
	}

    PreservedAnalyses run(Module &M, ModuleAnalysisManager &AM) {
    	errs() << "Hello from run()!\n"; // Check if the pass is called
        for (auto &F : M) {
        	errs() << F.getName() << " " << F.size() << "\n";
        	errs() << F << "\n";

			if (F.isDeclaration()) // exclude external functions
				continue;
			if (F.empty()) {
				errs() << "No entry block found.\n";
				continue;
			}
        	init(&F);
        	buildInfos(F);
        	codeMotion(&F);
        	errs() << "After: " << F.getName() << " " << F << "\n";
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