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
		if (!((i+1)%10))
			errs() << " ";
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
	expr.opcode = I->getOpcode();

	if (isa<StoreInst>(*I)) {
		expr.dest = I->getOperand(1);
	}
	else {
		expr.dest = I; // the destination value is the instruction itself
	}

	// https://stackoverflow.com/questions/44946645/traversal-of-llvm-operands
	for (unsigned i = 0; i < I->getNumOperands(); ++i) {
		if (isa<StoreInst>(*I) && i == 1) continue; // Skip the destination operand
		
		Value* op = I->getOperand(i);
		expr.operands.push_back(op);
	}

	// errs() << expr.dest << " = " << " " << I->getOpcodeName() << " ";
	return expr;
}


bool ignore_instr(Instruction* I) {
	return (isa<AllocaInst>(*I) || I->isTerminator() || isa<CallInst>(*I));
	// terminator: branch, return
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
void scanBlockAndMark(BasicBlockInfo* bbinfo, BitVector &target, int set_value, \
	int n_begin, int n_end, int n_step, std::map<Expression, unsigned int> exprmap, SmallVector<Expression, 128> inv_exprmap) {

	int n = exprmap.size();
	// errs() << n << "\n";
	BitVector defined;
	defined.resize(n);
	defined.reset();

	for(unsigned bit = n_begin; bit != n_end; bit +=n_step) {
		if (!bbinfo->Exprs[bit]) continue;

		defined[bit] = 1;
		// errs() << "defined:"; print_bitvector(defined);

		Expression I_expr = inv_exprmap[bit];

		for(auto &op: I_expr.operands) {
			for(auto &pair : exprmap) {
				if (inv_exprmap[])
				Expression expr_ = it.first;
				unsigned use_bit = exprmap[expr_];
				if (expr_.dest == op && defined[use_bit]) {
						target[bit] = set_value;
						break;
				}
			}
		}
	}
}
void buildExprKill(BasicBlockInfo* bbinfo, std::map<Expression, unsigned int> exprmap, \
	SmallVector<Expression, 128> inv_exprmap) {

	bbinfo->ExprKill.reset();
	for(auto &pair : exprmap) {
		const Expression* expr_ = &(pair.first);
		unsigned bit = exprmap[*expr_];
		Instruction* I = expr_->I;

		for(auto &op: expr_->operands) {

			int n = exprmap.size();
			for(int i=0; i<n; i++) {
				if (!bbinfo->Exprs[i]) continue;
				Expression* def_expr = &(inv_exprmap[i]);
				if (def_expr->dest == op) {
					bbinfo->ExprKill[bit] = 1;
					break;
				}
			}
		}
	}
}

void buildDEExpr(BasicBlockInfo* bbinfo, std::map<Expression, unsigned int> exprmap) {
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
	bbinfo->DEExpr.reset();
	bbinfo->DEExpr |= bbinfo->Exprs;
	// scanBlockAndMark(bbinfo->DEExpr, 1, bbinfo->B->begin(), bbinfo->B->end(), exprmap, 0);
	scanBlockAndMark(bbinfo->DEExpr, 0, 0, exprmap.size(), 1, exprmap);
}
void buildUEExpr(BasicBlockInfo* bbinfo, std::map<Expression, unsigned int> exprmap) {
	// UEExpr: reverse
	bbinfo->UEExpr.reset();
	bbinfo->UEExpr |= bbinfo->Exprs;
	// scanBlockAndMark(bbinfo->UEExpr, 1, bbinfo->B->rbegin(), bbinfo->B->rend(), exprmap, 0);
	scanBlockAndMark(bbinfo->UEExpr, 0, exprmap.size()-1, -1, -1, exprmap);
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
	errs() << "Insert:\t\t";
	print_bitvector(edgeinfo->Insert);
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

		// Initialization
		for(auto B : ReversePostOrderTraversal<BasicBlock*>(entryBlock)) {
			blockmap[B].AvailOut.reset();
			blockmap[B].AvailOut.flip();
			blockmap[B].AvailIn.reset();
		}
		blockmap[entryBlock].AvailIn.reset();

		for(auto B : ReversePostOrderTraversal<BasicBlock*>(entryBlock)) {

			B->printAsOperand(errs(), false);
			
			if (!pred_empty(B)) {
				errs() << *B << "\n";
				errs() << "AvailIn "; print_bitvector(blockmap[B].AvailIn); errs()<<"\n";

				int flag = 0;
				for(BasicBlock *pred : predecessors(B)) {
					if (flag)
						blockmap[B].AvailIn &= blockmap[pred].AvailOut;
					else
						blockmap[B].AvailIn |= blockmap[pred].AvailOut;
					flag = 1;

					errs()<<"& "; pred->printAsOperand(errs(), false); print_bitvector(blockmap[pred].AvailOut); errs()<<"\n";
					errs()<<"= ";print_bitvector(blockmap[B].AvailIn); errs()<<"\n";
				}
			}

			BitVector negExprkill = blockmap[B].ExprKill;
			negExprkill.flip();
			// blockmap[B].AvailOut = blockmap[B].DEExpr | (blockmap[B].AvailIn & negExprkill);
			blockmap[B].AvailOut.reset();
			blockmap[B].AvailOut |= blockmap[B].AvailIn;
			blockmap[B].AvailOut &= negExprkill;
			blockmap[B].AvailOut |= blockmap[B].DEExpr;

			B->printAsOperand(errs(), false);
			errs() << " AvailOut\n";
			errs() << "AvailIn: "; print_bitvector(blockmap[B].AvailIn); errs()<<"\n";
			errs() << "& !(ExprKill): ";print_bitvector(negExprkill); errs()<<"\n";
			errs() << "+ DEExpr: "; print_bitvector(blockmap[B].DEExpr); errs()<<"\n";
			errs() << "= ";print_bitvector(blockmap[B].AvailOut); errs()<<"\n";

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

		// Initialization
		for(auto B : RRPOlist) {
			blockmap[B].AntOut.reset();
			blockmap[B].AntIn.reset();
			blockmap[B].AntIn.flip(); // initialize with all expressions
		}

		for(auto B : RRPOlist) {
			B->printAsOperand(errs(), false);
			errs() << " ";

			blockmap[B].AntOut.reset();
			if (!succ_empty(B)) {
				int flag = 0;
				for(BasicBlock *succ: successors(B)) {
					if (flag)
						blockmap[B].AntOut &= blockmap[succ].AntIn;
					else
						blockmap[B].AntOut |= blockmap[succ].AntIn;
					flag = 1;
				}
			}

			BitVector negExprkill = blockmap[B].ExprKill;
			negExprkill.flip();
			// blockmap[B].AntIn = blockmap[B].UEExpr | (blockmap[B].AntOut & negExprkill);
			blockmap[B].AntIn.reset();
			blockmap[B].AntIn |= blockmap[B].AntOut;
			blockmap[B].AntIn &= negExprkill;
			blockmap[B].AntIn |= blockmap[B].UEExpr;

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
			edgeinfo->Earliest.reset();
			errs() << "Build earliest "; print_bitvector(edgeinfo->Earliest); errs()<<"\n"; 
			edgeinfo->Earliest |= blockmap[i].ExprKill;
			errs() << "= ExprKill "; print_bitvector(blockmap[i].ExprKill); errs()<<"\n";
			edgeinfo->Earliest |= negAntOut_i;
			errs() << "+ !AntOut(i) "; print_bitvector(negAntOut_i); errs()<<"\n";
			edgeinfo->Earliest &= blockmap[j].AntIn;
			errs() << "&  AntIn(j)"; print_bitvector(blockmap[j].AntIn); errs()<<"\n";
			edgeinfo->Earliest &= negAvailOut_i;
			errs() << "&  !AvailOut(i)"; print_bitvector(negAvailOut_i); errs()<<"\n";
			errs() << "= "; print_bitvector(edgeinfo->Earliest); errs()<<"\n"; 
		}
	}

	// Forward flow
	void buildLater(Function &F) {
		BasicBlock* entryBlock = &(F.getEntryBlock());
		for(auto B : ReversePostOrderTraversal<BasicBlock*>(entryBlock)) {
			errs()<<"buildLater "<<B<<" "<<pred_size(B)<<" "<<pred_empty(B)<<"\n";
			if (pred_empty(B)) continue;

			blockmap[B].LaterIn.reset();
			blockmap[B].LaterIn.flip();

			for(BasicBlock* pred : predecessors(B)) {
				BBpair pair = std::make_pair(B, pred);
				EdgeInfo* edgeinfo = &(edgemap[&pair]);
				BasicBlockInfo* bbinfo_i = &(blockmap[pred]);
				BasicBlockInfo* bbinfo_j = &(blockmap[B]);
				
				// Later(i,j) = Earliest(i,j) + (LaterIn(i) & UEExpr(i)) for i in pred(j)
				edgeinfo->Later.reset();
				errs() << "Build Later "; print_bitvector(edgeinfo->Later); errs()<<"\n"; 
				edgeinfo->Later |= bbinfo_i->LaterIn;
				errs() << "= LaterIn "; print_bitvector(bbinfo_i->LaterIn); errs()<<"\n";
				edgeinfo->Later &= bbinfo_i->UEExpr;
				errs() << "& UEExpr(i) "; print_bitvector(bbinfo_i->UEExpr); errs()<<"\n";
				edgeinfo->Later |= edgeinfo->Earliest;
				errs() << "| Earliest(i,j) "; print_bitvector(edgeinfo->Earliest); errs()<<"\n";
				errs() << "= "; print_bitvector(edgeinfo->Later); errs()<<"\n"; 

				bbinfo_j->LaterIn &= edgeinfo->Later;

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

	    		if (ignore_instr(&I))
	    			continue;

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

	    for(auto &B : F) {
	    	buildExprKill(&(blockmap[&B]), exprmap, inv_exprmap);
	    	buildDEExpr(&(blockmap[&B]), exprmap);
	    	buildUEExpr(&(blockmap[&B]), exprmap);
	    }
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

				errs() << "Insert " << *cloned_instr << "\n";

				if (succ_size(i)==1) {
					errs() << "insert the expression at the end of block i\n";
					cloned_instr->insertInto(i, i->end());
				}
				else if(pred_size(j)==1) {
					errs() << "insert the expression at the entry of block j\n";
					cloned_instr->insertBefore(i->begin());
				}
				else {
					errs() << "split the edge (i,j) by creating a new block in between\n";
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