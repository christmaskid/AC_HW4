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
#include <string>

// Ref.: https://stackoverflow.com/questions/60514223/how-to-insert-a-basic-block-between-two-block-in-llvm
#include "llvm/Transforms/Utils/BasicBlockUtils.h"

#include "llvm/Transforms/Utils/Cloning.h"

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
void scanBlockAndMark(BitVector &target, int set_value, \
	Iterator b_begin, Iterator b_end, std::map<Expression, unsigned int> exprmap) {

	// Get definitions and uses
	// A O(n^2) method. Maximum size of operands in an instruction is constant (<=3).
	for(auto it = b_begin; it != b_end; ++it) {
		Instruction &I = *it;
		// errs() << "I " << I << "\n";
		Expression E = InstrToExpr(&I);
		unsigned bit = exprmap[E];

		for(auto &op : E.operands) {
			int flag = 0;
			// errs() << "op ";
			// op->printAsOperand(errs(), false);
			// errs() << "\n";

			for(auto it2 = it; !flag && it2 != b_end; ++it2) {
				Instruction &I2 = *it2;
				// errs() << "I2 " << I2 << "\n";
				Expression E2 = InstrToExpr(&I2);

				if (E2.dest == op) {
					target[bit] = set_value;
					flag = 1;
				}
			}
		}
	}

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
	std::map<BBpair, EdgeInfo> edgemap;

	// In the forward problem, we can always do reverse postorder traversal on the function's
	// CFG because there is always only one entry block.
	// However, we may not be able to do the reverse postorder traversal on the reversed CFG
	// because there may be more than one exit blocks.
	// Then, the worklist algorithm cannot end in one rounds -> worklist still needed.

	void init(Function *F) {
		exprmap_n = 0;
		exprmap.clear();
		inv_exprmap.clear();
		// blocks.clear();
		blockmap.clear();
	}

	void buildExprKill(BasicBlockInfo* bbinfo) {

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
	void buildDEExpr(BasicBlockInfo* bbinfo) {
		// DEExpr:
		// the expression is evaluated AFTER (re)definition within the same block, 
		// and its operands are not redefined afterwards
		bbinfo->DEExpr.reset();
		bbinfo->DEExpr |= bbinfo->Exprs;
		scanBlockAndMark(bbinfo->DEExpr, 0, bbinfo->B->begin(), bbinfo->B->end(), exprmap);
	}
	void buildUEExpr(BasicBlockInfo* bbinfo) {
		// UEExpr: reverse
		bbinfo->UEExpr.reset();
		bbinfo->UEExpr |= bbinfo->Exprs;
		scanBlockAndMark(bbinfo->UEExpr, 0, bbinfo->B->rbegin(), bbinfo->B->rend(), exprmap);
	}
	// forward flow problem
	void buildAvailExpr(Function* F) {
		errs() << "Reverse postorder traversal on "<<F->getName()<<"\n";

		BasicBlock* entryBlock = &(F->getEntryBlock());

		// Initialization
		for(auto B : ReversePostOrderTraversal<BasicBlock*>(entryBlock)) {
			blockmap[B].AvailOut.reset();
			blockmap[B].AvailIn.reset();
			blockmap[B].AvailIn.flip();			
		}
		blockmap[entryBlock].AvailIn.reset();

		for(auto B : ReversePostOrderTraversal<BasicBlock*>(entryBlock)) {

			BitVector negExprkill = blockmap[B].ExprKill;
			negExprkill.flip();
			// blockmap[B].AvailOut = blockmap[B].DEExpr | (blockmap[B].AvailIn & negExprkill);
			blockmap[B].AvailOut.reset();
			blockmap[B].AvailOut |= blockmap[B].AvailIn;
			blockmap[B].AvailOut &= negExprkill;
			blockmap[B].AvailOut |= blockmap[B].DEExpr;

			if (!succ_empty(B)) {
				for(BasicBlock *succ : successors(B)) {
					blockmap[succ].AvailIn &= blockmap[B].AvailOut;
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

		// Initialization
		for(auto &BB : *F) {
			BasicBlock* B = &BB;
			blockmap[B].AntIn.reset();
			blockmap[B].AntOut.reset();
			if (!succ_empty(B))
				blockmap[B].AntOut.flip(); // initialize with all expressions
		}
		// Worklist algorithm
		bool changed = true;
		while (changed) {
			changed = false;

			for(auto B : post_order(F)) {
				B->printAsOperand(errs(), false);
				errs() << " ";

				BitVector oldVector(blockmap[B].AntIn);

				BitVector negExprkill = blockmap[B].ExprKill;
				negExprkill.flip();
				// blockmap[B].AntIn = blockmap[B].UEExpr | (blockmap[B].AntOut & negExprkill);
				blockmap[B].AntIn.reset();
				blockmap[B].AntIn |= blockmap[B].AntOut;
				blockmap[B].AntIn &= negExprkill;
				blockmap[B].AntIn |= blockmap[B].UEExpr;

				for(int i=0; !changed && i<exprmap_n; i++) {
					if (oldVector[i] != blockmap[B].AntIn[i]) {
						changed = true;
						break;
					}
				}

				if (!pred_empty(B)) {
					for(BasicBlock *pred : predecessors(B)) {
						BitVector oldVector(blockmap[pred].AntOut);
						blockmap[pred].AntOut &= blockmap[B].AntIn;

						B->printAsOperand(errs(), false);
						errs() << ".AntIn = ";
						print_bitvector(blockmap[B].AntIn);
						errs() << " & -> ";
						pred->printAsOperand(errs(), false);
						errs() << ".AntOut = ";
						print_bitvector(blockmap[pred].AntOut);

						for(int i=0; !changed && i<exprmap_n; i++) {
							if (oldVector[i] != blockmap[pred].AntOut[i]) {
								changed = true;
							}
						}
					}
				}
			}
		}
		errs() << "\n";
	}


	void buildEarliest() {
		for (auto &edge : edges) {
			EdgeInfo* edgeinfo = &(edgemap[edge]);
			BasicBlock* i = edgeinfo->start;
			BasicBlock* j = edgeinfo->end;

			BitVector negAvailOut_i = blockmap[i].AvailOut;
			negAvailOut_i.flip();
			BitVector negAntOut_i = blockmap[i].AntOut;
			negAntOut_i.flip();
			
			// Earliest(i,j) = AntIn(j) & !(AvailOut(i)) & (ExprKill(i) + !AntOut(i))
			edgeinfo->Earliest.reset();
			edgeinfo->Earliest |= blockmap[i].ExprKill;
			edgeinfo->Earliest |= negAntOut_i;
			edgeinfo->Earliest &= blockmap[j].AntIn;
			edgeinfo->Earliest &= negAvailOut_i;
		}
	}

	// Forward flow
	void buildLater(Function* F) {
		// Initialization
		for (auto &BB : *F) {
			BasicBlock* B = &BB;
			blockmap[B].LaterIn.reset();
			blockmap[B].LaterIn.flip();
		}
		BasicBlock* entryBlock = &(F->getEntryBlock());
		blockmap[entryBlock].LaterIn.reset();

		for(auto B : ReversePostOrderTraversal<BasicBlock*>(entryBlock)) {
			// errs()<<"buildLater "<<B->getName()<<" "<<pred_size(B)<<" "<<pred_empty(B)<<"\n";

			if (!succ_empty(B)) {
				for(BasicBlock* succ : successors(B)) {
					BBpair pair = std::make_pair(B, succ);
					EdgeInfo* edgeinfo = &(edgemap[pair]);
					BasicBlockInfo* bbinfo_i = &(blockmap[B]);
					BasicBlockInfo* bbinfo_j = &(blockmap[succ]);
					
					// Later(i,j) = Earliest(i,j) + (LaterIn(i) & UEExpr(i)) for i in pred(j)
					edgeinfo->Later.reset();
					// errs() << "Build Later "; print_bitvector(edgeinfo->Later); errs()<<"\n"; 
					edgeinfo->Later |= bbinfo_i->LaterIn;
					// errs() << "= LaterIn "; print_bitvector(bbinfo_i->LaterIn); errs()<<"\n";
					edgeinfo->Later &= bbinfo_i->UEExpr;
					// errs() << "& UEExpr(i) "; print_bitvector(bbinfo_i->UEExpr); errs()<<"\n";
					edgeinfo->Later |= edgeinfo->Earliest;
					// errs() << "| Earliest(i,j) "; print_bitvector(edgeinfo->Earliest); errs()<<"\n";
					// errs() << "= "; print_bitvector(edgeinfo->Later); errs()<<"\n"; 

					bbinfo_j->LaterIn &= edgeinfo->Later;
				}
			}
		}
	}

	void buildInsertDelete(Function &F) {
		for(auto &edge: edges) {
			EdgeInfo* edgeinfo = &(edgemap[edge]);
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
				blockmap[i].Delete |= blockmap[i].UEExpr;
				BitVector negLaterIn_i = blockmap[i].LaterIn;
				negLaterIn_i.flip();
				blockmap[i].Delete &= negLaterIn_i;
			}
		}
	}


	void buildNodes(Function &F) {
		// first pass: build CFG and collect global expressions
	    for (auto &B : F) {
	    	// errs() << "> basic block " << B << "\n";
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
	    // errs() << "N = " << exprmap_n << "\n";

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
	}

	void buildEdges(Function &F) {
	    for (auto &B : F) {
	    	if (succ_empty(&B)) continue;

			for(BasicBlock* succ : successors(&B))
				edges.push_back(std::make_pair(&B, succ));
	    }
	    // errs() << "buildEdges\n";
	    // print_edges(edges);
		for(auto &edge : edges) {
			EdgeInfo edgeinfo;
			edgeinfo.edge = edge;
			initEdgeInfoBitVector(&edgeinfo, edge, exprmap_n);
			edgemap[edge] = edgeinfo;
		}
	}

	void buildInfos(Function &F) {
		// Collect CFG info
		buildNodes(F);
	    buildEdges(F); // must be after nodes

	    // Finally: let's build LCM related variables!

	    // Nodes
	    for(auto &B : F) {
	    	buildExprKill(&(blockmap[&B]));
	    	buildDEExpr(&(blockmap[&B]));
	    	buildUEExpr(&(blockmap[&B]));
	    }
	    buildAvailExpr(&F);
	    buildAnticiExpr(&F);

	    // Edges
	    buildEarliest();
	    buildLater(&F);

	    // Code motion
	    buildInsertDelete(F);

	    for(auto &B : F) {
	    	printBasicBlockInfo(&(blockmap[&B]));
	    }
		for(auto &edge : edges) {
			printEdgeInfo(&(edgemap[edge]));
		}
	}

	void rewriteInsert(Function* F) {
		int cnt = 0;
		for(auto &edge : edges) {
			EdgeInfo* edgeinfo = &(edgemap[edge]);
			if (edgeinfo->Insert.empty())
				continue;

			cnt++;
			BasicBlock* i = edgeinfo->start;
			BasicBlock* j = edgeinfo->end;

			int choice = -1;
			IRBuilder<> *builder = nullptr;

			if (!i->getSingleSuccessor()) {
				choice = 1;
				builder = new IRBuilder<>(i->getContext());
			} else if (!j->getSinglePredecessor()) {
				choice = 2;
				builder = new IRBuilder<>(j->getContext());
			} else {
				choice = 3;
				// Don't put them into the function yet!!!
				// Ref.: https://stackoverflow.com/questions/61181446/how-to-build-a-empty-basicblock-and-insert-a-instruction-in-the-front
				LLVMContext &context = i->getContext();
				builder = new IRBuilder<>(i->getContext());
				edgeinfo->InsertBlock = BasicBlock::Create(context, "newBlock" + std::to_string(cnt));

				errs()<<"Insert new block between ";
				i->printAsOperand(errs(), false);
				errs()<<" and ";
				j->printAsOperand(errs(), false);
				errs()<<":\n";
			}

			for(int idx = exprmap_n-1; idx >= 0; idx--) {
				if (!edgeinfo->Insert[idx]) continue;
				Expression* expr = &(inv_exprmap[idx]);
				Instruction* cloned_instr = expr->I->clone();
				errs()<<*cloned_instr<<"\n";

				switch(choice) {
					case 1:
					// If i has only one successor, we insert the expressions at the end of block i.
						builder->SetInsertPoint(i->getTerminator());
						builder->Insert(cloned_instr);
						break;
					case 2:
					// else If j has only one predecessor, we insert the expressions at the entry of block j.
						builder->SetInsertPoint(j->getFirstInsertionPt());
						builder->Insert(cloned_instr);
						break;
					case 3:
					// else, we split the the edge (i, j) by creating a new block to insert the expressions.
						builder->SetInsertPoint(edgeinfo->InsertBlock->getFirstInsertionPt());
						builder->Insert(cloned_instr);
				}

				// Ref.: https://stackoverflow.com/questions/30319747/when-and-where-did-the-llvm-ir-instruction-set-its-parent-basicblock

				// Ref. Cornell course, LLVM for grad: addtomul example
    			// Everywhere the old instruction was used as an operand,
    			// use our new instruction instead.
    			for (auto& U : expr->I->uses()) {
    				User* user = U.getUser(); // A User is anything with operands
    				user->setOperand(U.getOperandNo(), cloned_instr);
    			}
			}
			delete builder;
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
	void cleanUpNewBlocks(Function* F) {
		// Put all newly created blocks into the function
		// Ref.: https://stackoverflow.com/questions/61181446/how-to-build-a-empty-basicblock-and-insert-a-instruction-in-the-front
		for(auto &edge : edges) {
			EdgeInfo* edgeinfo = &(edgemap[edge]);
			BasicBlock* i = edgeinfo->start;
			BasicBlock* j = edgeinfo->end;

			if (!(edgeinfo->InsertBlock))
				continue;
			// Set function parent and upstream node
			BasicBlock* newBlock = edgeinfo->InsertBlock;
			newBlock->insertInto(F, i);

			// Set descendant
			Instruction *terminator = i->getTerminator();
			int n = terminator->getNumSuccessors();
			for(unsigned edge_num=0; edge_num<n; ++edge_num) {
				if (terminator->getSuccessor(edge_num)==j) {
					terminator->setSuccessor(edge_num, newBlock);
					break;
				}
			}
			// Add terminator instruction (BranchInst) into the end ot fhe new block
			IRBuilder<> builder(newBlock);
			builder.CreateBr(j);
		}
	}

	void codeMotion(Function* F) {
		rewriteInsert(F);
		rewriteDelete(F);
		cleanUpNewBlocks(F);
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