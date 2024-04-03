//
// C++ Implementation: bddDump
//
// Description: 
//  Tool class for dumping BDDs to a nice .DOT file
//
// Author: Ruediger Ehlers <ehlers@grace>, (C) 2008
//

#include "BF.h"
#include "bddDump.h"
#include <vector>
#include <fstream>
#include <algorithm>
#undef fail
#define MAX_NODES_GRAPH 300
using namespace std;

/**
 Internal class for "MyDumpDot"
 */
class MyDumpDotNode {
private:	
	BF succF;
	BF succT;
	
	int succFlevel;
	int succFnr;
	int succTlevel;
	int succTnr;
	
public:
	BF getSuccF() { return succF; }
	BF getSuccT() { return succT; }
	int getSuccFlevel() { return succFlevel; }
	int getSuccFnr() { return succFnr; }
	int getSuccTlevel() { return succTlevel; }
	int getSuccTnr() { return succTnr; }
	
	MyDumpDotNode(const BF &_succF, const BF &_succT, const int _succFlevel, const int _succFnr, const int _succTlevel, const int _succTnr) : succF(_succF), succT(_succT), succFlevel(_succFlevel), succFnr(_succFnr), succTlevel(_succTlevel), succTnr(_succTnr) {};
		
};

/**
 Internal class for "MyDumpDot"
 */
class RecurseContext {
public:
	std::vector<unsigned int> &vars;
	std::vector<std::vector< MyDumpDotNode > > &nodes;
	const VariableInfoContainer &io;
	unsigned int nodesSoFar;
	
	RecurseContext(std::vector<unsigned int> &_vars, std::vector<std::vector< MyDumpDotNode > > &_nodes, const VariableInfoContainer &_io) : vars(_vars), nodes(_nodes), io(_io), nodesSoFar(0) {};
};

/**
 * Internal function for BDD dumping
 */
std::pair<int,unsigned int> BDD_newDumpDotRecurse(const BF &bdd, int level, RecurseContext &rc) {
	
        const BFManager *cudd = bdd.manager();
	if (rc.nodesSoFar>MAX_NODES_GRAPH) return std::pair<int,unsigned int>(-1,0);
	
	// Constant nodes?
    if (bdd==cudd->constantFalse()) return std::pair<int,unsigned int>(-1,0);
    if (bdd==cudd->constantTrue()) return std::pair<int,unsigned int>(-1,1);
	
	// int index = bdd.NodeReadIndex();
	if (level==(int)(rc.vars.size())) {
		#ifdef USE_BDD
		int index = bdd.readNodeIndex();
		std::ostringstream errorMsg;
		errorMsg << "MyDumpDot: Variable List was incomplete. Variable missing (" << index << "): " << rc.io.getVariableName(index);
                std::cerr << errorMsg.str() << std::endl;
		throw BFDumpDotException(errorMsg.str());
		#else
		throw BFDumpDotException("MyDumpDot: Variable List was incomplete. Variable missing (unknown);");
		#endif
	}
	
	// While not dependent on this var skip to next one
	BF currentVar;
	BF zeroBranch;
	BF oneBranch;
	bool depends = false;
	
	while ((!depends) && (level<(int)(rc.vars.size()))) {
		currentVar = rc.io.getVariableBF(rc.vars[level]);
		
		BF cube[1];
		int phase[1];
		phase[0] = 1;
		cube[0] = currentVar;
		
		zeroBranch = bdd & (!currentVar);
		zeroBranch = zeroBranch.ExistAbstract( cudd->computeCube(cube,phase,1));
		oneBranch = bdd & (currentVar);
		oneBranch = oneBranch.ExistAbstract( cudd->computeCube(cube,phase,1));
				
		if (oneBranch==zeroBranch) {
			level++;
		} else {
			depends = true;
		}
		
	}
		
	if (level==(int)(rc.vars.size())) {
		#ifdef USE_BDD
		int index = bdd.readNodeIndex();
		std::ostringstream errorMsg;
		errorMsg << "MyDumpDot: Variable List was incomplete. Variable missing (" << index << "): " << rc.io.getVariableName(index);
                std::cerr << errorMsg.str() << std::endl;
		throw BFDumpDotException(errorMsg.str());
		#else
		throw BFDumpDotException("MyDumpDot: Variable List was incomplete. Variable missing (unknown)");
		#endif
	}
		
	// Search for a suitable node
	for (unsigned int i=0;i<rc.nodes[level].size();i++) {
		MyDumpDotNode &current = rc.nodes[level][i];
		if ((current.getSuccF()==zeroBranch) && (current.getSuccT()==oneBranch))
			return std::pair<int,unsigned int>(level,i);
	}
	
	// Else: Make suitable node
	std::pair<int,unsigned int> continueZero = BDD_newDumpDotRecurse(zeroBranch, level+1, rc);
	std::pair<int,unsigned int> continueOne = BDD_newDumpDotRecurse(oneBranch, level+1, rc);
	rc.nodes[level].push_back(MyDumpDotNode(zeroBranch,oneBranch,continueZero.first,continueZero.second,continueOne.first,continueOne.second));
	rc.nodesSoFar++;
	return std::pair<int,unsigned int>(level,rc.nodes[level].size()-1);
}


/**
 * Dumps a BDD to a file for rendering with DOT
 *
 * Uses a custom variable ordering and "manual" dumping without "negation" edges
 */
void BF_newDumpDot(const VariableInfoContainer &cont, const BF &b, const char* varOrder, const std::string filename)
{
	        

    // Use NULL as varOrder to just use everything in the list
    std::string allVars;
    if (varOrder==NULL) {
        std::ostringstream os;
        std::vector<string> types;
        cont.getVariableTypes(types);
        for (std::vector<string>::const_iterator it = types.begin();it!=types.end();it++) {
            if (os.str().length()>0) os << " ";
            os << *it;
        }
        allVars = os.str();
        varOrder = allVars.c_str();
    }

        // Decoding Variable order
	std::istringstream order(varOrder);
	std::vector<unsigned int> vars;
	while (!order.eof()) {
		std::string part;
		order >> part;
		std::vector<unsigned int> newVars;
		cont.getVariableNumbersOfType(part,newVars);
		for (unsigned int i=0;i<newVars.size();i++) {
			
			std::vector<unsigned int>::iterator first_previous_usage;
			first_previous_usage = std::find(vars.begin(),vars.end(),newVars[i]);
			if (first_previous_usage != vars.end()) {
                // A variable occurs twice!
				throw BFDumpDotException(__FILE__,__LINE__);
			}
			
			vars.push_back(newVars[i]);
			//std::cout << "bddDump Variable: " << newVars[i] << std::endl;
		}
	}
	if (order.fail()) throw BFDumpDotException("Illegal variable order.");
	
	// Process the nodes
	// This is done by pushing a node downwards whenever it is independent of the current variable.
	std::vector<std::vector< MyDumpDotNode > > nodes;
	for (unsigned int i=0;i<vars.size();i++)
		nodes.push_back(std::vector<MyDumpDotNode>());
	RecurseContext context(vars,nodes,cont);
	// Process recursively
	BDD_newDumpDotRecurse(b,0,context);
		
        // Opening output file
	std::ofstream dumpFile(filename.c_str());
	
	if (context.nodesSoFar<=MAX_NODES_GRAPH) {
	
		// Preface
		dumpFile << "digraph \"DD\" { size = \"8,8\" \n  center = true; " << std::endl;
		
		// Start with variable order
		dumpFile << "edge [dir = none];\n"
			<< "{ node [shape = plaintext];\n"
			<< "  edge [style = invis];\n"
			<< " \"CONST NODES\" [style = invis];\n";
			
		std::vector<string> localVarNames;
		for (unsigned int i=0;i<vars.size();i++) {
			if (nodes[i].size()>0) {
				unsigned int var = vars[i];
				std::ostringstream thisOne;
                                std::string varName = cont.getVariableName(var);
                                std::replace(varName.begin(), varName.end(), '\"', '\'');
                                thisOne << "\"" << varName << "-";
				thisOne << " (" << var << ")\"";
				localVarNames.push_back(thisOne.str());
				dumpFile << thisOne.str();
				dumpFile << " -> ";
			} else {
				localVarNames.push_back("--INVALID--");
			}
		}
		dumpFile << "\"CONST NODES\"\n}\n";
		
		// Print the normal nodes
		for (unsigned int i=0;i<vars.size();i++) {
			if (nodes[i].size()>0) {
				dumpFile << "{ rank = same; " << localVarNames[i] << "; ";
				std::ostringstream thisOne;
				for (unsigned int j=0;j<nodes[i].size();j++) {
					thisOne << " \"" << i << "_" << j << "\"; "; 
				}
				dumpFile << thisOne.str() << "\n}\n";
			}
		}
		// Print the const nodes
		dumpFile << "{ rank = same; \"CONST NODES\";" << std::endl;
		{
                        BFManager const *cudd = b.manager();
                        if (b==cudd->constantFalse())
				dumpFile << "{ node [shape = box]; \"0\"; }}";
			else
				dumpFile << "{ node [shape = box]; \"1\"; }}";
		}
        dumpFile << "\n";
		
		// Print the Connections
		for (unsigned int i=0;i<vars.size();i++) {
			if (nodes[i].size()>0) {
				for (unsigned int j=0;j<nodes[i].size();j++) {
					std::ostringstream thisOne;
					
					// ELSE (But no zero-Transitions)
					if ((nodes[i][j].getSuccFlevel()!=-1) || (nodes[i][j].getSuccFnr()!=0)) {
						thisOne << " \"" << i << "_" << j << "\" ->";
						if (nodes[i][j].getSuccFlevel()==-1) {
							if (nodes[i][j].getSuccFnr()==0) thisOne << "\"0\"";
							else thisOne << "\"1\"";
						} else {
							thisOne << " \"" << nodes[i][j].getSuccFlevel() << "_" << nodes[i][j].getSuccFnr() << "\"";
						}
						thisOne << "[color=red];\n";
					}
					
					// IF
					if ((nodes[i][j].getSuccTlevel()!=-1) || (nodes[i][j].getSuccTnr()!=0)) { 
						thisOne << " \"" << i << "_" << j << "\" ->";
						if (nodes[i][j].getSuccTlevel()==-1) {
							if (nodes[i][j].getSuccTnr()==0) thisOne << "\"0\"";
							else thisOne << "\"1\"";
						} else {
							thisOne << " \"" << nodes[i][j].getSuccTlevel() << "_" << nodes[i][j].getSuccTnr() << "\"";
						}
						thisOne << "[color=blue,style=bold,dir=forward];\n";
					}
					
					dumpFile << thisOne.str();
				}
			}
		}
		dumpFile << "\n}\n";
	} else {
		dumpFile << "digraph \"DD\" { \n  \"Graph is too big\"\n}\n";		
	}
		
	dumpFile.close();
	if (dumpFile.fail()) throw BFDumpDotException("MyDotDump: Writing to output file "+filename+" failed.");
	
}

