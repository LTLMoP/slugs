#ifndef __EXTENSION_COMPUTE_INVARIANTS_HPP
#define __EXTENSION_COMPUTE_INVARIANTS_HPP

#include "gr1context.hpp"
#include <string>
#include <boost/tuple/tuple.hpp>
#include <boost/tuple/tuple_comparison.hpp>
#include <functional>
#include <random>
#include "subprocess.hpp"

#ifdef CUDD
#include <cuddInt.h>
#endif

/**
 * A class for computing invariants implied by the maximally permissive strategy (and probably later a bit more)
 */
template<class T> class XComputeInvariants : public T {
protected:

    using T::initSys;
    using T::initEnv;
    using T::safetyEnv;
    using T::safetySys;
    using T::lineNumberCurrentlyRead;
    using T::addVariable;
    using T::parseBooleanFormula;
    using T::livenessAssumptions;
    using T::livenessGuarantees;
    using T::mgr;
    using T::variables;
    using T::variableNames;
    using T::varVectorPre;
    using T::varVectorPost;
    using T::varCubePre;
    using T::varCubePost;
    using T::varCubePostInput;
    using T::varCubePostOutput;
    using T::varCubePreInput;
    using T::varCubePreOutput;
    using T::computeWinningPositions;
    using T::winningPositions;

    std::string satSolver;
    int nofInvariants;

    XComputeInvariants<T>(std::list<std::string> &filenames) : T(filenames) {
    }

    void init(std::list<std::string> &filenames) {
        T::init(filenames);

        if (filenames.size()<2) {
            throw SlugsException(false,"Error: Need file name of SAT solver and number of invariants to analyze invariants.");
        }

        satSolver = filenames.front();
        filenames.pop_front();
        std::cerr << "Using LP Solver: " << satSolver << std::endl;

        std::istringstream is(filenames.front());
        filenames.pop_front();
        is >> nofInvariants;
        if (is.fail()) throw SlugsException(false, "Error: Could not parse the number of invariants.");

    }

    /** Execute the analysis */
    void execute() {

        // To make the analysis of reachable positions precise enough, make safetySys
        // Stronger to avoid states with no outgoing transition *before* performing
        // realizability checking
        // safetySys &= safetySys.ExistAbstract(varCubePost).SwapVariables(varVectorPre,varVectorPost);

#ifdef USE_CUDD

        // 1. Perform realizability checking
        computeWinningPositions();
#ifndef NDEBUG
        BF_newDumpDot(*this,winningPositions,NULL,"/tmp/winningpositions.dot");
#endif

        // Compute states that are reachable when assumptions and guarantees are always satisfied.
        BF reachable = initEnv & initSys;
        BF_newDumpDot(*this,reachable,NULL,"/tmp/init.dot");
        BF oldReachable = mgr.constantFalse();
        while (reachable!=oldReachable) {
            oldReachable = reachable;
            reachable |= (safetyEnv & safetySys & reachable).ExistAbstract(varCubePre).SwapVariables(varVectorPre,varVectorPost);
            //BF_newDumpDot(*this,reachable,NULL,"/tmp/currentreachable.dot");
        }

        // Compute which states need to be covered
        //BF statesReachingTransitions = (safetyEnv & safetySys).ExistAbstract(varCubePost);


        BF toBeCovered = /*statesReachingTransitions & */ reachable & !winningPositions;
#ifndef NDEBUG
        BF_newDumpDot(*this,toBeCovered,NULL,"/tmp/tobecoveredoverall.dot");
        BF_newDumpDot(*this,reachable,NULL,"/tmp/reachable.dot");
#endif

        // In the following, we do an analysis over the BDD structure. Disable variable
        // reordering so that the following variable list can be in the BDD order
        mgr.setAutomaticOptimisation(false);

        // Prepare encoding -- Get Support
        std::vector<unsigned int> relevantCUDDVars;
        std::vector<BF> relevantCUDDVarBFs;
        std::vector<std::string> relevantCUDDVarNames;
        std::vector<unsigned int> cuddIndexToRelevantVarNumberMapper(variables.size());

        // Destroy intemediate data structures eagerly.
        {

            std::set<int> varsInSupport;
            std::set<DdNode *> done;

            std::function<void(DdNode*)> getSupportRecurse;

            getSupportRecurse = [&varsInSupport,&done,&getSupportRecurse](DdNode *current) {
                if (Cudd_IsConstant(current)) return;
                current = Cudd_Regular(current);
                if (done.count(current)>0) return;
                done.insert(current);
                varsInSupport.insert(current->index);
                getSupportRecurse(Cudd_T(current));
                getSupportRecurse(Cudd_E(current));
            };
            getSupportRecurse(winningPositions.getCuddNode());
            getSupportRecurse(toBeCovered.getCuddNode());

            for (int varNoPermutation=0;varNoPermutation<mgr.getMgr()->size;varNoPermutation++) {
                int targetNum = Cudd_ReadInvPerm(mgr.getMgr(),varNoPermutation);
                std::cerr << "The " << varNoPermutation << "th variable in the order is: " << targetNum << std::endl;
                for (unsigned int varNo=0;varNo<variables.size();varNo++) {
                    int index = variables[varNo].getCuddNode()->index;
                    if (varsInSupport.count(index)>0) {
                        if (index==targetNum) {
                            cuddIndexToRelevantVarNumberMapper[index] = relevantCUDDVars.size();
                            relevantCUDDVars.push_back(index);
                            relevantCUDDVarNames.push_back(variableNames[targetNum]);
                            relevantCUDDVarBFs.push_back(variables[targetNum]);
                        }
                    }
                }
            }
        }

#ifndef NDEBUG
        std::cerr << "Relevant variables:\n";
        for (unsigned int i=0;i<relevantCUDDVarNames.size();i++) {
            std::cerr << "- " << relevantCUDDVarNames[i] << std::endl;
        }
#endif

        // Find variable values implying other variable values to
        // prevent tem "inflating" the constants in the linear programming instances
        std::list<std::pair<unsigned int, unsigned int> > variableImplications;
        for (unsigned int i=0;i<relevantCUDDVarNames.size();i++) {
            for (unsigned int j=i+1;j<relevantCUDDVarNames.size();j++) {
                if (i!=j) {
                    BF possibility = (relevantCUDDVarBFs[i] & relevantCUDDVarBFs[j]) & reachable;
                    if (possibility.isFalse()) {
#ifndef NDEBUG
                        std::cerr << "Impl: " << i << "," << j << std::endl;
#endif
                        variableImplications.push_back(std::pair<unsigned int, unsigned int>(i,j));
                    }
                }
            }
        }

        // Allocate negative example list
        std::vector<std::vector<bool> > negativeExamples;

        // std::cerr << "TEST: ARTIFICIAL NEGATIVE EXAMPLE\n";
        // negativeExamples.push_back({false,false});

        // Main solving loop -- run a SAT solver to find next candidate set of invariants with an
        // assignment of negative examples so far to invariants such that:
        // a) for each negative example, everything between the *chosen* invariant and the negative examples needs to be negative cases as well
        // b) ?????
        // At the end of each loop, check if all negative examples have been covered. For this:
        // -> compute something like the "down-closure" of the invariant within the bad states

        // Random number generator to randomize which negative countereaxmple to pick -- leads to sufficient diversity in the examples.
        std::mt19937 rng(123);

        while (true) {

            // Clause storage
            std::vector<std::vector<int> > clauses;

            // Allocate variables for invariant bases
            std::vector<int> startingVarsInvariantBases;
            int nofVarsSoFar = 0;
            for (int i=0;i<nofInvariants;i++) {
#ifndef NDEBUG
                //std::cerr << "Starting var invariant base " << i << ": " << nofVarsSoFar+1 << std::endl;
#endif
                startingVarsInvariantBases.push_back(nofVarsSoFar+1);
                nofVarsSoFar += relevantCUDDVars.size();
            }

            // Allocate variables for selecting for each negative example which invariant is the right one
            std::vector<int> startingVarsInvariantSelectorForNegativeExample;
            for (unsigned int i=0;i<negativeExamples.size();i++) {
#ifndef NDEBUG
                //std::cerr << "Selector for negative example " << i << ": " << nofVarsSoFar+1 << std::endl;
#endif
                startingVarsInvariantSelectorForNegativeExample.push_back(nofVarsSoFar+1);
                nofVarsSoFar += nofInvariants;
            }

            // Allocate variables for the active bases for each negative example
            std::vector<int> startingVarsActiveBasesForEachNegativeExample;
            for (unsigned int i=0;i<negativeExamples.size();i++) {
#ifndef NDEBUG
                //std::cerr << "Starting var for active base for negative example " << i << ": " << nofVarsSoFar+1 << std::endl;
#endif
                startingVarsActiveBasesForEachNegativeExample.push_back(nofVarsSoFar+1);
                nofVarsSoFar += relevantCUDDVars.size();
            }

            // Every negative example needs to be covered by an invariant base
            for (unsigned int i=0;i<negativeExamples.size();i++) {
                std::vector<int> clauseSelector;
                for (int j=0;j<nofInvariants;j++) {
                    clauseSelector.push_back(startingVarsInvariantSelectorForNegativeExample[i]+j);
                }
                clauses.push_back(clauseSelector);
            }

            // Encode base selection
            for (unsigned int i=0;i<negativeExamples.size();i++) {
                for (int j=0;j<nofInvariants;j++) {
                    for (int k=0;k<static_cast<int>(relevantCUDDVars.size());k++) {
                        clauses.push_back({-1*startingVarsInvariantSelectorForNegativeExample[i]-j,-1*startingVarsActiveBasesForEachNegativeExample[i]-k,startingVarsInvariantBases[j]+k});
                        clauses.push_back({-1*startingVarsInvariantSelectorForNegativeExample[i]-j,startingVarsActiveBasesForEachNegativeExample[i]+k,-1*startingVarsInvariantBases[j]-k});
                    }
                }
            }

            // Now encode that everything between the negative example and the base needs to map to 0 in the BDD
            DdNode *one = Cudd_ReadOne(toBeCovered.manager()->getMgr());
            DdNode *zero = Cudd_Not(one);

            for (unsigned int negativeExample=0;negativeExample<negativeExamples.size();negativeExample++) {

                std::map<std::pair<DdNode*,unsigned int>,int> nodeToVarMapper;
                nodeToVarMapper[std::pair<DdNode*,unsigned int>(winningPositions.getCuddNode(),0)] = ++nofVarsSoFar;
                clauses.push_back({nofVarsSoFar});
                std::set<std::pair<DdNode*,unsigned int>> doneList;
                doneList.insert(std::pair<DdNode*,unsigned int>(winningPositions.getCuddNode(),0));
                std::list<std::pair<DdNode*,unsigned int>> todoList;
                todoList.push_back(std::pair<DdNode*,unsigned int>(winningPositions.getCuddNode(),0));
                // std::cerr << "digraph {\n\"n0\";\n";
                while (todoList.size()!=0) {
                    std::pair<DdNode*,unsigned int> thisNodeAndLevel = todoList.front();
                    todoList.pop_front();
                    int currentNo = nodeToVarMapper.at(thisNodeAndLevel);

                    if (Cudd_IsConstant(thisNodeAndLevel.first) && (thisNodeAndLevel.second==relevantCUDDVars.size())) {
                        if (thisNodeAndLevel.first==one) {
                            clauses.push_back({-1*currentNo});
                            //std::cerr << "n" << currentNo << "[label=\"n" << currentNo << ",ONE\"];\n";
                        } else {
                            assert(thisNodeAndLevel.first==zero);
                        }
                    } else if (Cudd_IsConstant(thisNodeAndLevel.first) ||
                               (cuddIndexToRelevantVarNumberMapper[Cudd_Regular(thisNodeAndLevel.first)->index]!=thisNodeAndLevel.second)) {

                        /* Case: Skipping a variable */
                        std::pair<DdNode*,unsigned int> nextPair = thisNodeAndLevel;
                        nextPair.second++;
                        if (nextPair.second > relevantCUDDVarBFs.size()) {
                            throw "Internal error: Went too low in the hierarchy.";
                        }
                        int numNext;
                        if (doneList.count(nextPair)==0) {
                            numNext = ++nofVarsSoFar;
                            nodeToVarMapper[nextPair] = numNext;
                            doneList.insert(nextPair);
                            todoList.push_back(nextPair);
                        } else {
                            numNext = nodeToVarMapper[nextPair];
                        }

                        // Negative example the same as invariant base --> Follow only the negative example case.
                        // otherwise follow both cases!
                        clauses.push_back({-1*currentNo,numNext});

                    } else {
                        //std::cerr << "n" << currentNo << "[label=\"n" << currentNo << "," << thisNodeAndLevel.second << "\"];\n";
                        DdNode *t;
                        DdNode *e;
                        if (reinterpret_cast<size_t>(thisNodeAndLevel.first) & 1) {
                            t = Cudd_Not(Cudd_T(Cudd_Regular(thisNodeAndLevel.first)));
                            e = Cudd_Not(Cudd_E(Cudd_Regular(thisNodeAndLevel.first)));
                        } else {
                            t = Cudd_T(thisNodeAndLevel.first);
                            e = Cudd_E(thisNodeAndLevel.first);
                        }

                        for (int edge=0;edge<2;edge++) {
                            std::pair<DdNode*,unsigned int> nextPair((edge==0)?t:e,thisNodeAndLevel.second+1);

                            // Sanity check
                            if (!Cudd_IsConstant(nextPair.first)) {
                                int nextIndex = Cudd_Regular(nextPair.first)->index;
                                if (cuddIndexToRelevantVarNumberMapper[nextIndex]<nextPair.second) {
                                    int thisIndex = Cudd_Regular(thisNodeAndLevel.first)->index;
                                    std::cerr << "ThisLevel: " << thisIndex << std::endl;
                                    throw "Internal error: Skipped a level.";
                                }
                            }

                            int numNext;
                            if (doneList.count(nextPair)==0) {
                                numNext = ++nofVarsSoFar;
                                nodeToVarMapper[nextPair] = numNext;
                                doneList.insert(nextPair);
                                todoList.push_back(nextPair);
                            } else {
                                numNext = nodeToVarMapper[nextPair];
                            }

                            // Negative example the same as invariant base --> Follow only the negative example case.
                            // otherwise follow both cases!
                            if ((negativeExamples[negativeExample][thisNodeAndLevel.second]) ^ (edge==1)) {
                                // Take this one either way
                                clauses.push_back({-1*currentNo,numNext});
                            } else {
                                // Take this one conditionally
                                int conditionLiteral = (negativeExamples[negativeExample][thisNodeAndLevel.second]?1:-1)*(startingVarsActiveBasesForEachNegativeExample[negativeExample]+thisNodeAndLevel.second);
                                clauses.push_back({conditionLiteral,-1*currentNo,numNext});
                            }

                            //std::cerr << "n" << currentNo << "-> n" << numNext;
                            //if (edge==1) std::cerr << "[style=dashed];\n";
                            //else std::cerr << ";\n";
                        }

                    }
                }
                //std::cerr << "}\n";
            }


            // Run SAT solver
            // Start encoding
            subprocess::popen cmd(satSolver, {});
            std::ostream &cmdos = cmd.stdin();
            cmdos << "p cnf " << nofVarsSoFar << " " << clauses.size() << "\n";
            for (auto &it : clauses) {
                for (auto &it2 : it) {
                    cmdos << it2 << " ";
                }
                cmdos << "0\n";
            }

            // Finishing the encoding and reading the result.
            cmd.close(); // Closes only inStream

            std::ostringstream stdoutBuffer;
            stdoutBuffer << cmd.stdout().rdbuf();

            int retVal = cmd.wait();
            if (retVal==10) {
                // Satisfiable!
                // Read model
                std::istringstream is(stdoutBuffer.str());
                std::string currentline;
                std::unordered_set<int> model;
                while (std::getline(is,currentline)) {
                    //std::cerr << "Interpreting model line: " << currentline << std::endl;
                    if (currentline.substr(0,2)=="v ") {
                        // Read model
                        std::istringstream modelreader(currentline.substr(2,std::string::npos));
                        while (!(modelreader.fail())) {
                            int next;
                            modelreader >> next;
                            if (!modelreader.fail()) model.insert(next);
                        }
                    }
                }

#ifndef NDEBUG
                //std::cerr << "Model read: ";
                //for (auto it: model) std::cerr << it << " ";
                //std::cerr << "\n";
#endif

                // Interpreting the model
                std::vector<BF> invariants;
                for (int i=0;i<nofInvariants;i++) {
                    invariants.push_back(mgr.constantTrue());
                }
                for (unsigned int i=0;i<negativeExamples.size();i++) {
                    for (int j=0;j<nofInvariants;j++) {
                        if (model.count(startingVarsInvariantSelectorForNegativeExample[i]+j)>0) {
                            //std::cerr << "Negative example " << i << " is covered by invariant " << j << std::endl;

                            BF thisCase = mgr.constantTrue();
                            for (unsigned int k=0;k<relevantCUDDVars.size();k++) {
                                if (negativeExamples[i][k] == (model.count(startingVarsInvariantBases[j]+k)>0)) {
                                    thisCase &= (negativeExamples[i][k]?relevantCUDDVarBFs[k]:!relevantCUDDVarBFs[k]);
                                }
                            }
                            invariants[j] &= !thisCase;

                            //BF_newDumpDot(*this,invariants[j],NULL,"/tmp/thisCase.dot");
                            //throw 4;
                        }
                    }
                }

                BF allInvariantsTogether = mgr.constantTrue();
                for (auto it : invariants) allInvariantsTogether &= it;

                // Not check if we are done!
                if (!((!allInvariantsTogether & winningPositions).isFalse())) {
                    throw SlugsException(false,"Internal Error: illegal invariants computed.");
                }

                BF rest = allInvariantsTogether & toBeCovered;

                if (rest.isFalse()) {

                    std::cout << "Result: Found invariants!\n";
                    std::cout << "Number of invariants: " << nofInvariants << std::endl;
                    for (int i=0;i<nofInvariants;i++) {
                        std::cout << "- Invariant " << i << " with base: ";
                        for (unsigned int k=0;k<relevantCUDDVars.size();k++) {
                            std::cout << ((model.count(startingVarsInvariantBases[i]+k)>0)?"1":"0");
                        }
                        std::cout << "\n";
                        for (unsigned int j=0;j<negativeExamples.size();j++) {
                            if (model.count(startingVarsInvariantSelectorForNegativeExample[j]+i)>0) {
                                std::cout << "  - Example ";
                                for (auto it : negativeExamples[j]) {
                                    if (it) std::cout << "1"; else std::cout << "0";
                                }
                                std::cout << "\n";
                            }
                        }
                    }

                    // Generate and DOT-output optimizecd BDDs for the invariants
                    BF_newDumpDot(*this,allInvariantsTogether,NULL,"/tmp/allInvariantsTogether.dot");
                    for (int i=0;i<nofInvariants;i++) {
                        std::ostringstream filename;
                        filename << "/tmp/invariant" << i << ".dot";

                        // Iterative simplification cycles
                        BF oldsimplified = mgr.constantFalse();
                        BF simplified = invariants[i];
                        if (oldsimplified != simplified) {
                            oldsimplified = simplified;
                            simplified = simplified.optimizeRestrict(winningPositions | toBeCovered);
                            simplified = simplified.optimizeRestrict(reachable | toBeCovered);
                            //simplified = simplified.optimizeRestrict(reachable);
                            simplified = simplified.optimizeRestrict((winningPositions & reachable) | toBeCovered);
                        }
                        BF_newDumpDot(*this,simplified,NULL,filename.str());
                    }

                    return;
                }

                // Ok, so rest is not empty
                // Compute new negative exaple
                std::vector<bool> nextNegativeExample;
                for (unsigned int k=0;k<relevantCUDDVars.size();k++) {
                    // Which direction to prefer is random to make negative examples for uniform
                    if (rng() & 1) {
                        if ((rest & relevantCUDDVarBFs[k]).isFalse()) {
                            nextNegativeExample.push_back(false);
                            rest &= !relevantCUDDVarBFs[k];
                        } else {
                            nextNegativeExample.push_back(true);
                            rest &= relevantCUDDVarBFs[k];
                        }
                    } else {
                        if ((rest & !relevantCUDDVarBFs[k]).isFalse()) {
                            nextNegativeExample.push_back(true);
                            rest &= relevantCUDDVarBFs[k];
                        } else {
                            nextNegativeExample.push_back(false);
                            rest &= !relevantCUDDVarBFs[k];
                        }
                    }
                }

                std::cerr << "New negative example (no." << negativeExamples.size() << "): ";
                for (auto it : nextNegativeExample) {
                    if (it) std::cerr << "1"; else std::cerr << "0";
                }
                std::cerr << "\n";

                negativeExamples.push_back(nextNegativeExample);

            } else if (retVal==20) {
                // Unsatisfiable!
                std::cout << "Result: Cannot find " << nofInvariants << " covering the non-winning reachable states.\n";
                return;
            } else {
                std::ostringstream stderrBuffer;
                stderrBuffer << "(" << retVal << ")" << cmd.stderr().rdbuf();
                std::ostringstream error;
                error << stderrBuffer.str() << ", stdout: " << stdoutBuffer.str();
                std::cerr << "BufSiz:" << error.str().length() << std::endl;
                throw SlugsException(false,error.str());
            }


        }


#if 0

        // Enumerate the Invariants
        while (!(toBeCovered.isFalse())) {


            // Start encoding
            subprocess::popen cmd(lpSolver, {});

            // Optimization criterion
            std::ostream &cmdos = cmd.stdin();
            cmdos << "max:";
            for (unsigned int i=0;i<relevantCUDDVarNames.size();i++) {
                if (i>0) cmdos << " +";
                cmdos << " 1.0 w" << i;
            }
            cmdos << " - limit;\n";

            // Weight limits
            for (unsigned int i=0;i<relevantCUDDVarNames.size();i++) {
                cmdos << "1 w" << i << " <= 1;\n";
                cmdos << "-1 w" << i << " <= 1;\n";
            }
            cmdos << "-1 limit <= " << relevantCUDDVarNames.size() << ";\n";

            // Find new assignment that needs to be covered
            DdNode *assignmentToBeCovered = toBeCovered.getCuddNode();
            bool first = true;
            bool complemented = false;
            DdNode *one = Cudd_ReadOne(toBeCovered.manager()->getMgr());
            DdNode *zero = Cudd_Not(one);
            std::cerr << "Invariant needed because of: ";
            while (!(Cudd_IsConstant(assignmentToBeCovered))) {
                if (reinterpret_cast<size_t>(assignmentToBeCovered) & 1) {
                    complemented = !complemented;
                    assignmentToBeCovered = Cudd_Regular(assignmentToBeCovered);
                }
                if (complemented) {
                    if (Cudd_T(assignmentToBeCovered)==one) {
                        assignmentToBeCovered = Cudd_E(assignmentToBeCovered);
                        // Pick Else
                    } else {
                        // Pick Then
                        if (!first) cmdos << " + ";
                        std::cerr << cuddIndexToRelevantVarNumberMapper[assignmentToBeCovered->index] << " ";
                        cmdos << "1 w" << cuddIndexToRelevantVarNumberMapper[assignmentToBeCovered->index];
                        assignmentToBeCovered = Cudd_T(assignmentToBeCovered);
                        first = false;

                    }
                } else {
                    if (Cudd_T(assignmentToBeCovered)==zero) {
                        // Pick Else
                        assignmentToBeCovered = Cudd_E(assignmentToBeCovered);
                        std::cerr << "0";
                    } else {
                        // Pick Then
                        if (!first) cmdos << " + ";
                        std::cerr << cuddIndexToRelevantVarNumberMapper[assignmentToBeCovered->index] << " ";
                        cmdos << "1 w" << cuddIndexToRelevantVarNumberMapper[assignmentToBeCovered->index];
                        assignmentToBeCovered = Cudd_T(assignmentToBeCovered);
                        first = false;
                    }
                }
            }
            std::cerr << "\n";
            cmdos << " -1 limit >= 0.0001;\n";

            // Encode that everything that is a winning position needs to satisfy the linear inequality.
            std::map<std::pair<DdNode*,unsigned int>,int> winningNodeToMaxAccumulatedValueMapper;
            int nextNumWinningNodeToMaxAccumulatedValueMapper = 1;
            std::set<std::pair<DdNode*,unsigned int>> doneList;
            doneList.insert(std::pair<DdNode*,unsigned int>(winningPositions.getCuddNode(),0));
            std::list<std::pair<DdNode*,unsigned int>> todoList;
            todoList.push_back(std::pair<DdNode*,unsigned int>(winningPositions.getCuddNode(),0));
            winningNodeToMaxAccumulatedValueMapper[std::pair<DdNode*,unsigned int>(winningPositions.getCuddNode(),0)] = 0;
            cmdos << " 1 n0 >= 0;\n";
            std::cerr << "digraph {\n\"n0\";\n";
            while (todoList.size()!=0) {
                std::pair<DdNode*,unsigned int> thisNodeAndLevel = todoList.front();
                todoList.pop_front();
                int currentNo = winningNodeToMaxAccumulatedValueMapper.at(thisNodeAndLevel);

                if (Cudd_IsConstant(thisNodeAndLevel.first) && (thisNodeAndLevel.second==relevantCUDDVars.size())) {
                    if (thisNodeAndLevel.first==one) {
                        cmdos << "1 n" << currentNo << " -1 limit <= -0.001;\n"; // Need to satisfy
                        std::cerr << "n" << currentNo << "[label=\"n" << currentNo << ",ONE\"];\n";
                    } else {
                        assert(thisNodeAndLevel.first==zero);
                    }
                } else if (Cudd_IsConstant(thisNodeAndLevel.first) ||
                           (cuddIndexToRelevantVarNumberMapper[Cudd_Regular(thisNodeAndLevel.first)->index]!=thisNodeAndLevel.second)) {

                    /* Case: Skipping a variable */
                    std::pair<DdNode*,unsigned int> nextPair = thisNodeAndLevel;
                    nextPair.second++;
                    if (nextPair.second > relevantCUDDVarBFs.size()) {
                        throw "Internal error: Went too low in the hierarchy.";
                    }
                    int numNext;
                    if (doneList.count(nextPair)==0) {
                        numNext = nextNumWinningNodeToMaxAccumulatedValueMapper++;
                        winningNodeToMaxAccumulatedValueMapper[nextPair] = numNext;
                        doneList.insert(nextPair);
                        todoList.push_back(nextPair);
                        cmdos << "1 n" << numNext << " >= -" << relevantCUDDVarNames.size() << ";\n";
                    } else {
                        numNext = winningNodeToMaxAccumulatedValueMapper[nextPair];
                    }

                    // Virtual "t" and "e" edges. Unclear which case is worse.
                    //cmdos << " -1 n" << currentNo << " 1 w" << thisNodeAndLevel.second << " 1 n" << numNext << " >= 0;\n";
                    cmdos << " -1 n" << currentNo << " -1 w" << thisNodeAndLevel.second << " 1 n" << numNext << " >= 0;\n";
                    cmdos << " -1 n" << currentNo << " 1 n" << numNext << " >= 0;\n";


                } else {
                    std::cerr << "n" << currentNo << "[label=\"n" << currentNo << "," << thisNodeAndLevel.second << "\"];\n";
                    DdNode *t;
                    DdNode *e;
                    if (reinterpret_cast<size_t>(thisNodeAndLevel.first) & 1) {
                        t = Cudd_Not(Cudd_T(Cudd_Regular(thisNodeAndLevel.first)));
                        e = Cudd_Not(Cudd_E(Cudd_Regular(thisNodeAndLevel.first)));
                    } else {
                        t = Cudd_T(thisNodeAndLevel.first);
                        e = Cudd_E(thisNodeAndLevel.first);
                    }

                    for (int edge=0;edge<2;edge++) {
                        std::pair<DdNode*,unsigned int> nextPair((edge==0)?t:e,thisNodeAndLevel.second+1);

                        // Sanity check
                        if (!Cudd_IsConstant(nextPair.first)) {
                            int nextIndex = Cudd_Regular(nextPair.first)->index;
                            if (cuddIndexToRelevantVarNumberMapper[nextIndex]<nextPair.second) {
                                int thisIndex = Cudd_Regular(thisNodeAndLevel.first)->index;
                                std::cerr << "ThisLevel: " << thisIndex << std::endl;
                                throw "Internal error: Skipped a level.";
                            }
                        }

                        int numNext;
                        if (doneList.count(nextPair)==0) {
                            numNext = nextNumWinningNodeToMaxAccumulatedValueMapper++;
                            winningNodeToMaxAccumulatedValueMapper[nextPair] = numNext;
                            doneList.insert(nextPair);
                            todoList.push_back(nextPair);
                            cmdos << "1 n" << numNext << " >= -" << relevantCUDDVarNames.size() << ";\n";
                        } else {
                            numNext = winningNodeToMaxAccumulatedValueMapper[nextPair];
                        }
                        cmdos << "1 n" << numNext;

                        // Consider skipped indices as well.
                        if (edge==0) cmdos << " -1 w" << thisNodeAndLevel.second;
                        cmdos << " -1 n" << currentNo << " >= 0;\n"; // Maximum is sufficient

                        std::cerr << "n" << currentNo << "-> n" << numNext;
                        if (edge==1) std::cerr << "[style=dashed];\n";
                        else std::cerr << ";\n";
                    }

                }
            }
            std::cerr << "}\n";
            /** Debug-Printer for specific example*/
            std::cerr << "Field:\n";
            for (unsigned int y=0;y<8;y++) {
                for (unsigned int x=0;x<32;x++) {
                    BF dis = winningPositions;
                    for (unsigned int bit=0;bit<5;bit++) {
                        dis &= (x & (1<<bit))?relevantCUDDVarBFs[bit]:!relevantCUDDVarBFs[bit];
                    }
                    for (unsigned int bit=0;bit<3;bit++) {
                        dis &= (y & (1<<bit))?relevantCUDDVarBFs[bit+5]:!relevantCUDDVarBFs[bit+5];
                    }
                    if (dis.isFalse()) std::cerr << "."; else std::cerr << "*";
                }
                std::cerr << "\n";
            }

            // Implement pairwise implications
            for (auto it : variableImplications) {
                cmdos << "1 w" << it.first << " 1 w" << it.second << " <= 1;\n";
            }


            // Finishing the encoding and reading the result.
            cmd.close(); // Closes only inStream

            std::ostringstream stdoutBuffer;
            stdoutBuffer << cmd.stdout().rdbuf();

            int retVal = cmd.wait();
            if (retVal!=0) {
                std::ostringstream stderrBuffer;
                stderrBuffer << cmd.stderr().rdbuf();
                std::ostringstream error;
                error << stderrBuffer.str() << ", stdout: " << stdoutBuffer.str();
                std::cerr << "BufSiz:" << error.str().length() << std::endl;
                throw SlugsException(false,error.str());
            }

            // Ok, so we got a result. Let's parse
            std::istringstream is(stdoutBuffer.str());
            std::string thisLine;
            bool gotModel = false;
            std::vector<double> linearInequality(relevantCUDDVars.size());
            double limitForLinearInequality;
            while (std::getline(is,thisLine)) {
                std::cerr << thisLine;
                if (thisLine=="Actual values of the variables:") gotModel = true;
                else if (gotModel) {
                    std::istringstream is2(thisLine);
                    char f;
                    is2 >> f;
                    if (!is2.fail()) {
                        if (f=='w') {
                            int numVar;
                            is2 >> numVar;
                            if (is2.fail()) throw "Error: couldn't parse number after 'w'.";

                            double val;
                            is2 >> val;
                            if (is2.fail()) throw "Error: couldn't parse double value after 'w'.";
                            std::cerr << "\nCult: " << numVar << " " << val << std::endl;
                            linearInequality[numVar] = val;
                        } else if (f=='l') {
                            std::string rest;
                            is2 >> rest;
                            if (is2.fail()) throw "Error: couldn't parse 'number after 'limit'.";
                            if (rest=="imit") {
                                is2 >> limitForLinearInequality;
                                if (is2.fail()) throw "Error: couldn't parse double limit";
                                std::cerr << "\nCult-Limit: " << limitForLinearInequality << std::endl;
                            }
                        }
                    }
                }
            }
            if (!gotModel) throw SlugsException(false,"Could not compute LP model. Numerical inaccuracies are the likely problem.");

            // Compute BDD for the linear inequality
            std::map<double,BF> valueSoFarToValuationsMapper;
            std::map<double,BF> valueSoFarToValuationsMapperNext;
            valueSoFarToValuationsMapper[0.0] = winningPositions.manager()->constantTrue();
            for (unsigned int i = 0;i<relevantCUDDVars.size();i++) {
                valueSoFarToValuationsMapperNext.clear();
                for (auto &it : valueSoFarToValuationsMapper) {
                    // False case
                    if (valueSoFarToValuationsMapperNext.count(it.first)==0) {
                        valueSoFarToValuationsMapperNext[it.first] = it.second & !relevantCUDDVarBFs[i];
                    } else {
                        valueSoFarToValuationsMapperNext[it.first] |= it.second & !relevantCUDDVarBFs[i];
                    }

                    double targetCosts = it.first+linearInequality[i];
                    if (valueSoFarToValuationsMapperNext.count(targetCosts)==0) {
                        valueSoFarToValuationsMapperNext[targetCosts] = it.second & relevantCUDDVarBFs[i];
                    } else {
                        valueSoFarToValuationsMapperNext[targetCosts] |= it.second & relevantCUDDVarBFs[i];
                    }
                }
                valueSoFarToValuationsMapper = valueSoFarToValuationsMapperNext;

                std::cerr << "Level " << i << ":";
                for (auto &it : valueSoFarToValuationsMapper) {
                    std::cerr << " " << it.first;
                    if (it.second.isFalse()) std::cerr << "(false)";
                }
                std::cerr << "\n";

            }

            // LIMIT....
            BF stillallowed = winningPositions.manager()->constantFalse();
            for (auto &it : valueSoFarToValuationsMapper) {
                std::cerr << "Sum of Values: " << it.first << std::endl;
                if (it.first<=limitForLinearInequality) {
                    stillallowed |= it.second;

                }
                /*
                std::ostringstream filename;
                filename << "/tmp/stillallowed" << it.first << ".dot";
                BF_newDumpDot(*this,it.second,NULL,filename.str());*/
            }

            BF_newDumpDot(*this,(winningPositions & !stillallowed),NULL,"/tmp/wrongcases.dot");
            BF_newDumpDot(*this,(stillallowed),NULL,"/tmp/stillallowed.dot");

            if (!((winningPositions & !stillallowed).isFalse())) throw "Erroneus encoded result.";

            if ((toBeCovered & !stillallowed).isFalse()) throw "Error: Did not remove any new element from the set of states to be covered.";

            BF_newDumpDot(*this,toBeCovered,NULL,"/tmp/coveredBefore.dot");
            toBeCovered &= stillallowed;
            BF_newDumpDot(*this,toBeCovered,NULL,"/tmp/coveredAfter.dot");


            // Print invariant
            std::cout << "Invariant:";
            for (unsigned int i=0;i<relevantCUDDVarNames.size();i++) {
                // Not yet here: Robustification of the constants
                if (linearInequality[i]!=0.0) {
                    std::cout << " " << linearInequality[i] << "*" << relevantCUDDVarNames[i];
                }
            }
            std::cout << " <= " << limitForLinearInequality << std::endl;
            std::cout.flush();

        }
#endif



#else
        std::cerr << "This plugin is only supported for a CUDD backend.\n";
#endif


    }




public:
    static GR1Context* makeInstance(std::list<std::string> &filenames) {
        return new XComputeInvariants<T>(filenames);
    }
};


#endif
