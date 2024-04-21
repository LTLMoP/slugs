#ifndef __EXTENSION_COMPUTE_INVARIANTS_HPP
#define __EXTENSION_COMPUTE_INVARIANTS_HPP

#include "gr1context.hpp"
#include <string>
#include <boost/tuple/tuple.hpp>
#include <boost/tuple/tuple_comparison.hpp>
#include <functional>
#include <unordered_map>
#include <random>
#include <fstream>
#include <algorithm>
#include "cadical.hpp"

#ifdef CUDD
#include <cuddInt.h>
#endif

class hashDdNodeUIntPair {
public:
    std::size_t operator () (const std::pair<DdNode*,unsigned int> &p) const {
        auto h1 = std::hash<size_t>{}((size_t)(p.first));
        auto h2 = std::hash<unsigned int>{}(p.second);

        // Mainly for demonstration purposes, i.e. works but is overly simple
        // In the real world, use sth. like boost.hash_combine
        return h1 ^ h2;
    }
};


/**
 * A class for computing invariants implied by the maximally permissive strategy (and probably later a bit more)
 */
template<class T, bool supportForDontCare> class XComputeInvariants : public T {
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
    using T::getVariableNumbersOfType;
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
    std::vector<std::vector<int> > negativeExamples; // +1: TRUE, -1: FALSE, 0: don't care

    XComputeInvariants<T,supportForDontCare>(std::list<std::string> &filenames) : T(filenames) {
    }

    void init(std::list<std::string> &filenames) {
        T::init(filenames);

        if (filenames.size()<2) {
            throw SlugsException(false,"Error: Need file name of SAT solver and number of invariants to analyze invariants.");
        }

        satSolver = filenames.front();
        filenames.pop_front();
        std::cerr << "Using SAT Solver: " << satSolver << std::endl;

        std::istringstream is(filenames.front());
        filenames.pop_front();
        is >> nofInvariants;
        if (is.fail()) throw SlugsException(false, "Error: Could not parse the number of invariants.");

        // Parse prepared negative examples
        while (filenames.size()>0) {
            std::vector<int> thisExample;
            std::string thisOne = filenames.front();
            filenames.pop_front();
            std::cerr << "Data: " << thisOne << std::endl;
            for (unsigned int i=0;i<thisOne.size();i++) {
                if (thisOne[i]=='?') {
                    thisExample.push_back(0);
                } else if (thisOne[i]=='1') {
                    thisExample.push_back(1);
                } else if (thisOne[i]=='0') {
                    thisExample.push_back(-1);
                } else {
                    throw SlugsException(false, "Error: Some pre-provided negative example does not only consider of the letters 01?");
                }
            }
            negativeExamples.push_back(thisExample);
        }


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

        mgr.setAutomaticOptimisation(false);


        //BF reachableOldStyle; // = initEnv & initSys & winningPositions;
        //BF_newDumpDot(*this,reachableOldStyle,NULL,"/tmp/initOld.dot");
        //BF oldReachable = mgr.constantFalse();
        /*while (reachableOldStyle!=oldReachable) {
            oldReachable = reachableOldStyle;
            reachableOldStyle |= (safetyEnv & safetySys & reachableOldStyle & winningPositions).ExistAbstract(varCubePre).SwapVariables(varVectorPre,varVectorPost);
            //BF_newDumpDot(*this,reachable,NULL,"/tmp/currentreachable.dot");
        }*/


        // Compute states that are reachable when assumptions and guarantees are always satisfied.
        // ...both by going only through winning positions and not
        BF reachableAndWinning = initEnv & initSys & winningPositions;
        //BF_newDumpDot(*this,reachableAndWinning,NULL,"/tmp/init.dot");
        BF oldReachable = mgr.constantFalse();
        while (reachableAndWinning!=oldReachable) {
            oldReachable = reachableAndWinning;
            reachableAndWinning |= (safetyEnv & safetySys & reachableAndWinning).ExistAbstract(varCubePre).SwapVariables(varVectorPre,varVectorPost) & winningPositions;
            //BF_newDumpDot(*this,reachable,NULL,"/tmp/currentreachable.dot");
        }
        BF reachableAndWinningOrFirstNonWinningStateReached = (safetyEnv & safetySys & reachableAndWinning).ExistAbstract(varCubePre).SwapVariables(varVectorPre,varVectorPost) | reachableAndWinning;

        //reachableOldStyle = reachableAndWinningOrFirstNonWinningStateReached;

        // Compute which states need to be covered
        //BF statesReachingTransitions = (safetyEnv & safetySys).ExistAbstract(varCubePost);

        // computing TildeB
        BF tildeB = (!((safetyEnv & safetySys & reachableAndWinning).ExistAbstract(varCubePre).SwapVariables(varVectorPre,varVectorPost))) | reachableAndWinning;

#ifndef NDEBUG
        BF_newDumpDot(*this,!tildeB,NULL,"/tmp/tobecoveredoverall.dot");
        BF_newDumpDot(*this,reachableAndWinning,NULL,"/tmp/reachableAndWinning.dot");
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
            getSupportRecurse(reachableAndWinning.getCuddNode());
            getSupportRecurse(tildeB.getCuddNode());

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

        // Compute the order of the variable names
        std::vector<int> bfVariableNameOrder;
        for (unsigned int i=0;i<relevantCUDDVarNames.size();i++) bfVariableNameOrder.push_back(i);
        std::sort(bfVariableNameOrder.begin(), bfVariableNameOrder.end(),
             [&](const int& left, const int& right) {
                 return (relevantCUDDVarNames[left] < relevantCUDDVarNames[right]);
             });
        /*std::vector<int> bfVariableNameOrderInverse(bfVariableNameOrder.size());
        for (unsigned int i=0;i<bfVariableNameOrder.size();i++) {
            bfVariableNameOrderInverse[bfVariableNameOrder[i]] = i;
        }*/


        // Get the negative examples into the right order
        // Check if all negative examples given already have the right size
        for (unsigned int nofNE=0;nofNE<negativeExamples.size();nofNE++) {
            std::vector<int> reversed(negativeExamples[nofNE].size());
            for (unsigned int i=0;i<negativeExamples[nofNE].size();i++) {
                reversed[bfVariableNameOrder[i]] = negativeExamples[nofNE][i];
            }
            negativeExamples[nofNE] = reversed;
            if (reversed.size()!=relevantCUDDVarBFs.size()) {
                std::cerr << "example size: " << reversed.size() << " wanted: " << relevantCUDDVarBFs.size() << "\n";
                throw SlugsException(false,"Some of the negative examples pre-provided do not have the correct size!");
            }
        }



        std::cerr << "Variable permutation:";
        for (auto it : bfVariableNameOrder) std::cerr << " " << it;
        std::cerr << "\n";
        /*std::cerr << "Inverse Variable permutation:";
        for (auto it : bfVariableNameOrderInverse) std::cerr << " " << it;
        std::cerr << "\n";*/


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

        // Incremental solving
        std::vector<int> startingVarsInvariantBases;
        std::vector<int> startingVarsInvariantSelectorForNegativeExample;
        std::vector<int> startingVarsActiveBasesForEachNegativeExample;
        int nofVarsSoFar = 0;


        // Allocate SAT Solver
        CaDiCaL::Solver solver;
        unsigned int nofNegativeExamplesProcessedSoFar = 0;

        // Allocate variables for invariant bases
        for (int i=0;i<nofInvariants;i++) {
#ifndef NDEBUG \
    //std::cerr << "Starting var invariant base " << i << ": " << nofVarsSoFar+1 << std::endl;
#endif
            startingVarsInvariantBases.push_back(nofVarsSoFar+1);
            nofVarsSoFar += relevantCUDDVars.size();
        }

        // Symmetry breaking: Invariant bases must be lexicographically ordered
        for (int i=0;i<nofInvariants-1;i++) {
            int startingVarDiff = nofVarsSoFar+1;
            nofVarsSoFar += relevantCUDDVars.size();

            // Start
            solver.clause(startingVarsInvariantBases[i],startingVarsInvariantBases[i+1],-1*startingVarDiff);
            solver.clause(-1*startingVarsInvariantBases[i],-1*startingVarsInvariantBases[i+1],-1*startingVarDiff);
            // Continue
            for (unsigned int j=0;j<relevantCUDDVars.size()-1;j++) {
                solver.clause(startingVarDiff+j,startingVarsInvariantBases[i]+j+1,startingVarsInvariantBases[i+1]+j+1,-1*startingVarDiff-j-1);
                solver.clause(startingVarDiff+j,-1*startingVarsInvariantBases[i]-j-1,-1*startingVarsInvariantBases[i+1]-j-1,-1*startingVarDiff-j-1);
            }

            // If no diff before, lexicographical
            // Start
            solver.clause(-1*startingVarsInvariantBases[i],startingVarsInvariantBases[i+1]);
            // Continue
            for (unsigned int j=0;j<relevantCUDDVars.size()-1;j++) {
                solver.clause(startingVarDiff+j,-1*startingVarsInvariantBases[i]-j-1,startingVarsInvariantBases[i+1]+j+1);
            }
        }



        while (true) {

            // Clause storage
            // std::list<std::vector<int> > clauses;

            // Allocate variables for selecting for each negative example which invariant is the right one
            if (negativeExamples.size()>0) {
                for (unsigned int i=nofNegativeExamplesProcessedSoFar;i<negativeExamples.size();i++) {
#ifndef NDEBUG
                    //std::cerr << "Selector for negative example " << i << ": " << nofVarsSoFar+1 << std::endl;
#endif
                    startingVarsInvariantSelectorForNegativeExample.push_back(nofVarsSoFar+1);
                    nofVarsSoFar += nofInvariants;
                }

                // Allocate variables for the active bases for each negative example
                for (unsigned int i=nofNegativeExamplesProcessedSoFar;i<negativeExamples.size();i++) {
#ifndef NDEBUG
                    //std::cerr << "Starting var for active base for negative example " << i << ": " << nofVarsSoFar+1 << std::endl;
#endif
                    startingVarsActiveBasesForEachNegativeExample.push_back(nofVarsSoFar+1);
                    nofVarsSoFar += relevantCUDDVars.size();
                }

                // Every negative example needs to be covered by an invariant base
                for (unsigned int i=nofNegativeExamplesProcessedSoFar;i<negativeExamples.size();i++) {
                    std::vector<int> clauseSelector;
                    for (int j=0;j<nofInvariants;j++) {
                        solver.add(startingVarsInvariantSelectorForNegativeExample[i]+j);
                    }
                    solver.add(0);
                }

                // Encode base selection
                for (unsigned int i=nofNegativeExamplesProcessedSoFar;i<negativeExamples.size();i++) {
                    for (int j=0;j<nofInvariants;j++) {
                        for (int k=0;k<static_cast<int>(relevantCUDDVars.size());k++) {
                            solver.clause(-1*startingVarsInvariantSelectorForNegativeExample[i]-j,-1*startingVarsActiveBasesForEachNegativeExample[i]-k,startingVarsInvariantBases[j]+k);
                            solver.clause(-1*startingVarsInvariantSelectorForNegativeExample[i]-j,startingVarsActiveBasesForEachNegativeExample[i]+k,-1*startingVarsInvariantBases[j]-k);
                        }
                    }
                }
            }

            // Now encode that everything between the negative example and the base needs to map to 0 in the BDD
            DdNode *one = Cudd_ReadOne(reachableAndWinning.manager()->getMgr());
            DdNode *zero = Cudd_Not(one);

            DdNode *bddForInvariantCorrectnessEncoding = reachableAndWinning.getCuddNode();

            if (negativeExamples.size()>0) {
                for (unsigned int negativeExample=nofNegativeExamplesProcessedSoFar;negativeExample<negativeExamples.size();negativeExample++) {

                    std::unordered_map<std::pair<DdNode*,unsigned int>,int,hashDdNodeUIntPair> nodeToVarMapper;
                    nodeToVarMapper[std::pair<DdNode*,unsigned int>(bddForInvariantCorrectnessEncoding,0)] = ++nofVarsSoFar;
                    solver.clause(nofVarsSoFar);
                    std::unordered_set<std::pair<DdNode*,unsigned int>,hashDdNodeUIntPair> doneList;
                    doneList.insert(std::pair<DdNode*,unsigned int>(bddForInvariantCorrectnessEncoding,0));
                    std::list<std::pair<DdNode*,unsigned int>> todoList;
                    todoList.push_back(std::pair<DdNode*,unsigned int>(bddForInvariantCorrectnessEncoding,0));
                    // std::cerr << "digraph {\n\"n0\";\n";
                    while (todoList.size()!=0) {
                        std::pair<DdNode*,unsigned int> thisNodeAndLevel = todoList.front();
                        todoList.pop_front();
                        int currentNo = nodeToVarMapper.at(thisNodeAndLevel);

                        if (Cudd_IsConstant(thisNodeAndLevel.first) && (thisNodeAndLevel.second==relevantCUDDVars.size())) {
                            if (thisNodeAndLevel.first==one) {
                                solver.clause(-1*currentNo);
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
                            solver.clause(-1*currentNo,numNext);

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
                                        std::cerr << "ThisLevel: " << thisIndex << "," << nextPair.second << std::endl;
                                        std::cerr << "data index: " << cuddIndexToRelevantVarNumberMapper[nextIndex] << std::endl;
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
                                // otherwise follow both cases, also in the case of don't cares
                                if (((negativeExamples[negativeExample][thisNodeAndLevel.second]==1) ^ (edge==1)) || (negativeExamples[negativeExample][thisNodeAndLevel.second]==0)) {
                                    // Take this one either way
                                    solver.clause(-1*currentNo,numNext);
                                } else {
                                    // Take this one conditionally
                                    int conditionLiteral = (negativeExamples[negativeExample][thisNodeAndLevel.second])*(startingVarsActiveBasesForEachNegativeExample[negativeExample]+thisNodeAndLevel.second);
                                    solver.clause(conditionLiteral,-1*currentNo,numNext);
                                }

                                //std::cerr << "n" << currentNo << "-> n" << numNext;
                                //if (edge==1) std::cerr << "[style=dashed];\n";
                                //else std::cerr << ";\n";
                            }

                        }
                    }
                    //std::cerr << "}\n";
                }
            }

            nofNegativeExamplesProcessedSoFar = negativeExamples.size();

            // Run SAT solver
            // Start encoding
            /*subprocess::popen cmd(satSolver, {});
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
            stdoutBuffer << cmd.stdout().rdbuf();*/

            auto retVal = solver.solve();
            if (retVal==CaDiCaL::Status::SATISFIABLE) {
                // Satisfiable!
                // Read model
                //std::istringstream is(stdoutBuffer.str());
                //std::string currentline;

                /*while (std::getline(is,currentline)) {
                    //std::cerr << "Interpreting model line: " << currentline << std::endl;
                    if (currentline.substr(0,2)=="v ") {
                        // Read model
                        std::istringstream modelreader(currentline.substr(2,std::string::npos));
                        while (!(modelreader.fail())) {
                            int next;
                            modelreader >> next;
                            if (!modelreader.fail()) {
                                model[std::abs(next)] = next>0;
                            }
                        }
                    }
                }*/

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
                        if (solver.val(startingVarsInvariantSelectorForNegativeExample[i]+j)>0) {
                            //std::cerr << "Negative example " << i << " is covered by invariant " << j << std::endl;

                            BF thisCase = mgr.constantTrue();
                            for (unsigned int k=0;k<relevantCUDDVars.size();k++) {
                                if (negativeExamples[i][k]!=0) {
                                    if ((negativeExamples[i][k]>0) == (solver.val(startingVarsInvariantBases[j]+k)>0)) {
                                        if (negativeExamples[i][k]>0)
                                            thisCase &= relevantCUDDVarBFs[k];
                                        else if (negativeExamples[i][k]<0)
                                            thisCase &= !relevantCUDDVarBFs[k];
                                    }
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
                if (!((!allInvariantsTogether & reachableAndWinning).isFalse())) {
                    throw SlugsException(false,"Internal Error: illegal invariants computed.");
                }

                // TODO: Why is the next one different from using !tildeB?
                BF rest = allInvariantsTogether & !tildeB; // !winningPositions & reachableAndWinningOrFirstNonWinningStateReached;
                BF noNextBehavior = !((safetySys).ExistAbstract(varCubePostOutput));

                if (rest.isFalse()) {

                    std::cout << "Result: Found invariants!\n";
                    std::cout << "Number of invariants: " << nofInvariants << std::endl;
                    for (int i=0;i<nofInvariants;i++) {
                        std::cout << "- Invariant " << i << " with base: ";
                        for (unsigned int k=0;k<relevantCUDDVars.size();k++) {
                            std::cout << ((solver.val(startingVarsInvariantBases[i]+k)>0?"1":"0"));
                        }
                        std::cout << "\n";
                        for (unsigned int j=0;j<negativeExamples.size();j++) {
                            if (solver.val(startingVarsInvariantSelectorForNegativeExample[j]+i)>0) {
                                std::cout << "  - Example ";
                                for (auto it : negativeExamples[j]) {
                                    if (it>0) std::cout << "1"; else { if (it<0) std::cout << "0"; else std::cout << "?"; }
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

                        // Simplification
                        //BF oldsimplified = mgr.constantFalse();
                        BF simplified = invariants[i];
                        //if (oldsimplified != simplified) {
                        //    oldsimplified = simplified;
                        simplified = simplified.optimizeRestrict(reachableAndWinningOrFirstNonWinningStateReached);
                        //simplified = simplified.optimizeRestrict(reachable);
                        //simplified = simplified.optimizeRestrict((winningPositions & reachable) | toBeCovered);
                        //}
                        BF_newDumpDot(*this,simplified /*& variables[12] & variables[6] & variables[8]*/,NULL,filename.str());

                        std::ostringstream filename3;
                        filename3 << "/tmp/invariant" << i << "-unoptimized.dot";
                        BF_newDumpDot(*this,invariants[i],NULL,filename3.str());

                        // Also print the cases of immediate specifiction violation separately
                        std::ostringstream filename2;
                        filename2 << "/tmp/invariant" << i << "-rightaway.dot";
                        BF immediatelyViolated = !invariants[i] & reachableAndWinningOrFirstNonWinningStateReached & noNextBehavior;
                        BF_newDumpDot(*this,immediatelyViolated,NULL,filename2.str());

                        // Globally Determinize case
                        if (!(immediatelyViolated.isFalse())) {
                            std::cout << "Reachable state immediately violating invariant " << i << " (using all variables declared in the input file in the order in which they are declared): ";
                            std::vector<unsigned int> varNums;
                            getVariableNumbersOfType("Pre", varNums);
                            for (auto it : varNums) {
                                if ((immediatelyViolated & variables[it]).isFalse()) {
                                    std::cerr << "0";
                                    immediatelyViolated &= !variables[it];
                                } else {
                                    std::cerr << "1";
                                    immediatelyViolated &= variables[it];
                                }
                                if (immediatelyViolated.isFalse()) throw "Internal error processing 'immediatelyViolated'";
                            }
                            std::cout << "\n";
                        }
                    }

                    // Generate SyGuS Instance
                    for (int i=0;i<nofInvariants;i++) {
                        std::ostringstream outFileName;
                        outFileName << "/tmp/invariant" << i << ".sygus";
                        std::ofstream sygusFile(outFileName.str());
                        sygusFile << "; Reactive Synthesis Invariant computation instance for invariant no. " << i << "\n; Variables (renamed):\n";
                        for (unsigned j = 0;j<relevantCUDDVarNames.size();j++) {
                            sygusFile << "; var " << j << ": " << relevantCUDDVarNames[j] << "\n";
                        }

                        // SyGuS File initial few lines
                        sygusFile << "( set-logic LRA )\n(synth-fun f (";
                        for (unsigned j = 0;j<relevantCUDDVarNames.size();j++) {
                            sygusFile << "(v" << j << " Bool)";
                        }
                        sygusFile << ") Bool"
                             "(( B Bool ))"
                                     "(( B Bool (";
                        for (unsigned j = 0;j<relevantCUDDVarNames.size();j++) {
                            sygusFile << "v" << j << " ";
                        }
                        sygusFile << "(not B )"
                                " (or B )"
                                " (and B))"
                                     ")))\n";

                        // Negative examples first
                        for (unsigned int j=0;j<negativeExamples.size();j++) {
                            if (solver.val(startingVarsInvariantSelectorForNegativeExample[j]+i)>0) {
                                sygusFile << "( constraint (= ( f";
                                for (unsigned int k=0;k<negativeExamples[j].size();k++) {
                                    if (negativeExamples[j][k]>0) {
                                        sygusFile << " true";
                                    } else {
                                        sygusFile << " false";
                                    }
                                }
                                sygusFile << ") false))\n";
                            }
                        }


                        // BDD: recurse
                        /*
                        std::unordered_set<DdNode *> doneSet;

                        std::function<void(DdNode*)> recurseFn = [&doneSet, &sygusFile, &relevantCUDDVarBFs, &recurseFn](DdNode * d) {

                            if (doneSet.count(d)>0) return;
                            doneSet.insert(d);

                            if (Cudd_IsConstant(d)) {
                                sygusFile << "(define-fun n" << (size_t)(d) << " ( ";
                                for (unsigned j = 0;j<relevantCUDDVarBFs.size();j++) {
                                    sygusFile << "(x" << j << " Bool)";
                                }
                                sygusFile << ") Bool ";

                                if (((size_t)d & 1)) {
                                    // Constant 0
                                    sygusFile << "false )\n";
                                } else {
                                    // Constant 1
                                    sygusFile << "true )\n";
                                }
                            } else {

                                DdNode *regular = Cudd_Regular(d);

                                // Recurse first
                                size_t thenSucc;
                                size_t elseSucc;
                                if (d==regular) {
                                    recurseFn(Cudd_T(regular));
                                    recurseFn(Cudd_E(regular));
                                    thenSucc = (size_t)(Cudd_T(regular));
                                    elseSucc = (size_t)(Cudd_E(regular));
                                } else {
                                    recurseFn(Cudd_Not(Cudd_T(regular)));
                                    recurseFn(Cudd_Not(Cudd_E(regular)));
                                    thenSucc = (size_t)(Cudd_Not(Cudd_T(regular)));
                                    elseSucc = (size_t)(Cudd_Not(Cudd_E(regular)));
                                }

                                sygusFile << "(define-fun n" << (size_t)(d) << " ( ";
                                for (unsigned j = 0;j<relevantCUDDVarBFs.size();j++) {
                                    sygusFile << "(x" << j << " Bool)";
                                }
                                sygusFile << ") Bool ";


                                // Find var
                                unsigned int foundVar = (unsigned int)-1;
                                for (unsigned int k=0;k<relevantCUDDVarBFs.size();k++) {
                                    if (relevantCUDDVarBFs[k].getCuddNode()->index == regular->index) foundVar = k;
                                }
                                if (foundVar==(unsigned int)-1) throw 4; // Should not happen, but if it does, at least don't compute wrong result!

                                if (regular!=d) sygusFile << "(not ";
                                sygusFile << "(ite x" << foundVar;
                                sygusFile << " (n" << thenSucc << " ";
                                for (unsigned j = 0;j<relevantCUDDVarBFs.size();j++) {
                                    sygusFile << "x" << j << " ";
                                }
                                sygusFile << ")";
                                sygusFile << "(n" << elseSucc << " ";
                                for (unsigned j = 0;j<relevantCUDDVarBFs.size();j++) {
                                    sygusFile << "x" << j << " ";
                                }
                                sygusFile << ")";
                                sygusFile << ")"; // ITE

                                if (regular!=d) sygusFile << ")"; // Not
                                sygusFile << ")\n";
                            }
                        };


                        recurseFn(bddForInvariantCorrectnessEncoding);


                        // Finally, the positive examples
                        sygusFile << "( constraint (forall (";
                        for (unsigned j = 0;j<relevantCUDDVarNames.size();j++) {
                            sygusFile << "(x" << j << " Bool)";
                        }
                        sygusFile << ") (or (not ( n" << (size_t)bddForInvariantCorrectnessEncoding;
                        for (unsigned j = 0;j<relevantCUDDVarNames.size();j++) {
                            sygusFile << " x" << j;
                        }
                        sygusFile << ") ) (f";
                        for (unsigned j = 0;j<relevantCUDDVarNames.size();j++) {
                            sygusFile << " x" << j;
                        }
                        sygusFile << "))))\n";
                        */



                        // Go and go.
                        std::function<double(DdNode*,std::vector<int>)> recurseFn2 = [&sygusFile, &relevantCUDDVarBFs, &recurseFn2](DdNode * d,std::vector<int> fix) {

                            if (Cudd_IsConstant(d)) {
                                if (((size_t)d & 1)) {
                                    // Constant 0
                                    return 0.0;
                                } else {
                                    // Constant 1
                                    sygusFile << "( constraint (forall (";
                                    for (unsigned int j=0;j<fix.size();j++) {
                                        if (fix[j]==0) {
                                            sygusFile << "(x" << j << " Bool)";
                                        }
                                    }
                                    sygusFile << ")";
                                    sygusFile << "(= ( f";
                                    for (unsigned int j=0;j<fix.size();j++) {
                                        if (fix[j]==0) {
                                            sygusFile << " x" << j;
                                        } else if (fix[j]==-1) {
                                            sygusFile << " false";
                                        } else if (fix[j]==1) {
                                            sygusFile << " true";
                                        } else {
                                            std::cerr << "Illegal fix: " << fix[j] << std::endl;
                                            throw 4;
                                        }
                                    }
                                    sygusFile << ") true )))\n";
                                    return 1.0;
                                }
                            } else {

                                DdNode *regular = Cudd_Regular(d);

                                // Find var
                                unsigned int foundVar = (unsigned int)-1;
                                for (unsigned int k=0;k<relevantCUDDVarBFs.size();k++) {
                                    if (relevantCUDDVarBFs[k].getCuddNode()->index == regular->index) foundVar = k;
                                }
                                if (foundVar==(unsigned int)-1) throw 4; // Should not happen, but if it does, at least don't compute wrong result!

                                if (regular==d) {
                                    fix[foundVar] = 1;
                                    double a = recurseFn2(Cudd_T(d),fix);
                                    fix[foundVar] = -1;
                                    double b = recurseFn2(Cudd_E(d),fix);
                                    return a+b;
                                } else {
                                    fix[foundVar] = 1;
                                    double a = recurseFn2(Cudd_Not(Cudd_T(regular)),fix);
                                    fix[foundVar] = -1;
                                    double b = recurseFn2(Cudd_Not(Cudd_E(regular)),fix);
                                    return a+b;
                                }
                            }
                        };

                        std::vector<int> fixes;
                        for (unsigned int l=0;l<relevantCUDDVarBFs.size();l++) {
                            fixes.push_back(0);
                        }

                        std::cerr << "Nof Cubes: " << recurseFn2(bddForInvariantCorrectnessEncoding,fixes) << std::endl;




                        sygusFile << "\n(check-synth)\n";




                    }

                    return;
                }

                // Ok, so rest is not empty
                // Compute new negative exaple
                std::vector<int> nextNegativeExample;
                for (unsigned int k=0;k<relevantCUDDVars.size();k++) {
                    // Which direction to prefer is random to make negative examples for uniform
                    if (supportForDontCare && ((rest & relevantCUDDVarBFs[k]).ExistAbstractSingleVar(relevantCUDDVarBFs[k]) == (rest & !relevantCUDDVarBFs[k]).ExistAbstractSingleVar(relevantCUDDVarBFs[k]))) {
                        // Dont't case!
                        nextNegativeExample.push_back(0);
                    } else  {
                        if (rng() & 1) {
                            if ((rest & relevantCUDDVarBFs[k]).isFalse()) {
                                nextNegativeExample.push_back(-1);
                                rest &= !relevantCUDDVarBFs[k];
                            } else {
                                nextNegativeExample.push_back(1);
                                rest &= relevantCUDDVarBFs[k];
                            }
                        } else {
                            if ((rest & !relevantCUDDVarBFs[k]).isFalse()) {
                                nextNegativeExample.push_back(1);
                                rest &= relevantCUDDVarBFs[k];
                            } else {
                                nextNegativeExample.push_back(-1);
                                rest &= !relevantCUDDVarBFs[k];
                            }
                        }
                    }

                    // TODO: Can this be done in a smarter way? Enumerating some cube instead?
                }

                std::cerr << "New negative example (no." << negativeExamples.size() << "): ";
                for (unsigned int i=0;i<nextNegativeExample.size();i++) {
                    int it = nextNegativeExample[bfVariableNameOrder[i]];
                    if (it>0) std::cerr << "1"; else { if (it<0) std::cerr << "0"; else std::cerr << "?"; }
                }
                std::cerr << "\n";

                negativeExamples.push_back(nextNegativeExample);

            } else if (retVal==20) {
                // Unsatisfiable!
                std::cout << "Result: Cannot find " << nofInvariants << " covering the non-winning reachable states.\n";
                return;
            } else {
                //std::ostringstream stderrBuffer;
                //stderrBuffer << "(" << retVal << ")" << cmd.stderr().rdbuf();
                //std::ostringstream error;
                //error << stderrBuffer.str() << ", stdout: " << stdoutBuffer.str();
                //std::cerr << "BufSiz:" << error.str().length() << std::endl;
                throw SlugsException(false,"Solving Error");
            }
        }




#else
        std::cerr << "This plugin is only supported for a CUDD backend.\n";
#endif


    }




public:
    static GR1Context* makeInstance(std::list<std::string> &filenames) {
        return new XComputeInvariants<T,supportForDontCare>(filenames);
    }
};


#endif
