#ifndef __EXTENSION_COMPUTE_INVARIANTS_HPP
#define __EXTENSION_COMPUTE_INVARIANTS_HPP

#include "gr1context.hpp"
#include <string>
#include <boost/tuple/tuple.hpp>
#include <boost/tuple/tuple_comparison.hpp>
#include <functional>
#include <unordered_map>
#include <random>
#include "subprocess.hpp"
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

    XComputeInvariants<T,supportForDontCare>(std::list<std::string> &filenames) : T(filenames) {
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
        std::vector<std::vector<int> > negativeExamples; // +1: TRUE, -1: FALSE, 0: don't care

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

        // Allocate variables for invariant bases
        for (int i=0;i<nofInvariants;i++) {
#ifndef NDEBUG \
    //std::cerr << "Starting var invariant base " << i << ": " << nofVarsSoFar+1 << std::endl;
#endif
            startingVarsInvariantBases.push_back(nofVarsSoFar+1);
            nofVarsSoFar += relevantCUDDVars.size();
        }

        // Allocate SAT Solver
        CaDiCaL::Solver solver;



        while (true) {

            // Clause storage
            // std::list<std::vector<int> > clauses;

            // Allocate variables for selecting for each negative example which invariant is the right one
            if (negativeExamples.size()>0) {
                for (unsigned int i=negativeExamples.size()-1;i<negativeExamples.size();i++) {
#ifndef NDEBUG
                    //std::cerr << "Selector for negative example " << i << ": " << nofVarsSoFar+1 << std::endl;
#endif
                    startingVarsInvariantSelectorForNegativeExample.push_back(nofVarsSoFar+1);
                    nofVarsSoFar += nofInvariants;
                }

                // Allocate variables for the active bases for each negative example
                for (unsigned int i=negativeExamples.size()-1;i<negativeExamples.size();i++) {
#ifndef NDEBUG
                    //std::cerr << "Starting var for active base for negative example " << i << ": " << nofVarsSoFar+1 << std::endl;
#endif
                    startingVarsActiveBasesForEachNegativeExample.push_back(nofVarsSoFar+1);
                    nofVarsSoFar += relevantCUDDVars.size();
                }

                // Every negative example needs to be covered by an invariant base
                for (unsigned int i=negativeExamples.size()-1;i<negativeExamples.size();i++) {
                    std::vector<int> clauseSelector;
                    for (int j=0;j<nofInvariants;j++) {
                        solver.add(startingVarsInvariantSelectorForNegativeExample[i]+j);
                    }
                    solver.add(0);
                }

                // Encode base selection
                for (unsigned int i=negativeExamples.size()-1;i<negativeExamples.size();i++) {
                    for (int j=0;j<nofInvariants;j++) {
                        for (int k=0;k<static_cast<int>(relevantCUDDVars.size());k++) {
                            solver.clause(-1*startingVarsInvariantSelectorForNegativeExample[i]-j,-1*startingVarsActiveBasesForEachNegativeExample[i]-k,startingVarsInvariantBases[j]+k);
                            solver.clause(-1*startingVarsInvariantSelectorForNegativeExample[i]-j,startingVarsActiveBasesForEachNegativeExample[i]+k,-1*startingVarsInvariantBases[j]-k);
                        }
                    }
                }
            }

            // Now encode that everything between the negative example and the base needs to map to 0 in the BDD
            DdNode *one = Cudd_ReadOne(toBeCovered.manager()->getMgr());
            DdNode *zero = Cudd_Not(one);

            if (negativeExamples.size()>0) {
                for (unsigned int negativeExample=negativeExamples.size()-1;negativeExample<negativeExamples.size();negativeExample++) {

                    std::unordered_map<std::pair<DdNode*,unsigned int>,int,hashDdNodeUIntPair> nodeToVarMapper;
                    nodeToVarMapper[std::pair<DdNode*,unsigned int>(winningPositions.getCuddNode(),0)] = ++nofVarsSoFar;
                    solver.clause(nofVarsSoFar);
                    std::unordered_set<std::pair<DdNode*,unsigned int>,hashDdNodeUIntPair> doneList;
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

                std::vector<bool> model(nofVarsSoFar+1);
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
                for (int i=1;i<=nofVarsSoFar;i++) {
                    model[i] = solver.val(i)>0;
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
                        if (model[startingVarsInvariantSelectorForNegativeExample[i]+j]) {
                            //std::cerr << "Negative example " << i << " is covered by invariant " << j << std::endl;

                            BF thisCase = mgr.constantTrue();
                            for (unsigned int k=0;k<relevantCUDDVars.size();k++) {
                                if (negativeExamples[i][k]!=0) {
                                    if ((negativeExamples[i][k]>0) == (model[startingVarsInvariantBases[j]+k])) {
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
                            std::cout << ((model[startingVarsInvariantBases[i]+k]?"1":"0"));
                        }
                        std::cout << "\n";
                        for (unsigned int j=0;j<negativeExamples.size();j++) {
                            if (model[startingVarsInvariantSelectorForNegativeExample[j]+i]) {
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
                for (auto it : nextNegativeExample) {
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
