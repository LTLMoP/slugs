#!/usr/bin/python
#
# This python script containts lists of all plugins
# and computes the code for main.cpp that lists all allowed parameter combinations
import os, sys


#========================================================
# Some Helper functions
#========================================================

# This one is used for the combinable/uncombinable parameters below
def combineWithAllOtherParameters(a):
    assert len([(b,c) for (b,c) in listOfCommandLineParameters if b==a])==1
    return [(a,b) for (b,c) in listOfCommandLineParameters if not b==a] 
def combineWithAllOtherParametersBut(a,q):
    assert len([(b,c) for (b,c) in listOfCommandLineParameters if b==a])==1
    for x in q:
        assert len([(b,c) for (b,c) in listOfCommandLineParameters if b==x])==1
    return [(a,b) for (b,c) in listOfCommandLineParameters if not b==a and not (b in q)] 

# This one is a basic parameter->plugin mapper.
def simpleInstantiationMapper(param,templateName,params):
    if param in params:
        ret = [(templateName,)]
    else:
        ret = []
    params.difference_update([param])
    return ret


#========================================================
# Configuration
#========================================================
#
# The information about plugins come in three shapes:
# 1. The command line parameters to the tools
# 2. Which command line parameters are combinable and which ones are not
# 3. The names of the templates
# 4. The order in which templates must be instantiated
# 5. Functions that "eat" command line parameters and produce template instantiations

# -------------------------------------------------------
# Information about command line parameters
# -------------------------------------------------------

# Which command line parameters exist?
listOfCommandLineParameters = [
    ("explicitStrategy","Extract an explicit-state strategy that is compatible with JTLV."),
    ("symbolicStrategy","Extract a symbolic (BDD-based) strategy."),
    ("simpleSymbolicStrategy","Extract a symbolic (BDD-based) strategy in which the system goals have been flattened out."),
    ("jsonOutput","When computing an explicit finite-state strategy, use json output."),
    ("sysInitRoboticsSemantics","In standard GR(1) synthesis, a specification is called realizable if for every initial input proposition valuation that is allowed by the initialization contraints, there is some suitable output proposition valuation. In the modified semantics for robotics applications, the controller has to be fine with any admissible initial position in the game."),
    ("computeWeakenedSafetyAssumptions","Extract a minimal conjunctive normal form Boolean formula that represents some minimal CNF for a set of safety assumptions that leads to realiazability and is a weakened form of the safety assumptions given. Requires the option '--onlyRealizability' to be given as well."),
    ("biasForAction","Extract controllers that rely on the liveness assumptions being satisfied as little as possible."),
    ("computeCNFFormOfTheSpecification","Lets the Synthesis tool skip the synthesis step, and only compute a version of the specification that can be used by other synthesis tools that require it to be CNF-based."),
    ("counterStrategy","Computes the environment counterstrategy"),
    ("simpleRecovery","Adds transitions to the system implementation that allow it to recover from sparse environment safety assumption faults in many cases"),
    ("fixedPointRecycling","Modifies the realizability checking algorithm to recycle previous innermost fixed points. Realizability checking should typically become faster this way."),
    ("interactiveStrategy","Opens an interactive shell after realizability checking to allow examining the properties of the generated strategy."),
    ("IROSfastslow","Uses fastslow semantics from IROS 2012 paper. Requires different input file format."),
    ("analyzeInterleaving","Interleaves the turn-taking. Requires different input file format."),
    ("analyzeInitialPositions","Performs an analysis of the set of starting positions in the realizability game."),
    ("restrictToReachableStates","Restricts the analysis of the starting positions (see --analyzeInitialPositions) to reachable ones."),
    ("analyzeAssumptions","Checks which assumptions are actually needed and which assumptions are helpful (i.e., they sometimes reduce reactive distances to the goal)."),
    ("analyzeSafetyLivenessInteraction","Analyzes how safety and liveness properties interact in the specification."),
    ("computeInterestingRunOfTheSystem","Computes an interesting run of the synthesized system"),
    ("computeAbstractWinningTrace","Computes an abstract trace that is winning for the system or the environment."),
    ("extractExplicitPermissiveStrategy","Computes an explicit-state permissive strategy."),
    ("computeIncompleteInformationEstimator","Computes a imcomplete-information state estimation controller."),
    ("nonDeterministicMotion","Computes a controller using an non-deterministic motion abstraction."),
    ("nonDeterministicMotionSelfLoopLivenessAssumption","Adds a liveness assumption for the nondeterministic Motion plugin that prevents the abstraction from self-looping forever."),
    ("twoDimensionalCost","Computes a controller that optimizes for waiting and action cost at the same time."),
    ("cooperativeGR1Strategy","Computes a controller strategy that is cooperative with its environment."),
    ("synthesisProfiling","Performs standard GR(1) synthesis but profiles the number of iterations and the computation times."),
    ("environmentFriendlyStrategy","Computes an environment-friendly strategy according to the construction from the TACAS 2019 paper 'Environmentally-friendly GR(1) Synthesis' by Majumdar, Piterman, and Schmuck"),
    ("environmentFriendlySynthesis","Performs environment-friendly realizability checking according to the construction from the TACAS 2019 paper 'Environmentally-friendly GR(1) Synthesis' by Majumdar, Piterman, and Schmuck, using a quadruply nested fixpoint."),
    ("useHeuristic","Modifier for --environmentFriendlySynthesis: When computing winningPositions for environment-friendly strategies a sound but incomplete heuristic is used which only explores b==a within EnvironmentFriendlySynthesis."),
    ("computeInvariants","Compute invariants that explain a synthesized strategy and/or the strategic choices that need to be made by an implementation of the specification"),
    ("computeInvariantsDontCare","Add don't care support for the '--computeInvariants' plugin, which can simplify the invariants but makes distributing the counter-examples to invariants less precise.")
]

# Which command line parameters can be combined?
combinableParameters = [

    # Environment-friendly synthesis
    ("environmentFriendlyStrategy","jsonOutput"),
    ("environmentFriendlyStrategy","useHeuristic"),
    ("environmentFriendlySynthesis","useHeuristic"),
    
    # SysInitRoboticsSemantics works with pretty much everything
    # where realizability is checked in the classical sense
    ("sysInitRoboticsSemantics","explicitStrategy"),
    ("sysInitRoboticsSemantics","counterStrategy"),
    ("sysInitRoboticsSemantics","jsonOutput"),
    ("sysInitRoboticsSemantics","biasForAction"),
    ("sysInitRoboticsSemantics","symbolicStrategy"),
    ("sysInitRoboticsSemantics","simpleSymbolicStrategy"),
    ("sysInitRoboticsSemantics","nonDeterministicMotion"),
    ("sysInitRoboticsSemantics","cooperativeGR1Strategy"),
    ("sysInitRoboticsSemantics","extractExplicitPermissiveStrategy"),
    ("sysInitRoboticsSemantics","simpleRecovery"),
    ("sysInitRoboticsSemantics","fixedPointRecycling"),
    ("sysInitRoboticsSemantics","IROSfastslow"),
    ("sysInitRoboticsSemantics","twoDimensionalCost"),
    
    # Strategy extraction options
    ("explicitStrategy","biasForAction"),
    ("symbolicStrategy","biasForAction"),
    ("simpleSymbolicStrategy","biasForAction"),
    ("explicitStrategy","cooperativeGR1Strategy"),
    ("symbolicStrategy","cooperativeGR1Strategy"),
    ("simpleSymbolicStrategy","cooperativeGR1Strategy"),
    ("simpleRecovery","explicitStrategy"),
    ("simpleRecovery","symbolicStrategy"),
    ("simpleRecovery","simpleSymbolicStrategy"),
    ("explicitStrategy","fixedPointRecycling"),
    ("simpleSymbolicStrategy","fixedPointRecycling"),
    ("simpleSymbolicStrategy","simpleSymbolicStrategy"),
    ("explicitStrategy","IROSfastslow"),
    ("simpleSymbolicStrategy","IROSfastslow"),
    ("symbolicStrategy","IROSfastslow"),
    ("explicitStrategy","twoDimensionalCost"),
    ("simpleSymbolicStrategy","twoDimensionalCost"),
    ("symbolicStrategy","twoDimensionalCost"),
    ("symbolicStrategy","fixedPointRecycling"),
    
    
    # Permissive Strategies
    ("extractExplicitPermissiveStrategy","simpleRecovery"),
    
    # Parameters to "restrictToReachableStates"
    ("analyzeInitialPositions","restrictToReachableStates"),
    
    # Analyze Initial Positions
    ("analyzeInitialPositions","restrictToReachableStates"),
    
    # NondeterministicMotion
    ("nonDeterministicMotion","sysInitRoboticsSemantics"),
    ("nonDeterministicMotion","interactiveStrategy"),
    ("nonDeterministicMotion","extractExplicitPermissiveStrategy"),
    ("simpleSymbolicStrategy","nonDeterministicMotion"),
    ("symbolicStrategy","nonDeterministicMotion"),
    
    # Nondet-Motion --> Self loops
    ("nonDeterministicMotionSelfLoopLivenessAssumption","nonDeterministicMotion"),
    ("nonDeterministicMotionSelfLoopLivenessAssumption","sysInitRoboticsSemantics"),
    ("nonDeterministicMotionSelfLoopLivenessAssumption","interactiveStrategy"),
    ("nonDeterministicMotionSelfLoopLivenessAssumption","extractExplicitPermissiveStrategy"),
    ("simpleSymbolicStrategy","nonDeterministicMotionSelfLoopLivenessAssumption"),
    ("symbolicStrategy","nonDeterministicMotionSelfLoopLivenessAssumption"),
    ("explicitStrategy","nonDeterministicMotionSelfLoopLivenessAssumption"),
    
    
    # Bias for Action
    ("biasForAction","extractExplicitPermissiveStrategy"),
    ("biasForAction","simpleRecovery"),
    ("biasForAction","interactiveStrategy"),
    
    # Simple Recovery
    ("simpleRecovery","IROSfastslow"),
    ("simpleRecovery","twoDimensionalCost"),
    ("simpleRecovery","cooperativeGR1Strategy"),
    ("simpleRecovery","fixedPointRecycling"),
    
    # FixedPointRecycling and Interactive Strategy
    ("fixedPointRecycling","extractExplicitPermissiveStrategy"),
    ("fixedPointRecycling","interactiveStrategy"),
    ("interactiveStrategy","IROSfastslow"),
    ("interactiveStrategy","twoDimensionalCost"),
    ("interactiveStrategy","cooperativeGR1Strategy"),
    
    # Compute Invariants
    ("computeInvariants","computeInvariantsDontCare"),
    
    # Misc
    ("IROSfastslow","extractExplicitPermissiveStrategy"),
    ("extractExplicitPermissiveStrategy","twoDimensionalCost"),


    
] + combineWithAllOtherParameters("jsonOutput") # there is a requirement below that this requires an explicit-state strategy output

# Which ones cannot be combined?
uncombinableParameters = [

    # Environment-friendly.
    ("environmentFriendlyStrategy","environmentFriendlySynthesis"),

    # Interactive Strategy
    ("interactiveStrategy","sysInitRoboticsSemantics"),
    ("interactiveStrategy","explicitStrategy"),
    ("interactiveStrategy","symbolicStrategy"),
    ("interactiveStrategy","simpleSymbolicStrategy"),
    ("simpleRecovery","interactiveStrategy"),

    # ComputeWeakenedSafetyAssumptions
    ("computeWeakenedSafetyAssumptions","explicitStrategy"),
    ("computeWeakenedSafetyAssumptions","symbolicStrategy"),
    ("computeWeakenedSafetyAssumptions","simpleSymbolicStrategy"),
    ("computeWeakenedSafetyAssumptions","sysInitRoboticsSemantics"),

    
    # Strategy can only be simple symbolic, symbolic or explicit
    ("explicitStrategy","symbolicStrategy"),
    ("explicitStrategy","simpleSymbolicStrategy"),
    ("symbolicStrategy","simpleSymbolicStrategy"),
    
    # No JSON Output for symbolic strategies
    ("jsonOutput","symbolicStrategy"),
    ("jsonOutput","simpleSymbolicStrategy"),
    
    # Permissive strategies have a special output format.
    ("explicitStrategy","extractExplicitPermissiveStrategy"),
    ("extractExplicitPermissiveStrategy","simpleSymbolicStrategy"),
    ("symbolicStrategy","extractExplicitPermissiveStrategy"),
    ("jsonOutput","extractExplicitPermissiveStrategy"),
    
    # Incompatible plugins that modify the computation of the winning positions
    ("cooperativeGR1Strategy","biasForAction"),
    
    # CounterStrategy
    ("symbolicStrategy","counterStrategy"),
    ("simpleSymbolicStrategy","counterStrategy"),
    ("counterStrategy","simpleRecovery"),
    ("counterStrategy","fixedPointRecycling"),
    ("counterStrategy","interactiveStrategy"),
    ("counterStrategy","IROSfastslow"),
    ("counterStrategy","extractExplicitPermissiveStrategy"),
    ("counterStrategy","twoDimensionalCost"),
    ("counterStrategy","cooperativeGR1Strategy"),
    ("explicitStrategy","counterStrategy"),
    
    # Bias For Action
    ("biasForAction","counterStrategy"),
    ("biasForAction","fixedPointRecycling"),
    ("biasForAction","IROSfastslow"),
    ("biasForAction","twoDimensionalCost"),
    
    # FixedPointRecycling and Interactive Strategy
    ("fixedPointRecycling","IROSfastslow"),
    ("fixedPointRecycling","twoDimensionalCost"),
    ("fixedPointRecycling","cooperativeGR1Strategy"),
    ("interactiveStrategy","extractExplicitPermissiveStrategy"),
    
    # Misc
    ("IROSfastslow","twoDimensionalCost"),
    ("IROSfastslow","cooperativeGR1Strategy"),
    ("extractExplicitPermissiveStrategy","cooperativeGR1Strategy"),
    ("twoDimensionalCost","cooperativeGR1Strategy"),

] + combineWithAllOtherParameters("computeIncompleteInformationEstimator") + combineWithAllOtherParameters("computeAbstractWinningTrace") + combineWithAllOtherParameters("computeInterestingRunOfTheSystem") + combineWithAllOtherParameters("analyzeSafetyLivenessInteraction") + combineWithAllOtherParameters("analyzeAssumptions") + combineWithAllOtherParameters("computeCNFFormOfTheSpecification") + combineWithAllOtherParameters("analyzeInterleaving") + combineWithAllOtherParametersBut("analyzeInitialPositions",["restrictToReachableStates"]) + combineWithAllOtherParametersBut("restrictToReachableStates",["analyzeInitialPositions"]) + combineWithAllOtherParametersBut("nonDeterministicMotion",["sysInitRoboticsSemantics","interactiveStrategy","extractExplicitPermissiveStrategy","simpleSymbolicStrategy","symbolicStrategy","nonDeterministicMotionSelfLoopLivenessAssumption"]) + combineWithAllOtherParametersBut("nonDeterministicMotionSelfLoopLivenessAssumption",["sysInitRoboticsSemantics","interactiveStrategy","extractExplicitPermissiveStrategy","simpleSymbolicStrategy","symbolicStrategy","nonDeterministicMotion"]) + combineWithAllOtherParameters("computeWeakenedSafetyAssumptions") + combineWithAllOtherParameters("synthesisProfiling") + combineWithAllOtherParametersBut("environmentFriendlyStrategy",["useHeuristic","jsonOutput"]) + combineWithAllOtherParametersBut("environmentFriendlySynthesis",["useHeuristic"]) +  combineWithAllOtherParametersBut("useHeuristic",["environmentFriendlySynthesis","environmentFriendlyStrategy","jsonOutput"]) + combineWithAllOtherParametersBut("computeInvariants",["computeInvariantsDontCare"]) + combineWithAllOtherParametersBut("computeInvariantsDontCare",["computeInvariants"])

# Which ones require (one of) another parameter(s)
requiredParameters = [
    ("restrictToReachableStates",["analyzeInitialPositions"]),
    ("simpleRecovery",["explicitStrategy","symbolicStrategy","simpleSymbolicStrategy"]),
    ("jsonOutput",["explicitStrategy","environmentFriendlyStrategy"]),
    ("nonDeterministicMotionSelfLoopLivenessAssumption",["nonDeterministicMotion"]),
    ("useHeuristic",["environmentFriendlySynthesis","environmentFriendlyStrategy"]),
    ("computeInvariantsDontCare",["computeInvariants"]),
]

# -------------------------------------------------------
# Information about plugin classes
# -------------------------------------------------------

# Which plugins exist?
listOfPluginClasses = [
    ("XAbstractWinningTraceGenerator","extensionAbstractWinningTraceGenerator.hpp"),
    ("XAnalyzeAssumptions","extensionAnalyzeAssumptions.hpp"),
    ("XAnalyzeInitialPositions","extensionAnalyzeInitialPositions.hpp"),
    ("XAnalyzeSafetyLivenessInteraction","extensionAnalyzeSafetyLivenessInteraction.hpp"),
    ("XBiasForAction","extensionBiasForAction.hpp"),
    ("XComputeCNFFormOfTheSpecification","extensionComputeCNFFormOfTheSpecification.hpp"),
    ("XComputeInterestingRunOfTheSystem","extensionComputeInterestingRunOfTheSystem.hpp"),
    ("XCooperativeGR1Strategy","extensionCooperativeGR1Strategy.hpp"),
    ("XCounterStrategy","extensionCounterstrategy.hpp"),
    ("XExtractExplicitCounterStrategy","extensionExtractExplicitCounterstrategy.hpp"),
    ("XExtractExplicitStrategy","extensionExtractExplicitStrategy.hpp"),
    ("XExtractSymbolicStrategy","extensionExtractSymbolicStrategy.hpp"),
    ("XFixedPointRecycling","extensionFixedPointRecycling.hpp"),
    ("XIncompleteInformationEstimatorSynthesis","extensionIncompleteInformationEstimatorSynthesis.hpp"),
    ("XInteractiveStrategy","extensionInteractiveStrategy.hpp"),
    ("XInterleave","extensionInterleave.hpp"),
    ("XIROSFS","extensionIROSfastslow.hpp"),
    ("XNonDeterministicMotion","extensionNondeterministicMotion.hpp"),
    ("XExtractPermissiveExplicitStrategy","extensionPermissiveExplicitStrategy.hpp"),
    ("XRoboticsSemantics","extensionRoboticsSemantics.hpp"),
    ("XTwoDimensionalCost","extensionTwoDimensionalCost.hpp"),
    ("XComputeWeakenedSafetyAssumptions","extensionWeakenSafetyAssumptions.hpp"),
    ("XSynthesisProfiling","extensionSynthesisProcessProfiling.hpp"),
    ("XEnvironmentFriendlySynthesis","extensionEnvironmentFriendlySynthesis.hpp"),
    ("XExtractEnvironmentFriendlyStrategy","extensionExtractEnvironmentFriendlyStrategy.hpp"),
    ("XComputeInvariants","extensionComputeInvariants.hpp")
    
    #include "extensionEnvironmentFriendlySynthesis.hpp"
#include "extensionExtractEnvironmentFriendlyStrategy.hpp"

]

# In which order do they have to be instantiated?
# This is a partial order. An element (A,B) means that A comes *outer than* B
orderOfPluginClassesInInstantiations = [

    # Standard-Order (from inner to outer):
    # - computeWinningPositions modifying plugins
    #   -> XBiasForAction
    #   -> XCooperativeGR1Strategy
    # - checkRealizability modifying plugins
    #   -> XRoboticsSemantics
    # - execute() modifying plugins
    #   -> XExtractSymbolicStrategy
    #   -> XExtractExplicitStrategy
    
    
    ("XRoboticsSemantics","XBiasForAction"),
    ("XExtractSymbolicStrategy","XBiasForAction"),
    ("XExtractExplicitStrategy","XBiasForAction"),
    ("XExtractSymbolicStrategy","XRoboticsSemantics"),
    ("XExtractExplicitStrategy","XRoboticsSemantics"),
    ("XExtractPermissiveExplicitStrategy","XRoboticsSemantics"),

    ("XRoboticsSemantics","XCooperativeGR1Strategy"),
    ("XExtractSymbolicStrategy","XCooperativeGR1Strategy"),
    ("XExtractExplicitStrategy","XCooperativeGR1Strategy"),
    
    ("XExtractPermissiveExplicitStrategy","XIROSFS"),
    ("XRoboticsSemantics","XIROSFS"),
    ("XRoboticsSemantics","XTwoDimensionalCost"),
    ("XExtractExplicitStrategy","XIROSFS"),
    ("XRoboticsSemantics","XFixedPointRecycling"),
    ("XExtractPermissiveExplicitStrategy","XTwoDimensionalCost"),
    ("XExtractExplicitStrategy","XFixedPointRecycling"),
    ("XExtractExplicitStrategy","XTwoDimensionalCost"),
    ("XExtractPermissiveExplicitStrategy","XNonDeterministicMotion"),
    ("XExtractSymbolicStrategy","XIROSFS"),
    ("XExtractSymbolicStrategy","XNonDeterministicMotion"),
    ("XExtractExplicitCounterStrategy","XCounterStrategy"),
    ("XInteractiveStrategy","XCooperativeGR1Strategy"),
    ("XInteractiveStrategy","XTwoDimensionalCost"),
    ("XInteractiveStrategy","XIROSFS"),
    ("XInteractiveStrategy","XNonDeterministicMotion"),
    ("XInteractiveStrategy","XBiasForAction"),
    ("XExtractPermissiveExplicitStrategy","XFixedPointRecycling"),
    ("XInteractiveStrategy","XFixedPointRecycling"),
    ("XExtractPermissiveExplicitStrategy","XBiasForAction"),
    ("XExtractSymbolicStrategy","XTwoDimensionalCost"),
    ("XExtractSymbolicStrategy","XFixedPointRecycling"),
    ("XExtractEnvironmentFriendlyStrategy","XEnvironmentFriendlySynthesis")
    
]



# -------------------------------------------------------
# Mapping Plugin combinations to class instantiations
# -------------------------------------------------------    
listOfCommandLineCombinationToClassInstantiationMappers = []

# Environment friendly synthesis
def envFriendlySynthesis(params):
    heuristic = "useHeuristic" in params
    if "environmentFriendlySynthesis" in params:
        ret = [("XEnvironmentFriendlySynthesis","true" if heuristic else "false") ]
        params.difference_update(["environmentFriendlySynthesis","useHeuristic"])
        return ret
    return []
listOfCommandLineCombinationToClassInstantiationMappers.append(envFriendlySynthesis)

# Environment friendly synthesis
def envFriendlyStrategy(params):
    json = "jsonOutput" in params
    heuristic = "useHeuristic" in params
    if "environmentFriendlyStrategy" in params:
        ret = [("XExtractEnvironmentFriendlyStrategy","true" if json else "false"),("XEnvironmentFriendlySynthesis","true" if heuristic else "false") ]
        params.difference_update(["jsonOutput","environmentFriendlyStrategy","useHeuristic"])
        return ret
    return []
listOfCommandLineCombinationToClassInstantiationMappers.append(envFriendlyStrategy)

# Two dimensional cost Motion (needs to know if robotics Semantics has been selected and if simple recovery is active or not)
def twoDimensionalCost(params):
    sysIn = "sysInitRoboticsSemantics" in params
    simpleRecovery = "simpleRecovery" in params
    if "twoDimensionalCost" in params:
        ret = [("XTwoDimensionalCost","true" if sysIn else "false","true" if simpleRecovery else "false")]
        params.difference_update(["twoDimensionalCost","sysInitRoboticsSemantics"])
        return ret
    return []
listOfCommandLineCombinationToClassInstantiationMappers.append(twoDimensionalCost)


# NonDeterministic Motion
def nondeterministicMotion(params):
    sysIn = "sysInitRoboticsSemantics" in params
    selfLoop = "nonDeterministicMotionSelfLoopLivenessAssumption" in params
    if "nonDeterministicMotion" in params:
        ret = [("XNonDeterministicMotion","true" if sysIn else "false","true" if selfLoop else "false")]
        params.difference_update(["nonDeterministicMotion","sysInitRoboticsSemantics","nonDeterministicMotionSelfLoopLivenessAssumption"])
        return ret
    return []
listOfCommandLineCombinationToClassInstantiationMappers.append(nondeterministicMotion)

# Permissive Strategies
def permissiveStrat(params):
    simpleRec = "simpleRecovery" in params
    if "extractExplicitPermissiveStrategy" in params:
        ret = [("XExtractPermissiveExplicitStrategy","true" if simpleRec else "false")]
        params.difference_update(["extractExplicitPermissiveStrategy","simpleRecovery"])
        return ret
    return []
listOfCommandLineCombinationToClassInstantiationMappers.append(permissiveStrat)

# Compute Invariants
def computeInvariants(params):
    dontCare = "computeInvariantsDontCare" in params
    if "computeInvariants" in params:
        ret = [("XComputeInvariants","true" if dontCare else "false")]
        params.difference_update(["computeInvariants","computeInvariantsDontCare"])
        return ret
    return []
listOfCommandLineCombinationToClassInstantiationMappers.append(computeInvariants)

# Analyze initial positions
def analyzeInitialPositions(params):
    reach = "restrictToReachableStates" in params
    if "analyzeInitialPositions" in params:
        ret = [("XAnalyzeInitialPositions","true" if reach else "false")]
        params.difference_update(["analyzeInitialPositions","restrictToReachableStates"])
        return ret
    return []
listOfCommandLineCombinationToClassInstantiationMappers.append(analyzeInitialPositions)

# Counter-strategy extraction
def counterStrategyExtraction(params):
    sysIn = "sysInitRoboticsSemantics" in params
    if "counterStrategy" in params:
        ret = [("XCounterStrategy","true" if sysIn else "false"),("XExtractExplicitCounterStrategy",)]
        params.difference_update(["counterStrategy","sysInitRoboticsSemantics"])
        return ret
    return []
listOfCommandLineCombinationToClassInstantiationMappers.append(counterStrategyExtraction)


# Basic strategy extraction
def basicExtraction(params):
    sc = "simpleRecovery" in params
    if "explicitStrategy" in params:
        sc = "simpleRecovery" in params
        jo = "jsonOutput" in params
        ret = [("XExtractExplicitStrategy","true" if sc else "false","true" if jo else "false")]
        params.difference_update(["simpleRecovery", "jsonOutput"])
    elif "symbolicStrategy" in params:
        ret = [("XExtractSymbolicStrategy","true" if sc else "false","false")]
        params.difference_update(["simpleRecovery"])
    elif "simpleSymbolicStrategy" in params:
        ret = [("XExtractSymbolicStrategy","true" if sc else "false","true")]
        params.difference_update(["simpleRecovery"])
    else:
        ret = []
    params.difference_update(["explicitStrategy", "simpleSymbolicStrategy", "symbolicStrategy"])
    return ret
listOfCommandLineCombinationToClassInstantiationMappers.append(basicExtraction)
    
# Simple Plugins
listOfCommandLineCombinationToClassInstantiationMappers.append(lambda x: simpleInstantiationMapper("cooperativeGR1Strategy","XCooperativeGR1Strategy",x))
listOfCommandLineCombinationToClassInstantiationMappers.append(lambda x: simpleInstantiationMapper("computeIncompleteInformationEstimator","XIncompleteInformationEstimatorSynthesis",x))
listOfCommandLineCombinationToClassInstantiationMappers.append(lambda x: simpleInstantiationMapper("computeAbstractWinningTrace","XAbstractWinningTraceGenerator",x))
listOfCommandLineCombinationToClassInstantiationMappers.append(lambda x: simpleInstantiationMapper("computeInterestingRunOfTheSystem","XComputeInterestingRunOfTheSystem",x))
listOfCommandLineCombinationToClassInstantiationMappers.append(lambda x: simpleInstantiationMapper("analyzeSafetyLivenessInteraction","XAnalyzeSafetyLivenessInteraction",x))
listOfCommandLineCombinationToClassInstantiationMappers.append(lambda x: simpleInstantiationMapper("analyzeAssumptions","XAnalyzeAssumptions",x))
listOfCommandLineCombinationToClassInstantiationMappers.append(lambda x: simpleInstantiationMapper("analyzeInterleaving","XInterleave",x))
listOfCommandLineCombinationToClassInstantiationMappers.append(lambda x: simpleInstantiationMapper("IROSfastslow","XIROSFS",x))
listOfCommandLineCombinationToClassInstantiationMappers.append(lambda x: simpleInstantiationMapper("interactiveStrategy","XInteractiveStrategy",x))
listOfCommandLineCombinationToClassInstantiationMappers.append(lambda x: simpleInstantiationMapper("fixedPointRecycling","XFixedPointRecycling",x))
listOfCommandLineCombinationToClassInstantiationMappers.append(lambda x: simpleInstantiationMapper("computeCNFFormOfTheSpecification","XComputeCNFFormOfTheSpecification",x))
listOfCommandLineCombinationToClassInstantiationMappers.append(lambda x: simpleInstantiationMapper("biasForAction","XBiasForAction",x))
listOfCommandLineCombinationToClassInstantiationMappers.append(lambda x: simpleInstantiationMapper("computeWeakenedSafetyAssumptions","XComputeWeakenedSafetyAssumptions",x))
listOfCommandLineCombinationToClassInstantiationMappers.append(lambda x: simpleInstantiationMapper("sysInitRoboticsSemantics","XRoboticsSemantics",x))
listOfCommandLineCombinationToClassInstantiationMappers.append(lambda x: simpleInstantiationMapper("synthesisProfiling","XSynthesisProfiling",x))

#============================================================
# Sanity checks
#============================================================
# For all combinations, is it known whether they are combinable?
for (a,b) in listOfCommandLineParameters:
    for (c,d) in listOfCommandLineParameters:
        if (a!=c):
            if (not (a,c) in combinableParameters) and (not (c,a) in combinableParameters) and (not (a,c) in uncombinableParameters) and (not (c,a) in uncombinableParameters):
                print >>sys.stderr, "Warning: The combinability of the parameters --"+a+" and --"+c+" is not known."
                

# combinableParameters and uncombinableParameters does not consider any parameters that are not in listOfCommandLineParameters
allParamsStraight = set([a for (a,b) in listOfCommandLineParameters])
for (a,b) in combinableParameters+uncombinableParameters:
    if not a in allParamsStraight:
        print >>sys.stderr,"Typo in combinableParameters or uncombinableParameters: "+a
        sys.exit(1)
    if not b in allParamsStraight:
        print >>sys.stderr,"Typo in combinableParameters or uncombinableParameters: "+b
        sys.exit(1)
del allParamsStraight


#============================================================
# Compute the combinations now
#============================================================
parameterCombinations = []

def recurse(optionsSoFar,remainingCommandLineOptions):

    # Base case
    if len(remainingCommandLineOptions)==0:
    
        # First check if all constraints in "requiredParameters" are satisfied.
        for (condition,constraint) in requiredParameters:
            if condition in optionsSoFar:
                found = False
                for a in constraint:
                    if a in optionsSoFar:
                        found = True
                if not found:
                    # A constraint is not fulfilled
                    return
        
        # Sanity check:            
        # No two parameters may be marked as combinable *and* uncombinable at the same time
        # -> We check that here, so tha the requiredParameters are taken into account.
        for a in optionsSoFar:
            for b in optionsSoFar:
                if (a,b) in combinableParameters or (b,a) in combinableParameters:
                    if (a,b) in uncombinableParameters or (b,a) in uncombinableParameters:
                        print >>sys.stderr,"Two parameters are both combinable and uncombinable: "+a+", "+b
                        sys.exit(1)

        # Obtain the list of instantiations.
        optionsSoFarOrig = optionsSoFar
        optionsSoFar = set(optionsSoFar) # Copy the array to a set
        instantiations = []
        for fn in listOfCommandLineCombinationToClassInstantiationMappers:
            instantiations = instantiations + fn(optionsSoFar)
        # Check if all command line paramters have been "eaten up"
        if len(optionsSoFar)>0:
            print >>sys.stderr, "Error: For the parameter list ", str(optionsSoFar),", the parameters ", str(optionsSoFarOrig)," have not been 'eaten'"
            sys.exit(1)
        
        # For the classes, we order according to 'orderOfPluginClassesInInstantiations'
        # This is a topological sorting.
        orderedInstantiations = []
        while len(instantiations)>0:
            noPriority = False
            for i in xrange(0,len(instantiations)):
                thisOne = True
                for j in xrange(0,len(instantiations)):
                    if i!=j:
                        if (instantiations[j][0],instantiations[i][0]) in orderOfPluginClassesInInstantiations:
                            thisOne = False
                        # Sanity check
                        elif not (instantiations[i][0],instantiations[j][0]) in orderOfPluginClassesInInstantiations:
                            print >>sys.stderr, "Warning: The order of plugin classes",instantiations[j][0],"and",instantiations[i][0],"is not known."

                if thisOne:
                    noPriority = i
            orderedInstantiations.append(instantiations[noPriority])
            instantiations.remove(instantiations[noPriority])
            
        # Build the command
        prefix = ""
        postfix = ""
        for p in orderedInstantiations:
            prefix = prefix + p[0] + "<"
            postfix = ">" + postfix
            if len(p)>1:
                postfix = ","+",".join(p[1:]) + postfix
        
        # Compute the line
        optionsSoFarOrig.sort()
        thisLine = "OptionCombination(\""+" ".join(["--"+a for a in optionsSoFarOrig])+"\","+prefix+"GR1Context"+postfix+"::makeInstance)"
        parameterCombinations.append("    "+thisLine.replace(" >",">")+",")
        return
        
    # No extra options case
    nextOption = remainingCommandLineOptions[0]
    remainingCommandLineOptions = remainingCommandLineOptions[1:]
    recurse(optionsSoFar,remainingCommandLineOptions)
    
    # Add this extra option
    for test in optionsSoFar:
        if (not (test,nextOption) in combinableParameters) and (not (nextOption,test) in combinableParameters):
            # Ok, so we can't add this option. We are done then.
            return

    # The additional parameter is admissible! So we recurse
    recurse(optionsSoFar+[nextOption],remainingCommandLineOptions)

recurse([],[a for (a,b) in listOfCommandLineParameters])
parameterCombinations.sort()

#============================================================
# Read the main.cpp file
#============================================================
oldMainFile = []
with open("main.cpp","r") as mainFileFile:
    for a in mainFileFile.readlines():
        oldMainFile.append(a)
        

#============================================================
# Compute the new main.cpp file
#============================================================
newLines = []
mode = None
for line in oldMainFile:
    if line.strip()=="//-BEGIN-COMMAND-LINE-ARGUMENT-LIST":
        newLines.append(line)
        mode = "Args"
        for (a,b) in listOfCommandLineParameters:
            newLines.append("    \"--"+a+"\",\""+b+"\",\n")
    elif line.strip()=="//-END-COMMAND-LINE-ARGUMENT-LIST":
        newLines.append(line)
        mode = None
    elif line.strip()=="//-BEGIN-OPTION-COMBINATION-LIST":
        newLines.append(line)
        mode = "Combinations"
        for a in parameterCombinations:
            newLines.append(a+"\n")
    elif line.strip()=="//-END-OPTION-COMBINATION-LIST":
        newLines.append(line)
        mode = None
    else:
        if mode==None:
            newLines.append(line)
            
#============================================================
# Write the new main.cpp file
#============================================================
with open("main.cpp","w") as mainFileFile:
    for a in newLines:
        mainFileFile.write(a)


