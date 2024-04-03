#!/usr/bin/python3
#
# Translates a structured specification into an unstructured one that is suitable to be read by the slugs synthesis tool

import math
import os
import sys
import resource
import subprocess
import signal
from Parser import Parser
from re import match

# =====================================================
# Allocate global parser and parser context variables:
# - which APs there are
# - how the numbers are encoded
# =====================================================
p = Parser()
booleanAPs = []
numberAPs = []
numberAPLimits = {}
numberAPNofBits = {}
translatedNames = {}

# =====================================================
# Lexer for the LTL formulas
# =====================================================
def tokenize(str):

    res = []
    while str:
        # Ignoring stuff        
        if str[0].isspace() or (str[0]=='\n'):
            str = str[1:]
            continue

        # Match words
        m = match('[a-zA-Z_.\'@]+[a-zA-Z0-9_.\'@]*', str)
        if m:
            currentSymbol = m.group(0)
            if (currentSymbol in ["X","F","G","U","W","FALSE","TRUE","next","LEASTSIGNIFICANTBITOVERWRITES"]):
                res.append((currentSymbol,))
            else:
                currentSymbol = m.group(0)
                if currentSymbol in booleanAPs:
                    res.append(('boolID', m.group(0)))
                else:
                    res.append(('numID', m.group(0)))
            str = str[m.end(0):]
            continue

        # Match numbers
        m = match('[0-9]+', str)
        if m:
            res.append(('numeral', m.group(0)))
            str = str[m.end(0):]
            continue

        # Single-literal element
        res.append((str[0],))
        str = str[1:]
    return res

# =====================================================
# Simplify the specifications
# =====================================================
def clean_tree(tree):
    """ Cleans a parse Tree, i.e. removes brackets and so on """
    if tree[0] in p.terminals:
        return tree
    if (tree[0]=="Brackets"):
        return clean_tree(tree[2])
    elif (tree[0]=="Implication") and (len(tree)==2):
        return clean_tree(tree[1])
    elif (tree[0]=="Atomic") and (len(tree)==2):
        return clean_tree(tree[1])
    elif (tree[0]=="Conjunction") and (len(tree)==2):
        return clean_tree(tree[1])
    elif (tree[0]=="Biimplication") and (len(tree)==2):
        return clean_tree(tree[1])
    elif (tree[0]=="Disjunction") and (len(tree)==2):
        return clean_tree(tree[1])
    elif (tree[0]=="Xor") and (len(tree)==2):
        return clean_tree(tree[1])
    elif (tree[0]=="LeastSignificantBitOverwriteExpression") and (len(tree)==2):
        return clean_tree(tree[1])
    elif (tree[0]=="BinaryTemporalFormula") and (len(tree)==2):
        return clean_tree(tree[1])
    elif (tree[0]=="BooleanAtomicFormula") and (len(tree)==2):
        return clean_tree(tree[1])
    elif (tree[0]=="BooleanAtomicFormula") and (len(tree)!=2):
        raise Exception("BooleanAtomic formula must have only one successor")
    elif (tree[0]=="UnaryFormula") and (len(tree)==2):
        return clean_tree(tree[1])
    elif (tree[0]=="MultiplicativeNumber") and (len(tree)==2):
        return clean_tree(tree[1])
    elif (tree[0]=="NumberExpression") and (len(tree)==2):
        return clean_tree(tree[1])
    elif (tree[0]=="AtomicNumberExpression"):
        if len(tree)!=2:
            raise ValueError("AtomicNumberExpression must have length 2")
        return clean_tree(tree[1])
    elif (tree[0]=="AtomicFormula"):
        if len(tree)!=2:
            raise ValueError("AtomicFormula must have length 2")
        return clean_tree(tree[1])
    elif (tree[0]=="Implication"):
        return [tree[0],clean_tree(tree[1]),clean_tree(tree[3])]
    elif (tree[0]=="Conjunction"):
        return [tree[0],clean_tree(tree[1]),clean_tree(tree[3])]
    elif (tree[0]=="Biimplication"):
        return [tree[0],clean_tree(tree[1]),clean_tree(tree[3])]
    elif (tree[0]=="Disjunction"):
        return [tree[0],clean_tree(tree[1]),clean_tree(tree[3])]
    elif (tree[0]=="Xor"):
        return [tree[0],clean_tree(tree[1]),clean_tree(tree[3])]
    elif (tree[0]=="BinaryTemporalFormula"):
        return [tree[0],clean_tree(tree[1]),clean_tree(tree[2]),clean_tree(tree[3])]
    elif (tree[0]=="UnaryFormula"):
        return [tree[0],clean_tree(tree[1]),clean_tree(tree[2])]
    elif (tree[0]=="MultiplicativeNumber"):
        return [tree[0],clean_tree(tree[1]),clean_tree(tree[2]),clean_tree(tree[3])]
    elif (tree[0]=="NumberExpression"):
        return [tree[0],clean_tree(tree[1]),clean_tree(tree[2]),clean_tree(tree[3])]
    elif (tree[0]=="BinaryTemporalOperator"):
        # Remove the "superfluous indirection"
        return clean_tree(tree[1])
    elif (tree[0]=="UnaryTemporalOperator"):
        # Remove the "superfluous indirection"
        return clean_tree(tree[1])
    elif (tree[0]=="Assignment"):
        # Flatten "id" case
        A = [tree[0],tree[1][1]]
        A.extend(tree[2:])
        return A
    else:
        A = [tree[0]]
        for x in tree[1:]:
           A.append(clean_tree(x))
        return A

def flatten_as_much_as_possible(tree):
    """ Flattens nested disjunctions/conjunctions """
    # Ground case?
    if len(tree)==1:
        return tree
    if (type(tree)==type("A")) or (type(tree)==type(u"A")): # TODO: How to do this in the way intended?
        return tree
    newTree = []
    for a in tree:
        newTree.append(flatten_as_much_as_possible(a))
    tree = newTree

    # Conjunction
    if (tree[0]=="Conjunction"):
        parts = [tree[0]]
        for a in tree[1:]:
            if a[0]=="Conjunction":
                parts.extend(a[1:])
            else:
                parts.append(a)
        return parts

    # Disjunction
    if (tree[0]=="Disjunction"):
        parts = [tree[0]]
        for a in tree[1:]:
            if a[0]=="Disjunction":
                parts.extend(a[1:])
            else:
                parts.append(a)
        return parts

    # Xor
    if (tree[0]=="Xor"):
        parts = [tree[0]]
        for a in tree[1:]:
            if a[0]=="Xor":
                parts.extend(a[1:])
            else:
                parts.append(a)
        return parts

    # Every other case
    return tree

# =====================================================
# Print Tree function
# =====================================================
def printTree(tree,depth=0):
    if isinstance(tree,str):
        print >>sys.stderr," "*depth+tree
    else:
        print >>sys.stderr," "*depth+tree[0]
        for a in tree[1:]:
            printTree(a,depth+2)


# =====================================================
# The Parsing function
# =====================================================
def parseLTL(ltlTxt,reasonForNotBeingASlugsFormula):

    try:
        input = tokenize(ltlTxt)
        # print >>sys.stderr, input
        tree = p.parse(input)

    except p.ParseErrors as exception:
        print("Offending specification line: ",ltlTxt,file=sys.stderr)
        for t,e in exception.errors:
            if t[0] == p.EOF:
                print("Formula end not expected here",file=sys.stderr)
                continue

            found = repr(t[0])
            print("Error in the property line: "+ltlTxt,file=sys.stderr)
            print("... which could not have been a slugs Polish notation line because of: "+ reasonForNotBeingASlugsFormula,file=sys.stderr)
            print("Could not parse %s, "%found,file=sys.stderr)
            print("Wanted a token of one of the following forms: "+", ".join([ repr(s) for s in e ]),file=sys.stderr)
        raise

    # Convert to a tree
    cleaned_tree = flatten_as_much_as_possible(clean_tree(tree))
    return cleaned_tree

# =====================================================
# Slugs functions for working with numbers
# This function computes a "memory structure" for the 
# slugs input whose final value is the result of the comparison 
# =====================================================

#------------------------------------------
# Computation Recursion function
# Assumes that every variable starts from 0
#------------------------------------------
def recurseCalculationSubformula(tree,memoryStructureParts, isPrimed):
    if (tree[0]=="NumberExpression"):
        assert len(tree)==4 # Everything else would have been filtered out already
        part1MemoryStructurePointers = recurseCalculationSubformula(tree[1],memoryStructureParts, isPrimed)        
        part2MemoryStructurePointers = recurseCalculationSubformula(tree[3],memoryStructureParts, isPrimed)  

        # Addition? 
        if tree[2][0]=="AdditionOperator":
            if len(part1MemoryStructurePointers)==0: return part2MemoryStructurePointers
            if len(part2MemoryStructurePointers)==0: return part1MemoryStructurePointers
            # Order the result by the number of bits
            if len(part2MemoryStructurePointers)<len(part1MemoryStructurePointers):
                part1MemoryStructurePointers, part2MemoryStructurePointers = part2MemoryStructurePointers, part1MemoryStructurePointers
            startingPosition = len(memoryStructureParts)
            memoryStructureParts.append(["^",part1MemoryStructurePointers[0],part2MemoryStructurePointers[0]])
            memoryStructureParts.append(["&",part1MemoryStructurePointers[0],part2MemoryStructurePointers[0]])
            # First part: Joint part of the word
            for i in range(1,len(part1MemoryStructurePointers)):
                memoryStructureParts.append(["^ ^",part1MemoryStructurePointers[i],part2MemoryStructurePointers[i],"?",str(len(memoryStructureParts)-1)])
                memoryStructureParts.append(["| | &",part1MemoryStructurePointers[i],part2MemoryStructurePointers[i],"& ?",str(len(memoryStructureParts)-2),part1MemoryStructurePointers[i],"& ?",str(len(memoryStructureParts)-2),part2MemoryStructurePointers[i]])
           
            # Second part: Part of the word where j1 is shorter than j2
            for i in range(len(part1MemoryStructurePointers),len(part2MemoryStructurePointers)):
                memoryStructureParts.append(["^",part2MemoryStructurePointers[i],"?",str(len(memoryStructureParts)-1)])
                memoryStructureParts.append(["&",part2MemoryStructurePointers[i],"?",str(len(memoryStructureParts)-2)])

            # Return new value including the final bit
            return ["? "+str(i*2+startingPosition) for i in range(0,len(part2MemoryStructurePointers))]+["? "+str(len(memoryStructureParts)-1)]

        # Subtraction?
        elif tree[2][0]=="SubtractionOperator":
            raise Exception("Subtraction is currently unsupported due to semantic difficulties")
        else:
            raise Exception("Found unsupported NumberExpression operator:"+tree[2][0])

    # Parse Numeral
    elif (tree[0]=="numeral"): 
        parameter = int(tree[1])
        result = []
        while parameter != 0:
            if (parameter % 2)==1:
                result.append("1")
            else:
                result.append("0")
            parameter = parameter // 2
        return result

    # Work on NumID
    elif (tree[0]=="numID"):
        apName = tree[1]
        primedLocally = apName[len(apName)-1]=="'"        
        if primedLocally and isPrimed:
            raise Exception("Variable is used primed in the scope of a next-operator, which is not supported: "+apName)
        if primedLocally:
            apName = apName[0:len(apName)-1]
        if (not primedLocally) and (not isPrimed):
            return translatedNames[apName]
        else:
            return [a+"'" for a in translatedNames[apName]]

    elif (tree[0]=="NumberBrackets"):
        # print >>sys.stderr,tree
        assert tree[1]==('(',)
        assert tree[3]==(')',)
        return recurseCalculationSubformula(tree[2],memoryStructureParts, isPrimed)

    # Overwrite the least significant bits of some expression
    elif tree[0]=="LeastSignificantBitOverwriteExpression":
        part1MemoryStructurePointers = recurseCalculationSubformula(tree[1],memoryStructureParts, isPrimed)        
        part2MemoryStructurePointers = recurseCalculationSubformula(tree[3],memoryStructureParts, isPrimed)  
        assert len(part1MemoryStructurePointers)<len(part2MemoryStructurePointers)
        return part1MemoryStructurePointers+part2MemoryStructurePointers[len(part1MemoryStructurePointers):]

        
    else:
        raise Exception("Found currently unsupported calculator subformula type:"+tree[0])

#-----------------------------------------------
# Special function that implicitly adds the lower
# bounds to all variable occurrences. In this
# way, it does not have to be considered in the
# actual translation algorithm.
#-----------------------------------------------
def addMinimumValueToAllVariables(tree):
    if tree[0]=="numID":
        apName = tree[1]
        primed = apName[len(apName)-1]=="'"        
        if primed:
            apName = apName[0:len(apName)-1]
        (minimum,maximum) = numberAPLimits[apName]
        if minimum==0:
            return tree
        else:
            return ("NumberExpression",tree,("AdditionOperator",),("numeral",str(minimum)))
    elif tree[0] in p.terminals:
        return tree
    else:
        return tuple([tree[0]] + [addMinimumValueToAllVariables(a) for a in tree[1:]])

#-----------------------------------------------
# Main Function. Takes the formula tree and adds
#-----------------------------------------------
def computeCalculationSubformula(tree, isPrimed):
    memoryStructureParts = []
    part1MemoryStructurePointers = recurseCalculationSubformula(addMinimumValueToAllVariables(tree[1]),memoryStructureParts, isPrimed)
    part2MemoryStructurePointers = recurseCalculationSubformula(addMinimumValueToAllVariables(tree[3]),memoryStructureParts, isPrimed)
    # print >>sys.stderr,"P1: "+str(part1MemoryStructurePointers)
    # print >>sys.stderr,"P2: "+str(part2MemoryStructurePointers)
    # print >>sys.stderr,"MSPatComp: "+str(memoryStructureParts)

    # Pick the correct comparison operator
    # ->    Greater or Greater-Equal
    if (tree[2][1][0]=="GreaterOperator") or (tree[2][1][0]=="GreaterEqualOperator"):
        thisParts = ["0"] if tree[2][1][0]=="GreaterOperator" else ["1"]
        for i in range(0,min(len(part1MemoryStructurePointers),len(part2MemoryStructurePointers))):
            thisParts = ["|","&",part1MemoryStructurePointers[i],"!",part2MemoryStructurePointers[i],"& | !",part2MemoryStructurePointers[i],part1MemoryStructurePointers[i]]+thisParts
        for i in range(len(part1MemoryStructurePointers),len(part2MemoryStructurePointers)):
            thisParts = ["& !",part2MemoryStructurePointers[i]]+thisParts
        for i in range(len(part2MemoryStructurePointers),len(part1MemoryStructurePointers)):
            thisParts = ["|",part1MemoryStructurePointers[i]]+thisParts
        memoryStructureParts.append(thisParts)

    # ->    Smaller or Smaller-Equal
    elif (tree[2][1][0]=="SmallerOperator") or (tree[2][1][0]=="SmallerEqualOperator"):
        thisParts = ["0"] if tree[2][1][0]=="SmallerOperator" else ["1"]
        for i in range(0,min(len(part1MemoryStructurePointers),len(part2MemoryStructurePointers))):
            thisParts = ["|","& !",part1MemoryStructurePointers[i],part2MemoryStructurePointers[i],"& |",part2MemoryStructurePointers[i],"!",part1MemoryStructurePointers[i]]+thisParts
        for i in range(len(part2MemoryStructurePointers),len(part1MemoryStructurePointers)):
            thisParts = ["& !",part1MemoryStructurePointers[i]]+thisParts
        for i in range(len(part1MemoryStructurePointers),len(part2MemoryStructurePointers)):
            thisParts = ["|",part2MemoryStructurePointers[i]]+thisParts
        memoryStructureParts.append(thisParts)

    # ->    Equal Operator or Unequal Operator
    elif (tree[2][1][0]=="EqualOperator") or (tree[2][1][0]=="UnequalOperator"):
        thisParts = ["1"]
        for i in range(0,min(len(part1MemoryStructurePointers),len(part2MemoryStructurePointers))):
            thisParts = ["&","! ^",part1MemoryStructurePointers[i],part2MemoryStructurePointers[i]]+thisParts
        for i in range(len(part2MemoryStructurePointers),len(part1MemoryStructurePointers)):
            thisParts = ["& !",part1MemoryStructurePointers[i]]+thisParts
        for i in range(len(part1MemoryStructurePointers),len(part2MemoryStructurePointers)):
            thisParts = ["& !",part2MemoryStructurePointers[i]]+thisParts
        if (tree[2][1][0]=="UnequalOperator"):
            memoryStructureParts.append(["!"]+thisParts)
        else:
            memoryStructureParts.append(thisParts)

    else:
        raise Exception("Found unsupported Number Comparison operator:"+tree[2][1][0])
    
    # Return memory structure
    return ["$",str(len(memoryStructureParts))] + [b for a in memoryStructureParts for b in a]

# ============================================
# Build Slugs file - Temporal logic properties
# ============================================
def parseSimpleFormula(tree, isPrimed):
    if (tree[0]=="Formula"):
        assert len(tree)==2
        return parseSimpleFormula(tree[1],isPrimed)
    if (tree[0]=="Biimplication"):
        b1 = parseSimpleFormula(tree[1],isPrimed)
        b2 = parseSimpleFormula(tree[2],isPrimed)
        return ["|","&","!"]+b1+["!"]+b2+["&"]+b1+b2
    if (tree[0]=="Implication"):
        b1 = parseSimpleFormula(tree[1],isPrimed)
        b2 = parseSimpleFormula(tree[2],isPrimed)
        return ["|","!"]+b1+b2
    if (tree[0]=="Conjunction"):
        ret = parseSimpleFormula(tree[1],isPrimed)
        for a in tree[2:]:
            ret = ["&"]+ret+parseSimpleFormula(a,isPrimed)
        return ret
    if (tree[0]=="Disjunction"):
        ret = parseSimpleFormula(tree[1],isPrimed)
        for a in tree[2:]:
            ret = ["|"]+ret+parseSimpleFormula(a,isPrimed)
        return ret
    if (tree[0]=="UnaryFormula"):
        if tree[1][0]=="NotOperator":
            return ["!"]+parseSimpleFormula(tree[2],isPrimed)
        elif tree[1][0]=="NextOperator":
            if isPrimed:
                raise "Nested nexts are not allowed."
            return parseSimpleFormula(tree[2],True)
    if (tree[0]=="Assignment"):
        var = tree[1]
        if isPrimed:
            if "'" in var:
                raise Exception("Cannot parse input formula: variable is both primed and in the scope of a next-operator")
            var = var + "'"
        return [var]
    if (tree[0]=="TRUE"):
        return ["1"]
    if (tree[0]=="FALSE"):
        return ["0"]
    if (tree[0]=="CalculationSubformula"):
        assert len(tree)==4
        return computeCalculationSubformula(tree,isPrimed)
    if (tree[0]=="BinaryTemporalFormula") or (tree[0]=="UnaryTemporalFormula"):
        raise Exception("Cannot parse input formula: Only GR(1) specification parts are supported by Slugs and the structured Slugs compiler - no temperal operators such as 'G', 'F', 'U', and 'W' can be used.")
    print("Cannot parse sub-tree!",file=sys.stderr)
    print(tree,file=sys.stderr)
    raise Exception("Slugs parsing error")
    

def translateToSlugsFormat(tree):
    tokens = parseSimpleFormula(tree,False)
    # print >>sys.stderr,tokens
    return " ".join(tokens)


# ============================================
# Function to check if an input line is already
# in slugs internal form. Checks that there
# will be one element on the stack left when
# applying the operations from right to left
# ============================================
def isValidRecursiveSlugsProperty(tokens):
    tokens = [a for a in tokens if a!=""]
    if "$" in tokens:
        return (True,"Found a '$' in the property.")
    stacksize = 0
    for i in range(len(tokens)-1,-1,-1):
        currentToken = tokens[i]
        if currentToken=="|" or currentToken=="&" or currentToken=="^":
            if stacksize<2:
                return (False,"Rejected part due to stack underflow")
            stacksize -= 1
        elif currentToken=="!":
            pass
        elif currentToken=="1" or currentToken=="0":
            stacksize += 1
        else:
            # Check if valid input or output bit
            if currentToken[len(currentToken)-1] == "'":
                currentToken = currentToken[0:len(currentToken)-1]
            if currentToken in booleanAPs:
                stacksize += 1
            elif currentToken=="0" or currentToken=="1":
                stacksize += 1
            else:
                return (False,"Rejected part \""+tokens[i]+"\" when reading right-to-left.")
    return (stacksize==1,"Stack size at end: "+str(stacksize))

# ============================================
# Main worker
# ============================================
def performConversion(inputFile,thoroughly):
    specFile = open(inputFile,"r")
    mode = ""
    lines = {"[ENV_TRANS]":[],"[ENV_INIT]":[],"[INPUT]":[],"[OUTPUT]":[],"[SYS_TRANS]":[],"[SYS_INIT]":[],"[ENV_LIVENESS]":[],"[SYS_LIVENESS]":[],"[OBSERVABLE_INPUT]":[],"[UNOBSERVABLE_INPUT]":[],"[CONTROLLABLE_INPUT]":[],"[MOTION STATE OUTPUT]":[],"[MOTION CONTROLLER OUTPUT]":[],"[OTHER OUTPUT]":[],"[HELPER_BDDS]":[] }

    for line in specFile.readlines():
        line = line.strip()
        if line.startswith("["):
            mode = line
            # if not mode in lines:
            #    lines[mode] = []
        else:
            if mode=="" and line.startswith("#"):
                # Initial comments
                pass
            elif mode!="":
                lines[mode].append(line)

    specFile.close()

    # ---------------------------------------    
    # Reparse input lines
    # Create information along the way that
    # encodes the possible values
    # ---------------------------------------    
    translatedIOLines = {"[INPUT]":[],"[OUTPUT]":[],"[OBSERVABLE_INPUT]":[],"[UNOBSERVABLE_INPUT]":[],"[CONTROLLABLE_INPUT]":[],"[MOTION STATE OUTPUT]":[],"[MOTION CONTROLLER OUTPUT]":[],"[OTHER OUTPUT]":[],"[HELPER_BDDS]":[]}
    
    # First: Encoded BDDs
    for line in lines["[HELPER_BDDS]"]:
        if line=="" or line.startswith("#"):
            translatedIOLines["[HELPER_BDDS]"].append(line.strip())
        else:
            assert line.find(" ")!=-1
            apName = line[0:line.find(" ")]    
            booleanAPs.append(apName)
            booleanAPs.append(apName+"'")
            translatedIOLines["[HELPER_BDDS]"].append(line)
    
    # Then: The other input/output variables
    for variableType in ["[INPUT]","[OUTPUT]","[OBSERVABLE_INPUT]","[UNOBSERVABLE_INPUT]","[CONTROLLABLE_INPUT]","[MOTION STATE OUTPUT]","[MOTION CONTROLLER OUTPUT]","[OTHER OUTPUT]"]: 
        for line in lines[variableType]:
            if line=="" or line.startswith("#"):
                translatedIOLines[variableType].append(line.strip())
            elif "'" in line:
                print("Error with atomic signal name "+line+": the name must not contain any \"'\" characters",file=sys.stderr)
                raise Exception("Translation error")
            elif "@" in line:
                print("Error with atomic signal name "+line+": the name must not contain any \"@\" characters",file=sys.stderr)
                raise Exception("Translation error")
            elif ":" in line:
                parts = line.split(":")
                parts = [a.strip() for a in parts]
                if len(parts)!=2:
                    print("Error reading line '"+line+"' in section "+variableType+": Too many ':'s!",file=sys.stderr)
                    raise Exception("Failed to translate file.")
                parts2 = parts[1].split("...")
                if len(parts2)!=2:
                    print("Error reading line '"+line+"' in section "+variableType+": Syntax should be name:from...to, where the latter two are numbers",file=sys.stderr)
                    raise Exception("Failed to translate file.")
                try:
                    minValue = int(parts2[0])
                    maxValue = int(parts2[1])
                except ValueError:
                    print("Error reading line '"+line+"' in section "+variableType+": the minimal and maximal values are not given as numbers",file=sys.stderr)
                    raise Exception("Failed to translate file.")
                if minValue>maxValue:
                    print("Error reading line '"+line+"' in section "+variableType+": the minimal value should be smaller than the maximum one (or at least equal)",file=sys.stderr)
                    raise Exception("Failed to translate file.")
                
                # Fill the dictionaries numberAPLimits, translatedNames with information
                variable = parts[0]
                numberAPs.append(parts[0])
                numberAPs.append(parts[0]+"'")
                numberAPLimits[parts[0]] = (minValue,maxValue)
                nofBits = 0
                while (2**nofBits <= (maxValue-minValue)):
                    nofBits += 1
                numberAPNofBits[variable] = nofBits
                # Translate name into bits in a way such that the first bit carries not only the original name, but also min and max information
                translatedNames[parts[0]] = [parts[0]+"@"+str(i)+("."+str(minValue)+"."+str(maxValue) if i==0 else "") for i in range(0,nofBits)]
                translatedIOLines[variableType] = translatedIOLines[variableType] + translatedNames[parts[0]]
                booleanAPs.extend(translatedNames[parts[0]])

                # Define limits
                limitDiff = maxValue - minValue + 1 # +1 because the range is inclusive 
                if (2**numberAPNofBits[variable]) != limitDiff:

                    propertyDestination = "ENV" if variableType.endswith("INPUT]") else "SYS"
                    # Init constraint
                    tokens = ["0"]
                    for i in range(0,numberAPNofBits[variable]):
                        if 2**i & limitDiff:
                            tokens = ["| !",translatedNames[variable][i]]+tokens
                        else:
                            tokens = ["& !",translatedNames[variable][i]]+tokens
                    lines["["+propertyDestination+"_INIT]"].append("## Variable limits: "+str(minValue)+"<="+variable+"<="+str(maxValue))
                    lines["["+propertyDestination+"_INIT]"].append(" ".join(tokens))

                    # Transition constraint for previous state -- only if using the "--thorougly mode"
                    if thoroughly:
                        lines["["+propertyDestination+"_TRANS]"].append("## Variable limits: "+str(minValue)+"<="+variable+"<="+str(maxValue))
                        lines["["+propertyDestination+"_TRANS]"].append(" ".join(tokens))

                    # Trans constraint for next states
                    tokens = ["0"]
                    for i in range(0,numberAPNofBits[variable]):
                        if 2**i & limitDiff:
                            tokens = ["| !",translatedNames[variable][i]+"'"]+tokens
                        else:
                            tokens = ["& !",translatedNames[variable][i]+"'"]+tokens
                    lines["["+propertyDestination+"_TRANS]"].append("## Variable limits: "+str(minValue)+"<="+variable+"'<="+str(maxValue))
                    lines["["+propertyDestination+"_TRANS]"].append(" ".join(tokens))

            else:
                # A "normal" atomic proposition
                line = line.strip()
                booleanAPs.append(line)
                booleanAPs.append(line+"'")
                translatedIOLines[variableType].append(line)

    # ---------------------------------------    
    # Output new input/output lines
    # ---------------------------------------    
    for variableType in ["[MOTION STATE OUTPUT]","[MOTION CONTROLLER OUTPUT]","[INPUT]","[OUTPUT]","[OBSERVABLE_INPUT]","[UNOBSERVABLE_INPUT]","[CONTROLLABLE_INPUT]","[OTHER OUTPUT]","[HELPER_BDDS]"]: 
        if len(translatedIOLines[variableType])>0:
            print(variableType)
            for a in translatedIOLines[variableType]:
                print(a)
            print("")

    # ---------------------------------------    
    # Go through the properties and translate
    # ---------------------------------------    
    for propertyType in ["[ENV_TRANS]","[ENV_INIT]","[SYS_TRANS]","[SYS_INIT]","[ENV_LIVENESS]","[SYS_LIVENESS]"]:
        if len(lines[propertyType])>0:
            print(propertyType)

            # Test for conformance with recursive definition
            for a in lines[propertyType]:
                # print >>sys.stderr, a.strip().split(" ")
                if (len(a.strip())==0) or a.strip()[0:1] == "#":
                    print(a)
                else:
                    (isSlugsFormula,reasonForNotBeingASlugsFormula) = isValidRecursiveSlugsProperty(a.strip().split(" "))
                    if isSlugsFormula:
                        print(a)
                    else:
                        # print >>sys.stderr,a
                        # Try to parse!
                        tree = parseLTL(a,reasonForNotBeingASlugsFormula)            
                        # printTree(tree)
                        currentLine = translateToSlugsFormat(tree)
                        print(currentLine)
            print("")
        



# ==================================
# Entry point
# ==================================
if __name__ == "__main__":
    if len(sys.argv)<2:
        print("Error: Need input file parameter",file=sys.stderr)
        sys.exit(1)

    inputFile = None
    thoroughly = False
    for parameter in sys.argv[1:]:
        if parameter.startswith("-"):
            if parameter=="--thorougly":
                thoroughly = True
            else:
                print("Error: did not understand parameter '"+parameter+"'",file=sys.stderr)
                sys.exit(1)
        else:
            if inputFile!=None:
                print("Error: more than one file name given.",file=sys.stderr)
                sys.exit(1)
            inputFile = parameter

    try:
        resource.setrlimit(resource.RLIMIT_STACK, (2**29,-1))
    except ValueError:
        pass # Cannot increase limit
    sys.setrecursionlimit(10**6)
    performConversion(inputFile,thoroughly)
    # print >>sys.stderr, translatedNames


