#!/usr/bin/env python2
#
# Interactive Strategy Simulator and Debugger for Slugs
import curses, sys, subprocess


# ==================================
# Constants
# ==================================
# Max size of any number in a run. Used to limit the column width
MAX_OVERALL_NUMBER = 999999

# Trace element description:
# 0: chosen by the computer
# 1: chosen by the user
# 2: value forced by the safety assumptions and guarantees
# 3: value forced by the safety assumptions and guarantees and the values chosen by the user
#
# The types must be numbered such that taking the minimum of different values for different bits (except for edited_by_hand) gives the correct labelling for a composite value obtained by merging the bits to an integer value. 
CHOSEN_BY_COMPUTER = 0
EDITED_BY_HAND = 1
FORCED_VALUE_ASSUMPTIONS = 2
FORCED_VALUE_ASSUMPTIONS_AND_GUARANTEES = 3
FORCED_VALUE_ASSUMPTIONS_AND_STRATEGY = 4


# ==================================
# Check parameters
# ==================================
if len(sys.argv)<2:
    print >>sys.stderr, "Error: Need Slugsin file as parameter. Additional parameters are optional"
    sys.exit(1)
specFile = " ".join(sys.argv[1:])


# ==================================
# Start slugs
# ==================================
slugsLink = sys.argv[0][0:sys.argv[0].rfind("cursesSimulator.py")]+"../src/slugs"
slugsProcess = subprocess.Popen(slugsLink+" --interactiveStrategy "+specFile, shell=True, bufsize=1048000, stdin=subprocess.PIPE, stdout=subprocess.PIPE)

# Get input APs
slugsProcess.stdin.write("XPRINTINPUTS\n")
slugsProcess.stdin.flush()
slugsProcess.stdout.readline() # Skip the prompt
lastLine = " "
inputAPs = []
while (lastLine!=""):
    lastLine = slugsProcess.stdout.readline().strip()
    if lastLine!="":
        inputAPs.append(lastLine)

# Get output APs
slugsProcess.stdin.write("XPRINTOUTPUTS\n")
slugsProcess.stdin.flush()
slugsProcess.stdout.readline() # Skip the prompt
lastLine = " "
outputAPs = []
while (lastLine!=""):
    lastLine = slugsProcess.stdout.readline().strip()
    if lastLine!="":
        outputAPs.append(lastLine)



# ==================================
# Parse input and output bits into structured form
# ==================================
structuredVariables = []
structuredVariablesBitPositions = []
structuredVariablesMin = []
structuredVariablesMax = []
structuredVariablesIsOutput = []

for (isOutput,source,startIndex) in [(False,inputAPs,0),(True,outputAPs,len(inputAPs))]:
    # First pass: Find the limits of all integer variables
    for i,a in enumerate(source):
        if "@" in a:
            # is Structured
            (varName,suffix) = a.split("@")
            if "." in suffix:
                # Is a master variable
                (varNum,minimum,maximum) = suffix.split(".")
                assert varNum=="0"
                structuredVariables.append(varName)    
                structuredVariablesBitPositions.append({0:i+startIndex})
                structuredVariablesMin.append(int(minimum))
                structuredVariablesMax.append(int(maximum))
                structuredVariablesIsOutput.append(isOutput)

    # Second pass: parse all other variables
    for i,a in enumerate(source):
        if "@" in a:
            (varName,suffix) = a.split("@")
            if not "." in suffix:
                # Is a slave variable
                indexFound = False
                for j,b in enumerate(structuredVariables):
                    if b==varName:
                        indexFound=j
                if indexFound==None:
                    print >>sys.stderr,"Error in input instance: Master variables have to occur before the slave variables in the input file.\n"
                    sys.exit(1)
                assert structuredVariablesIsOutput[indexFound]==isOutput
                structuredVariablesBitPositions[indexFound][int(suffix)] = i+startIndex
        else:
            # is Unstructured
            structuredVariables.append(a)    
            structuredVariablesBitPositions.append({0:i+startIndex})
            structuredVariablesMin.append(0)
            structuredVariablesMax.append(1)
            structuredVariablesIsOutput.append(isOutput)


# ===============================================
# Translating between structured positions/states
# and the state/position representations that
# slugs needs 
# ===============================================
def computeBinarySlugsStringFromStructuredLabeledTraceElementsForcedElements(traceElement):
    result = {}
    for i,name in enumerate(structuredVariables):
        (chosenValue,assignmentType) = traceElement[i]
        encodedValue = chosenValue-structuredVariablesMin[i]
        for (a,b) in structuredVariablesBitPositions[i].iteritems():
            if assignmentType!=EDITED_BY_HAND:
                result[b] = '.'
            elif (encodedValue & (1 << a))>0:
                result[b] = '1'
            else:
                result[b] = '0'
    result = "".join([result[a] for a in xrange(0,len(result))])
    return result

def computeBinarySlugsStringFromStructuredLabeledTraceElementsAllElements(traceElement):
    result = {}
    for i,name in enumerate(structuredVariables):
        (chosenValue,assignmentType) = traceElement[i]
        encodedValue = chosenValue-structuredVariablesMin[i]
        for (a,b) in structuredVariablesBitPositions[i].iteritems():
            if (encodedValue & (1 << a))>0:
                result[b] = '1'
            else:
                result[b] = '0'
    result = "".join([result[a] for a in xrange(0,len(result))])
    return result


def parseBinaryStateTupleIntoStructuredTuple(structuredTuple):
    result = []
    for i,name in enumerate(structuredVariables):
        thisOne = structuredVariablesMin[i]
        types = set([])
        for (a,b) in structuredVariablesBitPositions[i].iteritems():
            # print >>sys.stderr,(a,b)
            # print >>sys.stderr,(structuredTuple)
            if structuredTuple[b]=="A":
                thisOne += 1 << a
                types.add(FORCED_VALUE_ASSUMPTIONS)
            elif structuredTuple[b]=="a":
                types.add(FORCED_VALUE_ASSUMPTIONS)
            elif structuredTuple[b]=="G":
                thisOne += 1 << a
                types.add(FORCED_VALUE_ASSUMPTIONS_AND_GUARANTEES)
            elif structuredTuple[b]=="g":
                types.add(FORCED_VALUE_ASSUMPTIONS_AND_GUARANTEES)
            elif structuredTuple[b]=="S":
                thisOne += 1 << a
                types.add(FORCED_VALUE_ASSUMPTIONS_AND_STRATEGY)
            elif structuredTuple[b]=="s":
                types.add(FORCED_VALUE_ASSUMPTIONS_AND_STRATEGY)
            elif structuredTuple[b]=="1":
                thisOne += 1 << a
                types.add(CHOSEN_BY_COMPUTER)
            elif structuredTuple[b]=="0":
                types.add(CHOSEN_BY_COMPUTER)            
            else:
                print >>sys.stderr, "Error: Found literal ",structuredTuple[b]," in structured Tuple"
                assert False
        result.append((thisOne,min(types)))
    return result

# ==================================
# Prepare visualization
# ==================================
print "Out:",structuredVariables
print "Out:",structuredVariablesBitPositions
print "Out:",structuredVariablesMin
print "Out:",structuredVariablesMax
print "Out:",structuredVariablesIsOutput

print "inputAPs:",inputAPs
print "outputAPs:",outputAPs

maxLenInputOrOutputName = 15 # Minimium size
for a in structuredVariables:
    maxLenInputOrOutputName = max(maxLenInputOrOutputName,len(a))
if len(structuredVariables)==0:
    print >>sys.stderr, "Error: No variables found. Cannot run simulator.\n"
    sys.exit(1)


# ==================================
# Get initial state
# ==================================
# slugsProcess.stdin.write("XGETINIT\n")
# slugsProcess.stdin.flush()
# slugsProcess.stdout.readline() # Skip the prompt
# initLine = slugsProcess.stdout.readline().strip()
# currentState = parseBinaryStateTupleIntoStructuredTuple(initLine)


# ==================================
# Initialize Trace
# ==================================
unfixedState = []
for i in xrange(0,len(structuredVariables)):
    unfixedState.append((structuredVariablesMin[i],CHOSEN_BY_COMPUTER))
unfixedState = tuple(unfixedState) # Enforce non-mutability for the rest of this script
trace = [list(unfixedState)] 
traceGoalNumbers = [(0,0)]
traceFlags = [set([])]


# ==================================
# Initialize CURSES
# ==================================
stdscr = curses.initscr()
curses.start_color()
curses.noecho()
stdscr.keypad(1)
curses.init_pair(1, curses.COLOR_RED, curses.COLOR_WHITE)
curses.init_pair(2, curses.COLOR_GREEN, curses.COLOR_BLACK)
curses.init_pair(3, curses.COLOR_YELLOW, curses.COLOR_BLACK)
curses.init_pair(4, curses.COLOR_RED, curses.COLOR_BLACK)
stdscr.refresh()

try:

    # ==================================
    # Main loop
    # ==================================
    cursorInWhichProposition = 0
    cursorEditPosition = None
    helpScreen = 0
    postTrace = [] # When going back to earlier trace elements, forced entries in later trace elements are stored

    while 1:

        # ==============================
        # Update Trace
        # ==============================
        if len(trace)==1:
            # Update initial state whenever we can
            if not "(OOB)" in traceFlags[0]:
                writtenElement = computeBinarySlugsStringFromStructuredLabeledTraceElementsForcedElements(trace[0])
                slugsProcess.stdin.write("XCOMPLETEINIT\n"+writtenElement)
                print >> sys.stderr, "IPRINT: "+"XCOMPLETEINIT\n"+writtenElement+"\n"
                slugsProcess.stdin.flush()
                print >> sys.stderr, "IREAD: "+slugsProcess.stdout.readline() # Skip the prompt
                initLine = slugsProcess.stdout.readline().strip()
                print >> sys.stderr, "INITLINE: "+initLine
                isValidElement = True            
                if (initLine=="FAILASSUMPTIONS"):
                    traceFlags[0].add("A")
                    isValidElement = False
                else:
                    if "A" in traceFlags[0]:
                        traceFlags[0].remove("A")
                if (initLine=="FAILGUARANTEES"):
                    traceFlags[0].add("G")
                    isValidElement = False
                    # Read a new line
                    print >>sys.stderr, "Awaiting position line: "+initLine
                    initLine = slugsProcess.stdout.readline().strip()
                    print >>sys.stderr, "Read position line: "+initLine
                else:
                    if "G" in traceFlags[0]:
                        traceFlags[0].remove("G")
                if (initLine=="FORCEDNONWINNING"):
                    traceFlags[0].add("L")
                    isValidElement = False
                else:
                    if "L" in traceFlags[0]:
                        traceFlags[0].remove("L")
                
                if isValidElement:
                    parsedTraceElement = parseBinaryStateTupleIntoStructuredTuple(initLine)
                    # Merge the computed concretized trace element back into the actual trace
                    for i in xrange(0,len(structuredVariables)):
                        if trace[0][i][1]==EDITED_BY_HAND:
                            assert trace[0][i][0]==parsedTraceElement[i][0]
                        else:
                            trace[0][i] = parsedTraceElement[i]
                
        else:
            # Update non-initial state
            if not "(OOB)" in traceFlags[len(trace)-1]:
                currentElement = computeBinarySlugsStringFromStructuredLabeledTraceElementsAllElements(trace[len(trace)-2])
                successorElement = computeBinarySlugsStringFromStructuredLabeledTraceElementsForcedElements(trace[len(trace)-1])
                dataForStrategyTransition = currentElement+successorElement+"\n"+str(traceGoalNumbers[len(trace)-2][0])+"\n"+str(traceGoalNumbers[len(trace)-2][1])
                slugsProcess.stdin.write("XSTRATEGYTRANSITION\n"+dataForStrategyTransition+"\n")
                print >> sys.stderr, "IPRINT: "+"XSTRATEGYTRANSITION\n"+dataForStrategyTransition+"\n"
                slugsProcess.stdin.flush()
                print >> sys.stderr, "IREAD: "+slugsProcess.stdout.readline() # Skip the prompt
                positionLine = slugsProcess.stdout.readline().strip()
                print >> sys.stderr, "POSILINE: "+positionLine
                isValidElement = True            
                if (positionLine=="FAILASSUMPTIONS"):
                    traceFlags[len(trace)-1].add("A")
                    isValidElement = False
                else:
                    if "A" in traceFlags[len(trace)-1]:
                        traceFlags[len(trace)-1].remove("A")
                if (positionLine=="FAILGUARANTEES"):
                    traceFlags[len(trace)-1].add("G")
                    isValidElement = True
                    # Read a new line
                    print >>sys.stderr, "Awaiting position line: "+positionLine
                    positionLine = slugsProcess.stdout.readline().strip()
                    print >>sys.stderr, "Read position line: "+positionLine
                else:
                    if "G" in traceFlags[len(trace)-1]:
                        traceFlags[len(trace)-1].remove("G")
                if (positionLine=="FORCEDNONWINNING"):
                    traceFlags[len(trace)-1].add("L")
                    isValidElement = False
                else:
                    if "L" in traceFlags[len(trace)-1]:
                        traceFlags[len(trace)-1].remove("L")

                if isValidElement:
                    parsedTraceElement = parseBinaryStateTupleIntoStructuredTuple(positionLine)
                    # Merge the computed concretized trace element back into the actual trace
                    for i in xrange(0,len(structuredVariables)):
                        if trace[len(trace)-1][i][1]==EDITED_BY_HAND:
                            assert trace[len(trace)-1][i][0]==parsedTraceElement[i][0]
                        else:
                            trace[len(trace)-1][i] = parsedTraceElement[i]

                    nextLivenessAssumption = int(slugsProcess.stdout.readline().strip())
                    nextLivenessGuarantee = int(slugsProcess.stdout.readline().strip())
                    traceGoalNumbers[len(trace)-1] = (nextLivenessAssumption,nextLivenessGuarantee)
                    

        # ==============================
        # Draw interface
        # ==============================
        stdscr.clear()
        (ysize,xsize) = stdscr.getmaxyx()

        # Paint border
        initText = "SLUGS Simulator ("
        if len(specFile)>xsize-len(initText)-1:
            initText = initText + "[...]"+specFile[len(specFile)-xsize+len(initText)+6:]
        else:
            initText = initText + specFile
        initText = initText + ")"        
        stdscr.addstr(0, 0, initText+(xsize-min(xsize,len(initText)))*" ",curses.color_pair(1))
        stdscr.addstr(ysize-1, 0, (xsize-1)*" ",curses.color_pair(1))
        stdscr.addstr(ysize-1, 0, "Press (h) for help.",curses.color_pair(1))
        stdscr.insstr(ysize-1, 20, " ",curses.color_pair(1))

        # Main part
        if (xsize<max(72,maxLenInputOrOutputName+46)):
            stdscr.addstr(2, 0, "Terminal is not wide enough!",curses.color_pair(1))
        elif (ysize<max(len(structuredVariables)+13,17)) :
            stdscr.addstr(2, 0, "Terminal is not high enough!",curses.color_pair(1))
        elif helpScreen==1:
            stdscr.addstr(2, 0, "Basic Keys:")
            stdscr.addstr(3, 0, " - (h): Toggle Help")
            stdscr.addstr(4, 0, " - (q): Quit")
            stdscr.addstr(5, 0, " - Cursor keys: Move between the propositions and trace elements")
            stdscr.addstr(6, 0, " - Backspace: Revert forced value to automatically chosen one")
            stdscr.addstr(7, 0, " - Numbers: Enter a value to be enforced")
            stdscr.addstr(9, 0, "Marking semantics:")
            stdscr.addstr(10, 1, "1) Automatically chosen value")
            stdscr.addstr(11, 1, "2) ")
            stdscr.addstr(11, 4, "Manually chosen value", curses.A_UNDERLINE)
            stdscr.addstr(12, 1, "3) ")
            stdscr.addstr(12, 4, "Value that is implied by the safety a's and implied values", curses.color_pair(2))
            stdscr.addstr(13, 1, "4) ")
            stdscr.addstr(13, 4, "Value implied by the safety g's and the cases above", curses.color_pair(3))
            stdscr.addstr(14, 1, "5) ")
            stdscr.addstr(14, 4, "Value implied by the strat' of the winning player & cases above", curses.color_pair(4))
            stdscr.addstr(15, 0, "The order of case 4 and 5 are swapped for unrealizable specifications.")
            stdscr.move(ysize-1,0)
        elif helpScreen==2:
            stdscr.addstr(2, 0, "Flags:")
            stdscr.addstr(3, 0, " - A: Violates Safety or Initialization assumptions")
            stdscr.addstr(4, 0, " - G: Violates Safety or Initialization guarantees")
            stdscr.addstr(5, 0, " - L: Is losing with the forced values for the player that would")
            stdscr.addstr(6, 0, "      normally win")
            stdscr.addstr(7, 0, " - (OOB): Variable value out of bounds (not within its min and max")
            stdscr.addstr(9, 0, "Values are displayed as '?' is due to strategy or property violations")
            stdscr.addstr(10, 0, "(possibly due to forced values), no actual value can be given.")
            stdscr.addstr(12, 0, "Moving on to the next trace element is also only possible when")
            stdscr.addstr(13, 0, "none of the above flags are present.")
            stdscr.move(ysize-1,0)
        else:
            # Print Trace information
            # 1. First column (labels)
            stdscr.addstr(2, 1, "+-"+(maxLenInputOrOutputName)*"-"+"-+")
            stdscr.addstr(3, 1, "| Round"+(maxLenInputOrOutputName-5)*" "+" |")
            stdscr.addstr(4, 1, "+="+(maxLenInputOrOutputName)*"="+"=+")
            currentLine = 5
            currentMode = False
            for i,name in enumerate(structuredVariables):
                if structuredVariablesIsOutput[i] and not currentMode:
                    currentMode = True
                    stdscr.addstr(currentLine, 1, "+="+(maxLenInputOrOutputName)*"="+"=+")
                    currentLine += 1
                stdscr.addstr(currentLine, 1, "| "+name+(maxLenInputOrOutputName-len(name))*" "+" |")
                currentLine += 1
            stdscr.addstr(currentLine, 1, "+="+(maxLenInputOrOutputName)*"="+"=+")
            stdscr.addstr(currentLine+1, 1, "| Env. Goal. Num. "+(maxLenInputOrOutputName-15)*" "+"|")
            stdscr.addstr(currentLine+2, 1, "| Sys. Goal. Num. "+(maxLenInputOrOutputName-15)*" "+"|")
            stdscr.addstr(currentLine+3, 1, "| Flags           "+(maxLenInputOrOutputName-15)*" "+"|")
            stdscr.addstr(currentLine+4, 1, "+-"+(maxLenInputOrOutputName)*"-"+"-+")
            
            # 2. Print a trace elements:
            minTraceElement = max(0,len(trace)-5)
            maxTraceElement = len(trace)
            nofTraceElementsDrawn = maxTraceElement-minTraceElement
            for element in xrange(0,maxTraceElement-minTraceElement):
                # 2.1. Number
                startX = element*8+maxLenInputOrOutputName+5
                stdscr.addstr(2, startX, "-------+")
                stdscr.addstr(3, startX+1, str(element+minTraceElement))
                stdscr.addstr(3, startX+7, "|")
                stdscr.addstr(4, startX, "=======+")
                currentLine = 5
                currentMode = False
                for i,name in enumerate(structuredVariables):
                    if structuredVariablesIsOutput[i] and not currentMode:
                        currentMode = True
                        stdscr.addstr(currentLine, startX, "=======+")
                        currentLine += 1
                    # In case of an error, mask non-forced values
                    if ("A" in traceFlags[element+minTraceElement]) or (("G" in traceFlags[element+minTraceElement]) and structuredVariablesIsOutput[i]) or ("L" in traceFlags[element+minTraceElement]):
                        if trace[element+minTraceElement][i][1]==EDITED_BY_HAND:
                            stdscr.addstr(currentLine, startX+1, str(trace[element+minTraceElement][i][0]), curses.A_UNDERLINE)
                        else:
                            stdscr.addstr(currentLine, startX+1, "?") 
                    else:
                        if trace[element+minTraceElement][i][1]==CHOSEN_BY_COMPUTER:
                            stdscr.addstr(currentLine, startX+1, str(trace[element+minTraceElement][i][0]))
                        elif trace[element+minTraceElement][i][1]==EDITED_BY_HAND:
                            stdscr.addstr(currentLine, startX+1, str(trace[element+minTraceElement][i][0]), curses.A_UNDERLINE)
                        elif trace[element+minTraceElement][i][1]==FORCED_VALUE_ASSUMPTIONS:
                            stdscr.addstr(currentLine, startX+1, str(trace[element+minTraceElement][i][0]), curses.color_pair(2))
                        elif trace[element+minTraceElement][i][1]==FORCED_VALUE_ASSUMPTIONS_AND_GUARANTEES:
                            stdscr.addstr(currentLine, startX+1, str(trace[element+minTraceElement][i][0]), curses.color_pair(3))
                        elif trace[element+minTraceElement][i][1]==FORCED_VALUE_ASSUMPTIONS_AND_STRATEGY:
                            stdscr.addstr(currentLine, startX+1, str(trace[element+minTraceElement][i][0]), curses.color_pair(4))
                    stdscr.addstr(currentLine, startX+7, "|") 
                    currentLine += 1
                stdscr.addstr(currentLine, startX, "=======+")

                # 2.2. Print Goal numbers and Flags
                stdscr.addstr(currentLine+1, startX+1, str(traceGoalNumbers[element+minTraceElement][0]))
                stdscr.addstr(currentLine+1, startX+7, "|")
                stdscr.addstr(currentLine+2, startX+1, str(traceGoalNumbers[element+minTraceElement][1]))
                stdscr.addstr(currentLine+2, startX+7, "|")
                stdscr.addstr(currentLine+3, startX+1, "".join(traceFlags[element+minTraceElement]))
                stdscr.addstr(currentLine+3, startX+7, "|")
                stdscr.addstr(currentLine+4, startX, "-------+")

            # 3. Locate cursor
            cursorX = maxLenInputOrOutputName+5+nofTraceElementsDrawn*8-7
            if cursorEditPosition!=None:
                cursorX += cursorEditPosition
            cursorY = 5+cursorInWhichProposition
            if structuredVariablesIsOutput[cursorInWhichProposition]:
                cursorY += 1
            stdscr.move(cursorY, cursorX)             
        
        #=======================
        # Process key presses
        #=======================        
        c = stdscr.getch()

        # 0. Truncate all currently edited numbers to their limits when moving the cursor
        if c==curses.KEY_DOWN or c==curses.KEY_UP or c==curses.KEY_LEFT or c==curses.KEY_RIGHT:
            cursorEditPosition = None
            traceElementBeingEdited = len(trace)-1
            if trace[traceElementBeingEdited][cursorInWhichProposition][0] < structuredVariablesMin[cursorInWhichProposition]:
                trace[traceElementBeingEdited][cursorInWhichProposition] = (structuredVariablesMin[cursorInWhichProposition],CHOSEN_BY_COMPUTER)
            if trace[traceElementBeingEdited][cursorInWhichProposition][0] > structuredVariablesMax[cursorInWhichProposition]:
                trace[traceElementBeingEdited][cursorInWhichProposition] = (structuredVariablesMax[cursorInWhichProposition],CHOSEN_BY_COMPUTER)
            if "(OOB)" in traceFlags[traceElementBeingEdited]:
                traceFlags[traceElementBeingEdited].remove("(OOB)")
        
        # 1. Change proosition selection
        if c == curses.KEY_DOWN:
            if cursorInWhichProposition<len(structuredVariables)-1:
                cursorInWhichProposition += 1
        if c == curses.KEY_UP:
            if cursorInWhichProposition>0:
                cursorInWhichProposition -= 1

        # 2. Change trace element selection
        if c == curses.KEY_RIGHT:
            if len(traceFlags[len(trace)-1])==0:
                if len(postTrace)>0:
                    trace.append(postTrace[0])
                    postTrace = postTrace[1:]
                else:
                    trace.append(list(unfixedState))
                traceGoalNumbers.append((0,0))
                traceFlags.append(set([]))
        if c == curses.KEY_LEFT:
            if len(trace)>1:
                postTrace = [trace[len(trace)-1]]+postTrace
                trace = trace[0:len(trace)-1]
                traceGoalNumbers = traceGoalNumbers[0:len(trace)]
                traceFlags = traceFlags[0:len(trace)]
                

            
                   
        # 3. Numbers and Backspace
        if (c>=ord('0') and c<=ord('9')) or c==curses.KEY_BACKSPACE:
            
            # Only allow editing if no error currently there
            if (trace[element+minTraceElement][cursorInWhichProposition][1]==EDITED_BY_HAND) or not \
              (("A" in traceFlags[element+minTraceElement]) or ("G" in traceFlags[element+minTraceElement]) or ("L" in traceFlags[element+minTraceElement])):

                traceElementBeingEdited = len(trace)-1
                if (c>=ord('0') and c<=ord('9')):    
                    number = c - ord('0')
                    if cursorEditPosition==None:
                        trace[traceElementBeingEdited][cursorInWhichProposition] = (number,EDITED_BY_HAND)
                        cursorEditPosition = 1
                    else:
                        trace[traceElementBeingEdited][cursorInWhichProposition] = (min(MAX_OVERALL_NUMBER,
                              trace[traceElementBeingEdited][cursorInWhichProposition][0]*10+number),EDITED_BY_HAND)
                        cursorEditPosition = len(str(trace[traceElementBeingEdited][cursorInWhichProposition][0]))
                else:
                    if cursorEditPosition==None or trace[traceElementBeingEdited][cursorInWhichProposition][0]==0:
                        trace[traceElementBeingEdited][cursorInWhichProposition] = (structuredVariablesMin[cursorInWhichProposition],CHOSEN_BY_COMPUTER)
                        cursorEditPosition=None
                    else:
                        trace[traceElementBeingEdited][cursorInWhichProposition] = (trace[traceElementBeingEdited][cursorInWhichProposition][0]/10,EDITED_BY_HAND)
                        cursorEditPosition = len(str(trace[traceElementBeingEdited][cursorInWhichProposition][0]))

                # Out of bounds check
                if ((trace[traceElementBeingEdited][cursorInWhichProposition][0] < structuredVariablesMin[cursorInWhichProposition]) or
                   (trace[traceElementBeingEdited][cursorInWhichProposition][0] > structuredVariablesMax[cursorInWhichProposition])):
                    traceFlags[traceElementBeingEdited].add("(OOB)")
                else:
                    if "(OOB)" in traceFlags[traceElementBeingEdited]:
                        traceFlags[traceElementBeingEdited].remove("(OOB)")
        
        # 4. Special keys                        
        if c == ord('q'):
            break  # Exit the while()
        if c == ord('h'):
            helpScreen = (helpScreen+1) % 3




# =====================
# Cleanup Curses
# =====================
finally:
    curses.endwin()

