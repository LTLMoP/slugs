#!/usr/bin/env python3
# A script for checking for a given initial state
# which sys_trans constraints are responsible for making it losing after at most one step. 
import os, sys, tempfile, subprocess, time

def checkRealizability(basepath,parameter):
    '''
    This functions calls a script and looks out for lines stating realizability/unrealizability by Slugs.
    It returns an error message if the subprocess returned with a non-zero errorcode or if multiple results are found.
    Otherwise, the result is True or False.    
    '''
    slugsProcess = subprocess.Popen(basepath+"../src/slugs "+str(parameter), shell=True, bufsize=1048000, stdout=subprocess.PIPE,stderr=subprocess.STDOUT)

    nofRealizableLines = 0
    nofUnrealizableLines = 0
    lastLines = []

    for line in slugsProcess.stdout.readlines():
        line = line.strip().decode("utf-8")
        print("O: ",line)
        if len(lastLines)>100:
            lastLines = lastLines[1:]+[line]
        else:
            lastLines.append(line)
        if line=="RESULT: Specification is realizable.":
            nofRealizableLines +=1 
        elif line=="RESULT: Specification is unrealizable.":
            nofUnrealizableLines +=1 
    
    errorCode = slugsProcess.wait()
    if (errorCode!=0):
        errorMessage = "External tool or script terminated with a non-zero error code: "+str(errorCode)+"\n"+"\n".join(lastLines)
        return errorMessage
    if (nofRealizableLines+nofUnrealizableLines)>1:
        return "Found more than one realizability/unrealizability result!"
    if (nofRealizableLines+nofUnrealizableLines)==0:
        return "Found no realizability/unrealizability result!"
    if nofRealizableLines>0:
        return True
    elif nofUnrealizableLines>0:
        return False
    else:
        raise Exception("Internal error. Should not be able to happen.")
        


# Read parameters
if len(sys.argv)<3:
    print("Error: Need input file (structuredslugs) and initial state",file=sys.stderr)
    sys.exit(1)

inputFile = sys.argv[1]
initialState = sys.argv[2]
basepath =  os.path.realpath(__file__)
basepath = basepath[0:basepath.rfind("/")] + "/"


# READ INPUT FILE
segments = {"ENV_TRANS":[],"SYS_TRANS":[],"ENV_LIVENESS":[],"SYS_LIVENESS":[],"ENV_INIT":[],"SYS_INIT":[],"INPUT":[],"OUTPUT":[]}
currentSegment = ""
for line in open(inputFile,"r").readlines():
    line = line.strip()
    if line.startswith("#") or len(line)==0:
        pass
    elif line.startswith("["):
        currentSegment = line[1:len(line)-1]
    else:
        segments[currentSegment].append(line)

# Perform analysis
with tempfile.TemporaryDirectory() as tmpDir:

    # First, get list of decoded variables
    assert os.system(basepath+"../tools/StructuredSlugsParser/compiler.py "+inputFile+" > "+tmpDir+"/initial.slugsin")==0

    inputAndOutputVarsEncoded = []
    currentSegment = False
    currentOutput = False
    for line in open(tmpDir+"/initial.slugsin","r").readlines():
        line = line.strip()
        if line.startswith("#") or len(line)==0:
            pass
        elif line == "[INPUT]" or line=="[OUTPUT]":
            currentSegment = True
            if line=="[OUTPUT]":
                currentOutput = True
        elif line.startswith("["):
            currentSegment = False
        else:
            if currentSegment:
                inputAndOutputVarsEncoded.append((line,currentOutput))

    # Now translate....
    currentPointerSysTrans = 0
    firstRound = True
    while currentPointerSysTrans<len(segments["SYS_TRANS"]):
        with open(tmpDir+"/try.structuredslugs","w") as outFile:

            # Input/Output
            allVars = []
            outFile.write("[INPUT]\n")
            for a in segments["INPUT"]:
                outFile.write(a)
                outFile.write("\n")
                allVars.append((a,False))
            outFile.write("[OUTPUT]\n")
            for a in segments["OUTPUT"]:
                outFile.write(a)
                outFile.write("\n")
                allVars.append((a,True))
            outFile.write("AFTERFIRSTSTEP\n")

            # AFTERFIRSTSTEP
            outFile.write("[SYS_INIT]\n! AFTERFIRSTSTEP\n")

            # ENV_TRANS and liveness
            for segName in ["ENV_TRANS","SYS_LIVENESS","ENV_LIVENESS"]:
                outFile.write("["+segName+"]\n")
                for a in segments[segName]:
                    outFile.write(a)
                    outFile.write("\n")
            
            # SYS_TRANS
            outFile.write("[SYS_TRANS]\n")
            for i,a in enumerate(segments["SYS_TRANS"]):
                if i<currentPointerSysTrans or i>currentPointerSysTrans:
                    outFile.write("AFTERFIRSTSTEP | ("+a+")\n")
        
        # Now try to translate
        assert os.system(basepath+"../tools/StructuredSlugsParser/compiler.py "+tmpDir+"/try.structuredslugs > "+tmpDir+"/try.slugsin")==0
        
        # Add initial state information
        with open(tmpDir+"/try.slugsin","a") as outFile:
            outFile.write("\n")
            if firstRound:
                print("Initial State:")
            for i,(varname,vartype) in enumerate(inputAndOutputVarsEncoded):
                if vartype:
                    outFile.write("[SYS_INIT]\n")
                else:
                    outFile.write("[ENV_INIT]\n")
                if initialState[i]=="0":
                    outFile.write("! "+varname+"\n")
                    if firstRound:
                        print("! "+varname)
                elif initialState[i]=="1":
                    outFile.write(varname+"\n")
                    if firstRound:
                        print(varname)
                else:
                    print("Error: Initial state contains character other than 0 and 1!",file=sys.stderr)
                    sys.exit(1)
            
            if len(initialState)>len(inputAndOutputVarsEncoded):
                print("Error: Initial state string is too long.",file=sys.stderr)
                sys.exit(1)

        firstRound = False

        realizable = checkRealizability(basepath,tmpDir+"/try.slugsin")

        if realizable is False:
            segments["SYS_TRANS"] = segments["SYS_TRANS"][0:currentPointerSysTrans]+segments["SYS_TRANS"][currentPointerSysTrans+1:]
        elif realizable is True:
            currentPointerSysTrans += 1
        else:
            print("Slugs call failed: ",realizable)
            sys.exit(1)


    print("Done")
    # time.sleep(5000000)

print("================Specification parts needed for this case: ====================")
for a in segments["SYS_TRANS"]:
    print(a)
