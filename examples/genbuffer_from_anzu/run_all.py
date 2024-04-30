#!/usr/bin/env python3
import os, sys
import glob

allInputFiles = glob.glob("*.structuredslugs")

for inputFile in allInputFiles:
  base = inputFile[0:-1*len(".structuredslugs")]
  if len(sys.argv)==1 or base in sys.argv[1:] or inputFile in sys.argv[1:]:
    print("Processing: ",base)
    assert os.system("../../tools/StructuredSlugsParser/compiler.py "+base+".structuredslugs > "+base+".slugsin")==0
    assert os.system("../../src/slugs "+base+".slugsin > /tmp/resultslugs.txt 2>&1")==0
    with open("/tmp/resultslugs.txt","r") as inFile:
      allLines = [a.strip() for a in inFile.readlines()]
    if allLines.count("RESULT: Specification is realizable."):
      print("Realizable")
      foundInvariantNumber = False
      currentInvariantNumber = 0
      negativeExamplesCarriedOver = []
      while not foundInvariantNumber:
        print("Carrying over negative examples:",len(negativeExamplesCarriedOver))
      
        foundInvariantNumber = True
        # --computeInvariantsDontCare 
        print("Execute: ","../../src/slugs --computeInvariants "+base+".slugsin ../../src/satSolver.py "+str(currentInvariantNumber)+" > "+base+".invariant 2>&1")
        assert os.system("../../src/slugs --computeInvariants "+base+".slugsin ../../src/satSolver.py "+str(currentInvariantNumber)+" " + " ".join(negativeExamplesCarriedOver) + " > "+base+".invariant 2>&1")==0
        with open(base+".invariant","r") as inFile:
          allLines = inFile.readlines()
          for line in allLines:
            if line.startswith("Result: Cannot find"):
              foundInvariantNumber = False
              currentInvariantNumber += 1
            elif line.startswith("New negative example "):
              negativeExamplesCarriedOver.append(line.split(":")[1].strip())

    else:
      print("Unrealizable")
  
