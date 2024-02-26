#!/usr/bin/python
#
# Creates some benchmarks for an obstacle and a robot in a maze, used for testing the environmental-friendly synthesis extension
# This version: 
# - robot and obstacle can move one step at a time to non-occupied cells
# - the passage in the middle is only one cell wide

import math
import os
import sys
import resource
import subprocess
import signal
import tempfile
import copy


# ==================================
# Configurations, consisting of:
# 1. X Size of the Field  (must be odd)
# 2. Y Size of the Field  
# ==================================
configurations = [(3,2),(3,10),(3,20),(25,2),(63,2)]


# ==================================
# Check if run as intended
# ==================================
if __name__ != "__main__":
    raise Exception("This script is not to be used as a module!")
startingDir = os.path.dirname(sys.argv[0])

# ==================================
# Declare executables
# ==================================
structuredSlugsParserExecutable = startingDir+"../../../tools/StructuredSlugsParser/compiler.py"

# ==================================
# Read parameters
# ==================================
makeAAGBenchmarks = False
if len(sys.argv)>1:
    if sys.argv[1]=="--makeAAGBenchmarks":
        makeAAGBenchmarks = True
    else:
        print >>sys.stderr, "Error: the only parameter supported by this script is '--makeAAGBenchmarks'!"
        sys.exit(1)

# ==================================
# Make a benchmark file
# ==================================
def makeBenchmarkFile(configuration):

    filenamePrefix = "maze_"+str(configuration[0])+"x"+str(configuration[1])
    outFile = open(filenamePrefix+".structuredslugs","w")
    
    linesbytwo=configuration[1]/2
    
    

    text = """
[INPUT]
obsx: 0...%(maxX)d
obsy: 0...%(maxY)d


[OUTPUT]
robx: 0...%(maxX)d
roby: 0...%(maxY)d

[SYS_INIT]
robx = %(maxX)d & roby = 0


[SYS_TRANS]
(robx' <= robx+1) & (roby' <= roby+1) & (robx <= robx'+1) & (roby <= roby'+1) 
(robx < robx' | robx' < robx) -> (roby' = roby)
(roby < roby' | roby' < roby) -> (robx' = robx)
(obsx' = robx') ->  ((obsy' < roby') | (roby'< obsy'))
(obsy' = roby') ->  ((obsx' < robx') | (robx'< obsx'))
(robx <= %(cbytwo)d | %(dbytwo)d <= robx )-> (roby' = roby)


[SYS_LIVENESS]
%(sysLive)s

[ENV_INIT]
obsx=0 & obsy=0

[ENV_TRANS]
(obsx' <= obsx+1) & (obsy' <= obsy+1) & (obsx <= obsx'+1) & (obsy <= obsy'+1) 
(obsx < obsx' | obsx' < obsx) -> (obsy' = obsy)
(obsy < obsy' | obsy' < obsy) -> (obsx' = obsx)
(robx = obsx') -> ( (roby < obsy') | (obsy'< roby) )
(roby = obsy') -> ( (robx < obsx') | (obsx'< robx) )
(robx = obsx) -> ( (roby < obsy) | (obsy< roby) )
(roby = obsy) -> ( (robx < obsx) | (obsx< robx) )
(obsx <= %(cbytwo)d | %(dbytwo)d <= obsx) -> (obsy' = obsy)


[ENV_LIVENESS]
%(envLive)s

""" 
    text = text % {
        'maxX': configuration[0]-1, 'maxY': configuration[1]-1,
        'cbytwo': ((configuration[0]-1)/2)-1,
        'dbytwo': ((configuration[0]-1)/2)+1,
        'sysLive': "\n".join(["robx = 2 & roby = "+str(2*i)+"\nrobx = 0 & roby = "+str(2*i+1) for i in xrange(0,linesbytwo)]),
        'envLive': "\n".join(["obsx = 0 & obsy = "+str(2*i)+"\nobsx = 2 & obsy = "+str(2*i+1) for i in xrange(0,linesbytwo)])
        }
    
    outFile.write(text)
    outFile.close()

    # =====================================================
    # Translate to slugsin
    # =====================================================
    retValue = os.system(structuredSlugsParserExecutable + " " + filenamePrefix+".structuredslugs >  "+filenamePrefix+".slugsin")
    if (retValue!=0):
        print >>sys.stderr, "Structured to Non-structured Slugs Translation failed!"
        raise Exception("Translation Aborted")

    retValue = os.system("( time ../../../src/slugs --explicitStrategy --jsonOutput " + filenamePrefix+".slugsin ) > " +filenamePrefix+"_data_3FP.txt 2>&1")
    if (retValue!=0):
        print >>sys.stderr, "Strategy Extraction 3FP Failed"
        raise Exception("Translation Aborted") 

    retValue = os.system("( time ../../../src/slugs --environmentFriendlyStrategy --jsonOutput " + filenamePrefix+".slugsin ) > " +filenamePrefix+"_data_4FP.txt 2>&1")
    if (retValue!=0):
        print >>sys.stderr, "Strategy Extraction 4FP Failed"
        raise Exception("Extraction Aborted") 

    retValue = os.system("( time ../../../src/slugs --environmentFriendlyStrategy --jsonOutput --useHeuristic " + filenamePrefix+".slugsin ) > " +filenamePrefix+"_data_4FP_Heuristic.txt 2>&1")
    if (retValue!=0):
        print >>sys.stderr, "Strategy Extraction 4FP_Heuristic Failed"
        raise Exception("Extraction Aborted")

# ==================================
# Make files
# ==================================
for a in configurations:
    makeBenchmarkFile(a)


