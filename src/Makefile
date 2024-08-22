#================================= Slugs main Makefile =====================================

# Definitions
COMPILEROPTIONS = $(shell $(CC) BFAbstractionLibrary/compilerOptionGenerator.c -o /tmp/BFAbstractionCompilerOptionsProducer-$(USER);/tmp/BFAbstractionCompilerOptionsProducer-$(USER))
DEFINES       = -DUSE_CUDD -DNDEBUG -DNBUILD
CFLAGS        = -pipe -O3 -g -mtune=native $(COMPILEROPTIONS) -Wall -W -fPIC $(DEFINES)
CXXFLAGS      = -pipe -O3 -g -std=c++11 -mtune=native $(COMPILEROPTIONS) -fPIC $(DEFINES)
INCPATH       = -I. -I../lib/ -I../lib/cudd-3.0.0/ -I../lib/cudd-3.0.0/cudd -I../lib/cudd-3.0.0/mtr -I../lib/cudd-3.0.0/epd -I../lib/cudd-3.0.0/st -I../lib/cudd-3.0.0/util -I../lib/cudd-3.0.0/dddmp -IBFAbstractionLibrary -I../lib/cadical/src
LINK          = $(CXX)
LFLAGS        = 

# Object files
OBJECTS       = main.o \
				synthesisAlgorithm.o synthesisContextBasics.o tools.o variableManager.o \
				BFAbstractionLibrary/bddDump.o BFAbstractionLibrary/BFCuddManager.o \
				BFAbstractionLibrary/BFCuddVarCube.o BFAbstractionLibrary/BFCudd.o \
				BFAbstractionLibrary/BFCuddMintermEnumerator.o  BFAbstractionLibrary/BFCuddVarVector.o \
                $(filter-out ../lib/cudd-3.0.0/cudd/testextra.o,$(filter-out ../lib/cudd-3.0.0/cudd/testcudd.o,$(patsubst %.c,%.o,$(wildcard ../lib/cudd-3.0.0/cudd/*.c)))) \
                $(filter-out ../lib/cudd-3.0.0/mtr/testmtr.o,$(patsubst %.c,%.o,$(wildcard ../lib/cudd-3.0.0/mtr/*.c))) \
                $(patsubst %.c,%.o,$(wildcard ../lib/cudd-3.0.0/epd/*.c)) \
                $(filter-out ../lib/cudd-3.0.0/st/testst.o,$(patsubst %.c,%.o,$(wildcard ../lib/cudd-3.0.0/st/*.c))) \
                $(filter-out ../lib/cudd-3.0.0/util/cpu_stats.o,$(patsubst %.c,%.o,$(wildcard ../lib/cudd-3.0.0/util/*.c))) \
                $(filter-out ../lib/cudd-3.0.0/dddmp/testdddmp.o,$(patsubst %.c,%.o,$(wildcard ../lib/cudd-3.0.0/dddmp/*.c))) \
                ../lib/cadical/src/analyze.o \
		../lib/cadical/src/arena.o \
		../lib/cadical/src/assume.o \
		../lib/cadical/src/averages.o \
		../lib/cadical/src/backtrack.o \
		../lib/cadical/src/backward.o \
		../lib/cadical/src/bins.o \
		../lib/cadical/src/block.o \
		../lib/cadical/src/ccadical.o \
		../lib/cadical/src/checker.o \
		../lib/cadical/src/clause.o \
		../lib/cadical/src/collect.o \
		../lib/cadical/src/compact.o \
		../lib/cadical/src/condition.o \
		../lib/cadical/src/config.o \
		../lib/cadical/src/constrain.o \
		../lib/cadical/src/contract.o \
		../lib/cadical/src/cover.o \
		../lib/cadical/src/decide.o \
		../lib/cadical/src/decompose.o \
		../lib/cadical/src/deduplicate.o \
		../lib/cadical/src/drattracer.o \
		../lib/cadical/src/elim.o \
		../lib/cadical/src/ema.o \
		../lib/cadical/src/extend.o \
		../lib/cadical/src/external.o \
		../lib/cadical/src/external_propagate.o \
		../lib/cadical/src/file.o \
		../lib/cadical/src/flags.o \
		../lib/cadical/src/flip.o \
		../lib/cadical/src/format.o \
		../lib/cadical/src/frattracer.o \
		../lib/cadical/src/gates.o \
		../lib/cadical/src/idruptracer.o \
		../lib/cadical/src/instantiate.o \
		../lib/cadical/src/internal.o \
		../lib/cadical/src/ipasir.o \
                ../lib/cadical/src/lidruptracer.o \
		../lib/cadical/src/limit.o \
		../lib/cadical/src/logging.o \
		../lib/cadical/src/lookahead.o \
		../lib/cadical/src/lratbuilder.o \
		../lib/cadical/src/lratchecker.o \
		../lib/cadical/src/lrattracer.o \
		../lib/cadical/src/lucky.o \
		../lib/cadical/src/message.o \
		../lib/cadical/src/minimize.o \
		../lib/cadical/src/occs.o \
		../lib/cadical/src/options.o \
		../lib/cadical/src/parse.o \
		../lib/cadical/src/phases.o \
		../lib/cadical/src/probe.o \
		../lib/cadical/src/profile.o \
		../lib/cadical/src/proof.o \
		../lib/cadical/src/propagate.o \
		../lib/cadical/src/queue.o \
		../lib/cadical/src/random.o \
		../lib/cadical/src/reap.o \
		../lib/cadical/src/reduce.o \
		../lib/cadical/src/rephase.o \
		../lib/cadical/src/report.o \
		../lib/cadical/src/resources.o \
		../lib/cadical/src/restart.o \
		../lib/cadical/src/restore.o \
		../lib/cadical/src/score.o \
		../lib/cadical/src/shrink.o \
		../lib/cadical/src/signal.o \
		../lib/cadical/src/solution.o \
		../lib/cadical/src/solver.o \
		../lib/cadical/src/stats.o \
		../lib/cadical/src/subsume.o \
		../lib/cadical/src/terminal.o \
		../lib/cadical/src/ternary.o \
		../lib/cadical/src/transred.o \
		../lib/cadical/src/util.o \
		../lib/cadical/src/var.o \
		../lib/cadical/src/veripbtracer.o \
		../lib/cadical/src/version.o \
		../lib/cadical/src/vivify.o \
		../lib/cadical/src/walk.o \
		../lib/cadical/src/watch.o


# Headers
HEADERS_BUT_EXTENSIONS = gr1context.hpp variableManager.hpp variableTypes.hpp \
	BFAbstractionLibrary/bddDump.h \
	BFAbstractionLibrary/BFCudd.h \
	BFAbstractionLibrary/BFCuddInlines.h \
	BFAbstractionLibrary/BFCuddManager.h \
	BFAbstractionLibrary/BFCuddMintermEnumerator.h \
	BFAbstractionLibrary/BFCuddVarCube.h \
	BFAbstractionLibrary/BFCuddVarVector.h \
	BFAbstractionLibrary/BF.h

# Executable & Cleaning
slugs: $(OBJECTS)
	$(LINK) $(LFLAGS) -o slugs $(OBJECTS)

clean: 
	rm -f $(OBJECTS) ../lib/cudd-3.0.0/config.h

# Special Transition Rules
../lib/cudd-3.0.0/config.h:
	cd ../lib/cudd-3.0.0; ./configure

main.o : main.cpp ../lib/cudd-3.0.0/config.h extension*.hpp $(HEADERS_BUT_EXTENSIONS)
	$(CXX) -c $(CXXFLAGS) $(INCPATH) -o "$@" "$<"

# General Translation rules
%.o : %.cpp ../lib/cudd-3.0.0/config.h $(HEADERS_BUT_EXTENSIONS)
	$(CXX) -c $(CXXFLAGS) $(INCPATH) -o "$@" "$<"

%.o : %.c ../lib/cudd-3.0.0/config.h
	$(CC) -c $(CFLAGS) $(INCPATH) -o "$@" "$<"


