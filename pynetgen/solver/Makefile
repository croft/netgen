.PHONY: cppsolver.so

DEST=./
TARGET=cppsolver
SOLVER_DIR=.


PY_INCL=/usr/include/python2.7

# BOOST_DIR=/usr/include/boost
# BOOST_INCLUDE=$(BOOST_DIR)
# BOOST_LIB=$(BOOST_DIR)
BOOST_DIR=/home/me/boost_1_60_0
BOOST_INCLUDE=$(BOOST_DIR)/include
BOOST_LIB=$(BOOST_DIR)/stage/lib

# Z3_DIR=/home/croftj/src/netgen/Lib/z3Linux
Z3_DIR=/home/me/mac/Networks/netgen/lib/z3Linux
Z3_LIB_DIR=$(Z3_DIR)/bin
Z3_INC_DIR=$(Z3_DIR)/include


CC=g++
#/usr/local/gcc-4.8.1-for-linux64/bin/x86_64-pc-linux-g++
STD=c++11
LTYPE=dynamic
ARCHITECTURE=-m64
OPTFLAGS=-O3
PROFILE=false
DEBUG=false


INCLUDES= \
		$(Z3_INC_DIR) \
		$(SOLVER_DIR) \
		$(BOOST_INCLUDE) \
		$(PY_INCL)

INCLUDE_PARAMS=$(foreach d, $(INCLUDES), -I$d)

SOURCES=$(SOLVER_DIR)/solver.cpp

OTHER_DEP_FILES=$(SOLVER_DIR)/solver.h \
				$(SOLVER_DIR)/recursive_definitions.h \
				$(SOLVER_DIR)/utils.h \
				$(SOLVER_DIR)/network.h \
				$(SOLVER_DIR)/automata.h

OBJECTS=$(DEST)/$(TARGET).so
TEMPOBJ=$(DEST)/$(TARGET).o


CFLAGS =  -c $(OPTFLAGS) -std=$(STD) $(ARCHITECTURE) -fPIC
LFLAGS =  -shared


ifeq ($(PROFILE),true)
	CFLAGS := -pg --coverage $(CFLAGS)
	LFLAGS += -pg --coverage
endif


ifeq ($(DEBUG),false)
	CFLAGS += -DNDEBUG
else
	CFLAGS += -g
endif



ifeq ($(LTYPE),static)
	Z3_LIB=$(Z3_LIB_DIR)/libz3.a
else
	Z3_LIB=$(Z3_LIB_DIR)/libz3.so
endif


all : $(SOURCES) $(INCLUDES)  $(OBJECTS)

$(OBJECTS) : $(TEMPOBJ) $(Z3_LIB)
	$(CC) $(LFLAGS) -Wl,-soname,$(TARGET).so -o $(OBJECTS)  $(TEMPOBJ)  $(Z3_LIB)  -lpython2.7 -lboost_python


$(TEMPOBJ) : $(SOURCES) $(OTHER_DEP_FILES)
	$(CC) $(CFLAGS) -o  $(TEMPOBJ)  $(INCLUDE_PARAMS) $(SOURCES)


clean :
	rm  -f $(OBJECTS) $(TEMPOBJ)

# solver.so:
# 	g++ -Wall -shared -fPIC -o $(DEST)/solver.so solver.cpp -std=c++0x -lboost_python -I$(PY_INCL)
