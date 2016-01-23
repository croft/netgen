PROJECT_NAME=netgen

ROOT_DIR=$(CURDIR)
SOLVER_DIR=$(ROOT_DIR)/Solver


BIN_DIR=$(ROOT_DIR)/Bin
OBJ_DIR=$(ROOT_DIR)/Obj

Z3_DIR=$(ROOT_DIR)/Lib/z3Linux
Z3_LIB_DIR=$(Z3_DIR)/bin
Z3_INC_DIR=$(Z3_DIR)/include



CC=/usr/local/gcc-4.8.1-for-linux64/bin/x86_64-pc-linux-g++
STD=c++11
LTYPE=static
ARCHITECTURE=-m64
OPTFLAGS=-O3
PROFILE=false
DEBUG=false


INCLUDES= \
		$(Z3_INC_DIR)
		

INCLUDE_PARAMS=$(foreach d, $(INCLUDES), -I$d)

SOURCES=$(SOLVER_DIR)/Solver.cpp

OBJECTS=$(OBJ_DIR)/$(PROJECT_NAME).o
BINARY=$(BIN_DIR)/$(PROJECT_NAME)



CFLAGS = -c $(OPTFLAGS) -std=$(STD) $(ARCHITECTURE) 
LFLAGS = -$(LTYPE)-libstdc++ 


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


Z3_FLAGS=-Wl,-B$(LTYPE)  $(Z3_LIB) -$(LTYPE) -lgomp -pthread -lrt 




MKDIR_P = mkdir -p
.PHONY: directories


all : $(SOURCES) directories $(INCLUDES) $(Z3_LIB)  $(PROJECT_NAME) 

directories: ${BIN_DIR} ${OBJ_DIR}
	
${BIN_DIR}:
	${MKDIR_P} ${BIN_DIR}

${OBJ_DIR}:
	${MKDIR_P} ${OBJ_DIR}



$(OBJECTS) : $(SOURCES)
	$(CC) $(CFLAGS) -o $(OBJECTS) $(INCLUDE_PARAMS) $(SOURCES) 

$(PROJECT_NAME): $(OBJECTS)
	$(CC)  $(LFLAGS) -o $(BINARY) $(OBJECTS) $(Z3_FLAGS) $(PARSER_FLAGS)

clean :
	rm -R $(OBJECTS) $(BINARY) 




