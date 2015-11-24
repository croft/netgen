PROJECT_NAME=SOSR

ROOT_DIR=$(CURDIR)
SRC_DIR=$(ROOT_DIR)
OUT_DIR=$(ROOT_DIR)

Z3_DIR=/home/parallels/z3
Z3_LIB_DIR=$(Z3_DIR)/build
Z3_INC_DIR=$(Z3_DIR)/include

CC=g++
STD=c++11


#not tested for mutiple sources... 
SOURCES=$(SRC_DIR)/prog.cpp
OBJECTS=$(OUT_DIR)/prog.o
BINARY=$(OUT_DIR)/prog


ifeq ($(STD),)
   CFLAGS=-c -Wall -O3
else
   CFLAGS=-c -Wall -O3 -std=$(STD)
endif

LTYPE=static
LFLAGS=-$(LTYPE)-libstdc++

ifeq ($(LTYPE),static)
  Z3_FLAGS=-Wl,-B$(LTYPE)  $(Z3_LIB_DIR)/libz3.a -$(LTYPE)  -lgomp -pthread -lrt 
else 
  Z3_FLAGS=-Wl,-B$(LTYPE)  $(Z3_LIB_DIR)/libz3.so -$(LTYPE)  -lgomp -pthread -lrt 
endif


MKDIR_P = mkdir -p
.PHONY: directories


all : directories $(PROJECT_NAME) $(SOURCES)

directories: ${OUT_DIR}

${OUT_DIR}:
	${MKDIR_P} ${OUT_DIR}


$(OBJECTS) : $(SOURCES)
	$(CC) $(CFLAGS) -o $(OBJECTS) -I$(Z3_INC_DIR)  $(SOURCES) 

$(PROJECT_NAME): $(OBJECTS)
	$(CC)  $(LFLAGS) -o $(BINARY) $(OBJECTS) $(Z3_FLAGS)
	rm prog.o 

clean :
	rm -R $(OBJECTS) $(BINARY) $(OUT_DIR)

