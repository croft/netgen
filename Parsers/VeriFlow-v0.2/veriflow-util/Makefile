# This file is protected by the VeriFlow Research License Agreement
# available at http://www.cs.illinois.edu/~khurshi1/projects/veriflow/veriflow-research-license-agreement.txt.
# A copy of this agreement is also included in this package.
#
# Copyright (c) 2012-2013 by
# The Board of Trustees of the University of Illinois.
# All rights reserved.

CXXFLAGS =	-O2 -g -Wall -D_REENTRANT -fPIC

OBJS =		net.o thread.o socks.o StringTokenizer.o R.o Packet.o debug.o log.o

LIBS =		-lpthread

TARGET =	libveriflowutil.so

$(TARGET):	$(OBJS)
	$(CXX) -shared -o $(TARGET) $(OBJS) $(LIBS)

all:	$(TARGET)

clean:
	rm -f $(OBJS) $(TARGET) *.o

.PHONY : clean all
