.PHONY: solver.so

PY_INCL=/usr/include/python2.7
DEST=..

solver.so:
	g++ -Wall -shared -fPIC -o $(DEST)/solver.so solver.cpp -std=c++0x -lboost_python -I$(PY_INCL)

clean:
	rm -f $(DEST)/solver.so
