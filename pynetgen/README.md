## Pynetgen

### Setup and Requirements

Z3 [[github.com](https://github.com/Z3Prover/z3#python)]
* Download z3: `git checkout http://github.com/z3prover/z3`
* Generate Python bindings: `python scripts/mk_make.py --python`
* Install: `cd build; make && sudo make install`

Python libraries  
* Install Python package manager `pip`: `sudo apt-get install pip`  
* Install libraries: `sudo pip install fado ipaddr graphviz pyparsing`  


### Walkthrough

To start, run `./netgen.py -h` to see command-line options.  Sample specifications are provided in the directory `specs/`, and contains (as comments) information about the paths installed by default (that are rerouted with the change specification).

To run a simple diamond topology: `./netgen.py --topo=diamond --spec=specs/diamond.txt`

To run fattree topology: `./netgen.py --topo=fattree --spec=specs/diamond.txt`
