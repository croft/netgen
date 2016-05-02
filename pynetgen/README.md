## Pynetgen

### Setup and Requirements

Z3 [[github.com](https://github.com/Z3Prover/z3#python)]  
* Install Python bindings: `python scripts/mk_make.py --python`  

Python libraries  
* Install Python package manager `pip`: `sudo apt-get install pip`  
* Install libraries: `sudo pip install fado ipaddr graphviz`  


### Walkthrough

To start, run `./netgen.py -h` to see command-line options.  Sample specifications are provided in the directory `specs/`, and contains (as comments) information about the paths installed by default (that are rerouted with the change specification).

To run a simple diamond topology: `./netgen.py --topo=diamond --spec=specs/diamond.txt`

To run fattree topology: `./netgen.py --topo=fattree --spec=specs/diamond.txt`
