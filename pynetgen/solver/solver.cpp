#include <boost/python.hpp>
#include <string>
#include <iostream>
#include <vector>
#include <tuple>

using namespace std;
namespace py = boost::python;

// -----------------------------------------------------------------------------
// COUT OVERRIDES
// -----------------------------------------------------------------------------
template <typename T>
std::ostream& operator<<(std::ostream& out, const std::vector<T>& v) {
    if (!v.empty()) {
	out << '[';
	std::copy(v.begin(), v.end(), std::ostream_iterator<T>(out, ", "));
	out << "\b\b]";
    }

    return out;
}

template<typename T1,typename T2>
std::ostream &operator<<(std::ostream &stream, const std::tuple<T1,T2> & p) {
	stream<<"("<<get<0>(p)<<","<<get<1>(p)<<")";
	return stream;
}

template<typename T1,typename T2, typename T3>
std::ostream &operator<<(std::ostream &stream, const std::tuple<T1,T2,T3> & p) {
	stream<<"("<<get<0>(p)<<","<<get<1>(p)<<","<<get<2>(p)<<")";
	return stream;
}
// -----------------------------------------------------------------------------


// -----------------------------------------------------------------------------
// PYTHON TYPES CONVERSION
// -----------------------------------------------------------------------------
template <typename T>
std::vector<T> pylist_to_vector(const py::object& obj) {
    std::vector<T> vect(len(obj));
    for (unsigned long i = 0; i < vect.size(); i++)
    {
	vect[i] = py::extract<T>(obj[i]);
    }

    return vect;
}

std::vector<tuple<int,int>> pylist_to_tuplist2(const py::object& obj) {
    std::vector<tuple<int,int>> vect(len(obj));
    int j, k;
    for (unsigned long i = 0; i < vect.size(); i++)
    {
	j = py::extract<int>(obj[i][0]);
	k = py::extract<int>(obj[i][1]);
	vect[i] = make_tuple(j, k);
	//cout << vect[i] << endl;
    }

    return vect;
}

std::vector<tuple<int,int,int>> pylist_to_tuplist3(const py::object& obj) {
    std::vector<tuple<int,int,int>> vect(len(obj));
    int j, k, m;
    for (unsigned long i = 0; i < vect.size(); i++)
    {
	j = py::extract<int>(obj[i][0]);
	k = py::extract<int>(obj[i][1]);
	m = py::extract<int>(obj[i][2]);
	vect[i] = make_tuple(j, k, m);
	//cout << vect[i] << endl;
    }

    return vect;
}
// -----------------------------------------------------------------------------

class AbstractNetwork {
public:
    vector<int> nodes;
    vector<int> sources;
    vector<int> egresses;
    vector<int> immutables;

    // (from node, to node)
    vector<tuple<int,int>> topology;

    // (from node, pc, to node)
    vector<tuple<int,int,int>> classes;

    // (state, symbol, successor)
    vector<tuple<int,int,int>> fsa;
    vector<int> states;
    vector<int> symbols;
    int initial;
    int dead;
    vector<int> finals;

    AbstractNetwork() {}

    AbstractNetwork(py::list _nodes,
		    py::list _sources,
		    py::list _egresses,
		    py::list _immutables,
		    py::list _topology,
		    py::list _classes,
		    py::list _fsa,
		    py::list _states,
		    py::list _symbols,
		    py::list _finals,
		    int _initial,
		    int _dead);
};

AbstractNetwork::AbstractNetwork(py::list _nodes,
				 py::list _sources,
				 py::list _egresses,
				 py::list _immutables,
				 py::list _topology,
				 py::list _classes,
				 py::list _fsa,
				 py::list _states,
				 py::list _symbols,
				 py::list _finals,
				 int _initial,
				 int _dead) {
    // topology
    topology = pylist_to_tuplist2(_topology);
    nodes = pylist_to_vector<int>(_nodes);
    sources = pylist_to_vector<int>(_sources);
    egresses = pylist_to_vector<int>(_egresses);
    immutables = pylist_to_vector<int>(_immutables);

    // classes
    classes = pylist_to_tuplist3(_classes);

    // fsa
    fsa = pylist_to_tuplist3(_fsa);
    symbols = pylist_to_vector<int>(_symbols);
    states = pylist_to_vector<int>(_states);
    finals = pylist_to_vector<int>(_finals);
    initial = initial;
    dead = dead;

    // cout << "Nodes:" << nodes << endl;
    // cout << "Sources:" << sources << endl;
    // cout << "Egresses:" << egresses << endl;
    // cout << "Immutables:" << immutables << endl;
    // cout << "Initial:" << _initial << endl;
    // cout << "Dead:" << _dead << endl;
}

class Solver {
public:
    AbstractNetwork network;
    Solver(AbstractNetwork _network);
    py::list solve();
};

Solver::Solver(AbstractNetwork _network) {
    network = _network;
}

/* TODO: hook existing solver code into this function.
 * The Solver class contains an AbstractNetwork member.
 * Solver::solve() should return a list of tuples of the
 * changed path.  That is, a list of the form, for k changes:
 *    [(n_0, n1_0), (n_1, n1_1), ... (n_k, n1_k)]
 * Each tuple should be instantiated using:
 *    py::make_tuple(n, n1)
 */
py::list Solver::solve() {
    py::list ret;
    cout << "Solver:solve() was invoked" << endl;
    ret.append(py::make_tuple(1, 2));
    return ret;
}

BOOST_PYTHON_MODULE(solver){
    py::class_<AbstractNetwork>("AbstractNetwork",
				py::init<py::list,
				py::list,
				py::list,
				py::list,
				py::list,
				py::list,
				py::list,
				py::list,
				py::list,
				py::list,
				int,
				int>());

    py::class_<Solver>("Solver",
    		       py::init<AbstractNetwork>())
    	.def("solve", &Solver::solve);
}
