#include <boost/python.hpp>
#include <boost/type_traits/integral_constant.hpp>
#include <string>
#include <iostream>
#include <vector>
#include <tuple>
#include <set>
#include <ctime>
#include <math.h> 
#include "utils.h"
#include "solver.h"
#include "network.h"
#include "automata.h"
#include "z3++.h"
#include "recursive_definitions.h"

using namespace std;
namespace py = boost::python;
using namespace z3;

int SIZE; 

#define  LIA 1
#define  BV  2 
#define  LRA 3


#define THEORY LIA


#if THEORY == LIA
    #define SORT     ctx.int_sort()
#elif THEORY == BV
    #define SORT     ctx.bv_sort(SIZE)
#elif THEORY == LRA
    #define SORT     ctx.real_sort()
#endif



#define UF    4
#define MACRO 5

#define ENCODING MACRO




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

template <typename T>
std::set<T> pylist_to_set(const py::object& obj) {
    std::set<T> st;
    for (unsigned long i = 0; i < len(obj); i++)
    {
        st.insert(py::extract<T>(obj[i]));
    }

    return st;
}

// std::vector<tuple<int,int>> pylist_to_tuplist2(const py::object& obj) {
//     std::vector<tuple<int,int>> vect(len(obj));
//     int j, k;
//     for (unsigned long i = 0; i < vect.size(); i++)
//     {
//      j = py::extract<int>(obj[i][0]);
//      k = py::extract<int>(obj[i][1]);
//      vect[i] = make_tuple(j, k);
//      //cout << vect[i] << endl;
//     }

//     return vect;
// }

// std::vector<tuple<int,int,int>> pylist_to_tuplist3(const py::object& obj) {
//     std::vector<tuple<int,int,int>> vect(len(obj));
//     int j, k, m;
//     for (unsigned long i = 0; i < vect.size(); i++)
//     {
//      j = py::extract<int>(obj[i][0]);
//      k = py::extract<int>(obj[i][1]);
//      m = py::extract<int>(obj[i][2]);
//      vect[i] = make_tuple(j, k, m);
//      //cout << vect[i] << endl;
//     }

//     return vect;
// }

std::map<std::pair<int,int>,int> pylist_to_map_pair(const py::object& obj) {
    std::map<std::pair<int,int>,int> mpr;
    int j, k, m;
    for (unsigned long i = 0; i < len(obj); i++)
    {
        j = py::extract<int>(obj[i][0]);
        k = py::extract<int>(obj[i][1]);
        m = py::extract<int>(obj[i][2]);
        mpr[make_pair(j,k)] =  m;
    //cout << vect[i] << endl;
    }

    return mpr  ;
}

std::set<std::pair<int,int>> pylist_to_set_pair(const py::object& obj) {
    std::set<std::pair<int,int>> spr;
    int j, k;
    for (unsigned long i = 0; i < len(obj); i++)
    {
        j = py::extract<int>(obj[i][0]);
        k = py::extract<int>(obj[i][1]);
        spr.insert(make_pair(j,k));
    //cout << vect[i] << endl;
    }

    return spr  ;
}

// -----------------------------------------------------------------------------

class AbstractNetwork {
public:
    Automata a1;
    Network n1;

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
                                 int _dead)
{
    a1.states = pylist_to_set<int>(_states);
    a1.symbols = pylist_to_vector<int>(_symbols);
    a1.transitions = pylist_to_map_pair(_fsa);
    a1.final_states = pylist_to_set<int>(_finals);
    a1.start_state = _initial;
    a1.dead_state = _dead;

    n1.abstract_nodes =  pylist_to_set<int>(_nodes);
    n1.abstract_topology = pylist_to_set_pair(_topology);
    n1.abstract_rules = pylist_to_map_pair(_classes);
    n1.abstract_immutable_nodes[1] = pylist_to_set<int>(_immutables);
    n1.abstract_egress_nodes[1] = pylist_to_set<int>(_egresses);
    n1.abstract_source_nodes[1] = pylist_to_set<int>(_sources);
    n1.abstract_pc_map["1"] = 1;

    // std::cout << "\n\nNetwork";
    // std::cout << "\nNodes : " << n1.abstract_nodes;
    // std::cout << "\nTopology : " << n1.abstract_topology;
    // std::cout << "\nRules : " << n1.abstract_rules;
    // std::cout << "\nImmutable Nodes : " << n1.abstract_immutable_nodes[1];
    // std::cout << "\nEgress Nodes : " << n1.abstract_egress_nodes[1];
    // std::cout << "\nSource Nodes : " << n1.abstract_source_nodes[1];
    //
    // std::cout << "\n\nAutomata";
    // std::cout << "\nStates : " << a1.states;
    // std::cout << "\nSymbols : " << a1.symbols;
    // std::cout << "\nTransitions : " << a1.transitions;
    // std::cout << "\nFinal States : " << a1.final_states;
    // std::cout << "\nStart State : " << a1.start_state;
    // std::cout << "\nDead State : " << a1.dead_state;

}

class CPPSolver {
public:
    AbstractNetwork network;
    std::vector<std::tuple<int, std::string, double>> perfCounters;
    CPPSolver(AbstractNetwork _network);
    py::list solve();
    py::list get_perf_counters();
};

CPPSolver::CPPSolver(AbstractNetwork _network) {
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

py::list CPPSolver::get_perf_counters()
{
    py::list ret;

    for (auto counter: perfCounters)
    {

        ret.append(py::make_tuple(get<0>(counter),
                                  get<1>(counter),
                                  get<2>(counter)));
    }

    return ret;
}

py::list CPPSolver::solve()
{
    py::list ret;

    try
    {
        network.n1.Compute_OD();
        SIZE = ceil((float)log2(network.n1.abstract_nodes.size()))+2;
        cout << "\nSIZE = " << SIZE << "\n";  
        //std::cout << "\n\nOriginal Destination : " << network.n1.abstract_od;
        clock_t begin, end;
        double elapsed_ms;

        for(int k=1; k <= network.n1.abstract_nodes.size() ; k++)
        {
            //cout << "\n\nPhase " << k << "\n";
            std::cout << "Starting phase: " << k << endl;

            context ctx;
            Solver s1(ctx,network.n1,k);

            begin = clock();

            s1.define_k_rules();
    
    
            #if ENCODING == MACRO             
                s1.delta_satisfies_topology();
            #elif ENCODING == UF
                func_decl topology = z3::function("topology", SORT, SORT, ctx.bool_sort());
                s1.delta_satisfies_topology_uf(topology);
            #endif
                
                
            s1.delta_satisfies_non_mutable();
            s1.delta_satisfies_not_egress();
            s1.delta_satisfies_not_existing();

            func_decl cycle = z3::function("cycle", SORT, SORT, SORT);
            s1.execute_recursive(Cyclicity(ctx,cycle));

            func_decl dest = z3::function("dest", SORT, SORT, SORT);
            s1.execute_recursive(Compute_Dest(ctx,dest,network.n1));

            func_decl rho = z3::function("rho", SORT, SORT, SORT);
            func_decl delta = z3::function("delta", SORT, SORT, SORT);
            //expr_vector delta_vars(ctx);
            //expr  delta_expr(ctx);
            s1.execute_recursive(Modified_Functionality(ctx,rho,delta,network.a1,network.n1.abstract_nodes));
            s1.accept_automata(rho,network.a1);

            end = clock();
            elapsed_ms = double(end - begin) / (CLOCKS_PER_SEC/1000);
            perfCounters.push_back(make_tuple(k, "query constr", elapsed_ms));

            //s1.print_query();

            cout << "solving" << endl;

            begin = clock();
            Z3_model m = s1.solve_z3();
            end = clock();
            elapsed_ms = double(end - begin) / (CLOCKS_PER_SEC/1000);
            perfCounters.push_back(make_tuple(k, "z3 solve", elapsed_ms));

            if(m)
            {
                model m1(ctx, m);
                //cout << "\n\nModel\n" << m1;

                for( int index = 0; index < k ; index++)
                {
                    //cout << "\n" << s1.n[index] << " -> " << s1.n1[index] ;
                  
                    const char* from = Z3_get_numeral_string (ctx, m1.eval(s1.n[index], true));
                    const char* to = Z3_get_numeral_string(ctx, m1.eval(s1.n1[index], true));  
                   
                    ret.append(py::make_tuple(from, to));
                }

                return ret;
            }
        }
    }
    catch(...)
    {   std::cout << "\nException Caught\n";
        return ret;
    }

    return ret;
}

BOOST_PYTHON_MODULE(cppsolver){
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

    py::class_<CPPSolver>("CPPSolver",
                          py::init<AbstractNetwork>())
        .def("solve", &CPPSolver::solve)
        .def("get_perf_counters", &CPPSolver::get_perf_counters);
}
