#include <boost/python.hpp>
#include <boost/type_traits/integral_constant.hpp>
#include <string>
#include <iostream>
#include <vector>
#include <tuple>
#include <set> 
#include "utils.h"
#include "solver.h"
#include "network.h"
#include "automata.h"
#include "z3++.h"
#include "recursive_definitions.h"

using namespace std;
namespace py = boost::python;
using namespace z3;


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
// 	j = py::extract<int>(obj[i][0]);
// 	k = py::extract<int>(obj[i][1]);
// 	vect[i] = make_tuple(j, k);
// 	//cout << vect[i] << endl;
//     }

//     return vect;
// }


// std::vector<tuple<int,int,int>> pylist_to_tuplist3(const py::object& obj) {
//     std::vector<tuple<int,int,int>> vect(len(obj));
//     int j, k, m;
//     for (unsigned long i = 0; i < vect.size(); i++)
//     {
// 	j = py::extract<int>(obj[i][0]);
// 	k = py::extract<int>(obj[i][1]);
// 	m = py::extract<int>(obj[i][2]);
// 	vect[i] = make_tuple(j, k, m);
// 	//cout << vect[i] << endl;
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
    CPPSolver(AbstractNetwork _network);
    py::list solve();
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



py::list CPPSolver::solve() 
{
    py::list ret;

    try
    {
        network.n1.Compute_OD();
        std::cout << "\n\nOriginal Destination : " << network.n1.abstract_od; 
        

        for(int k=1; k <= network.n1.abstract_nodes.size() ; k++)
        {
            cout << "\n\n Phase " << k << "\n";  
            context ctx;
            
            
            Solver s1(ctx,network.n1,k);
            
            s1.define_k_rules();
            s1.delta_satisfies_topology();
            s1.delta_satisfies_non_mutable();
            s1.delta_satisfies_not_egress();
            s1.delta_satisfies_not_existing(); 
          
                        
            func_decl cycle = z3::function("cycle", ctx.int_sort(), ctx.int_sort(), ctx.int_sort()); 
            s1.execute_recursive(Cyclicity(ctx,cycle));
            
            func_decl dest = z3::function("dest", ctx.int_sort(), ctx.int_sort(), ctx.int_sort());
            s1.execute_recursive(Compute_Dest(ctx,dest,network.n1));
            
            
            
            func_decl rho = z3::function("rho", ctx.int_sort(), ctx.int_sort(), ctx.int_sort()); 
            func_decl delta = z3::function("delta", ctx.int_sort(), ctx.int_sort(), ctx.int_sort()); 
            //expr_vector delta_vars(ctx);
            //expr  delta_expr(ctx);
            s1.execute_recursive(Modified_Functionality(ctx,rho,delta,network.a1,network.n1.abstract_nodes));   
            s1.accept_automata(rho,network.a1);
            
            //s1.print_query(); 

            Z3_model m = s1.solve_z3();
            if(m)
            {
                model m1(ctx, m);
                //cout << "\n\nModel\n" << m1;
                
                for( int index = 1; index <= k ; index++)
                {
                    int from = m1.eval(s1.n[index]);
                    int to =  m1.eval(s1.n1[index]); 
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
    	.def("solve", &CPPSolver::solve);
}

