#include <sys/types.h>
#include <dirent.h>
#include <errno.h>
#include <vector>
#include <string>
#include <iostream>
#include <string.h>
#include <sstream>
#include <fstream>
#include <tuple>
#include <functional>
#include <set>
#include <map>
#include <algorithm>
#include <time.h>
#include <regex>
#include "boost/regex.hpp"
#include <boost/algorithm/string.hpp>

#include "network.h"
#include "automata.h"
#include "utils.h"
#include "solver.h"
#include "recursive_definitions.h"

#include "z3++.h"

using namespace z3;
using namespace std;
using namespace boost; 
using namespace boost::algorithm;



string automata = "avoid_a_must_b.txt";

// //RocketFuel Topology
// string config_map_file = "data_set/RocketFuel/AS-1755/config.map";
// string topology_file   = "data_set/RocketFuel/Topology.txt";
// string selected_classes_dir = "data_set/RocketFuel/selected";

//SOSR Topology

//string exp_folder = "diamond";
string exp_folder = "sosr_network";
string config_map_file = "data_set/" + exp_folder + "/config.map";
string topology_file   = "data_set/" + exp_folder + "/Topology.txt";
string selected_classes_dir = "data_set/" + exp_folder + "/selected";
string automata_file = "data_set/" + exp_folder + "/automata.txt";


int main()
{
	try
	{
		Network n1(config_map_file,topology_file,selected_classes_dir);
		//209 nodes, 944 edges, 380 classes, 65360 rules
		n1.read_network();
		n1.create_abstract_network();
		n1.Compute_OD();
		


		Automata a1(automata_file); 
		a1.read_automata();
		a1.parse_automata();
		//log(3) << "automata " << a1.final_states << "\n";


		for(int k=1; k <= 2  ; k++)//n1.abstract_nodes.size()
		{
			cout << "\n\n Phase " << k << "\n";  
			context ctx;
			
		    
		   	Solver s1(ctx,n1,k);
			
			s1.define_k_rules();
			s1.delta_satisfies_topology();
			// s1.delta_satisfies_non_mutable();
			//s1.delta_satisfies_not_egress();
			// s1.delta_satisfies_not_existing(); 
			
			func_decl cycle = z3::function("cycle", ctx.int_sort(), ctx.int_sort(), ctx.int_sort()); 
			s1.execute_recursive(Cyclicity(ctx,cycle));
			
			func_decl dest = z3::function("dest", ctx.int_sort(), ctx.int_sort(), ctx.int_sort());
			s1.execute_recursive(Compute_Dest(ctx,dest,n1));
			
			
			
			func_decl rho = z3::function("rho", ctx.int_sort(), ctx.int_sort(), ctx.int_sort()); 
			func_decl delta = z3::function("delta", ctx.int_sort(), ctx.int_sort(), ctx.int_sort()); 
			//expr_vector delta_vars(ctx);
			//expr  delta_expr(ctx);
			s1.execute_recursive(Modified_Functionality(ctx,rho,delta,a1,n1.abstract_nodes));	
			s1.accept_automata(rho,a1);
			
			
			
			Z3_model m = s1.solve_z3();
			if(m)
			{
				model m1(ctx, m);
				cout << "\n\nModel\n" << m1;
				break;
			}
		}

	}
	catch(...)	
	{	log(10) << "exception caught";
	}
}



//Network
//nodes: 1 2 3 4 5 6 7 8
//topology: 1,4  1,5  2,4  2,5  3,4  3,5  4,6  5,7  6,8  7,8
//edges: 1,4  2,4  3,4  4,6  6,8  5,7  7,0


//>>> check multiple classes
//


// add BGP rules on rocketfuel
// rewriting in Veriflow
// fattree
// 
// 
// netgen syntax and merlin syntax
// contact nick feamster
// aditya akela: what kind of changes are applied to networks
// 
// veriflow networks from matt
// 
// smt solver: arithmetic, may not be sets
// 
// isolate a node FlowVisor: A Network Virtualization Layer section 4
// 
// mining netgen spec N -> N' , Find simplest  netgen spec equivalent to spec
// which packets are affected
// which paths are affected
// 
// benjamin pierce lenses
// 
// Anduo paper and talk
// 
// 