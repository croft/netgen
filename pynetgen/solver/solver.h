#ifndef SOLVER_H
#define SOLVER_H

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
#include <sstream>
#include "boost/regex.hpp"
#include <boost/algorithm/string.hpp>
#include "z3++.h"
#include "recursive_definitions.h"

#include "network.h"
#include "config.h"


using namespace z3;
using namespace std;

extern int SIZE; 


#if THEORY == LIA
    #define CONST(X) ctx.int_const(X)
    #define VALUE(X) ctx.int_val(X)
#elif THEORY == BV
    #define CONST(X) ctx.bv_const(X,SIZE)
    #define VALUE(X) ctx.bv_val(X,SIZE)
#elif THEORY == LRA
    #define CONST(X) ctx.real_const(X)
    #define VALUE(X) ctx.real_val(X)
#endif


class Network;

class Solver
{
public:
	int k; 
	int num_nodes;
	int num_pc;

	context& ctx;
	expr_vector n; 
	expr_vector pc; 
	expr_vector n1;

	expr query; 

	Network& network; 
	Z3_model model;
	check_result status; 


	Solver(context & ctx_i, Network &n_i, int k_i) :
	ctx(ctx_i), network(n_i), k{k_i} , n(ctx), pc(ctx), n1(ctx), query(ctx)
	{
		query = ctx.bool_val(true);
		num_nodes = network.abstract_nodes.size();
		num_pc = network.abstract_pc_map.size();
		status = unknown; 
		model=0;
	}
	
	void print_query()
	{
		std::cout << "\nQuery : "  << query; 
	}

	void define_prev_model(std::vector<std::tuple<int,int>> prev_model)
	{
	    for (int i = 0; i < prev_model.size(); i++)
	    {
		query = query && (n[i] == VALUE(std::get<0>(prev_model[i])));
		query = query && (n1[i] == VALUE(std::get<1>(prev_model[i])));
	    }
	}

	void define_k_rules()
	{
		for (unsigned int index = 0; index < k; index++)
		{
			stringstream ns,ps,n1s;
			ns << "n_" << index;
			ps << "p_" << index;
			n1s<< "n1_" << index ;

			expr x = CONST(ns.str().c_str());
			n.push_back(x);
            expr y = CONST(ps.str().c_str());
            pc.push_back(y);
            expr z = CONST(n1s.str().c_str());
            n1.push_back(z);
            
            
        #if THEORY == LIA || THEORY == BV 
            query = query && (VALUE(0) < x) && (x <= VALUE(num_nodes)) ;
            query = query && (VALUE(0) < y) && (y <= VALUE(num_pc)) ;
            query = query && (VALUE(0) < z) && (z <= VALUE(num_nodes) ) ; 
        #elif THEORY == LRA
            expr nvalue  = ctx.bool_val(false);
            expr n1value = ctx.bool_val(false); 
            for( int i = 1 ; i<= num_nodes; i++)
            {
                    nvalue = nvalue || ( VALUE(i) == x );
                    n1value = n1value || (VALUE(i) == z);
            }
            expr pcvalue = ctx.bool_val(false); 
            for( int i =1; i<= num_pc; i++)
            {
                pcvalue = pcvalue || ( VALUE(i) == y); 
            }
            query = query && nvalue && pcvalue && n1value; 
        #endif
            
		
		}
	}

	void delta_satisfies_non_mutable()
	{
		//for ( auto pc_it = 0; pc_it <= network.abstract_pc_map.size(); pc_it++)
		// {
		// 	for (unsigned int index = 0; index < k; index++)
		// 	{
		// 			set<int> immutable_nodes = network.abstract_immutable_nodes[]; //get_immutable_nodes(pc[index])
		// 			for( auto imm_it = immutable_nodes.begin(); imm_it != immutable_nodes.end(); imm_it++)
		// 			{
		// 				query = query && ( n[index] != ctx.int_val(*imm_it) );
		// 			}	
					
		// 		}
				
		// 	}		
	}

	void delta_satisfies_topology()
	{
		std::stringstream topo_str; 
		set<pair<int,int>> abstract_topology = network.abstract_topology;
        
        std::string sort_string; 
        
        #if THEORY == LIA
            sort_string = string(" Int ");
        #elif THEORY == BV
            sort_string = string(" (_ BitVec " + std::to_string(SIZE) + " ) ");
        #elif THEORY == LRA
            sort_string = string(" Real ");
        #endif
                        
		int count=0;
		topo_str << "(define-fun topology ((node_from " << sort_string << " ) (node_to " << sort_string << " )) Bool \n ";
		for ( auto at_it = abstract_topology.begin(); at_it != abstract_topology.end(); at_it++)
		{ 
            std::stringstream v1, v2; 
            
            #if THEORY == LIA
                v1 << ctx.int_val(at_it->first); 
                v2 << ctx.int_val(at_it->second); 
            #elif THEORY == BV
                v1 << ctx.bv_val(at_it->first,SIZE); 
                v2 << ctx.bv_val(at_it->second,SIZE); 
            #elif THEORY == LRA
                v1 << ctx.real_val(at_it->first); 
                v2 << ctx.real_val(at_it->second);  
            #endif
            
			topo_str << "( ite ( and ( = node_from " << v1.str() << " ) ( = node_to " << v2.str() <<" )) true  \n ";
			count++;
		}
		topo_str << "false";
		for(int i = 0; i <= count; i++)
		{
			topo_str << ")";
		}
		topo_str << "\n";
		for(unsigned index = 0; index < k; index++ )
		{
			topo_str << "\n (declare-const " << n[index]    << sort_string << " )";
			topo_str << "\n (declare-const " << n1[index]   << sort_string << " )";
			topo_str << "\n(assert ( topology " << n[index] << " " << n1[index] << "))";
		}
		Z3_ast asty;
		asty = Z3_parse_smtlib2_string(ctx, topo_str.str().c_str(), 0, 0, 0, 0, 0, 0);
		expr ex(ctx, asty);
        
		query = query && ex; 
	}
	
	void delta_satisfies_topology_uf(func_decl &topology)
	{
		
		for( auto n_it = network.abstract_nodes.begin(); n_it != network.abstract_nodes.end(); n_it ++ )
		{
			for( auto n1_it = network.abstract_nodes.begin(); n1_it != network.abstract_nodes.end(); n1_it ++ )
			{
				if( *n_it == *n1_it) 
				{
					query = query && topology(VALUE(*n_it),VALUE(*n1_it)) == ctx.bool_val(false);
				}
				else if (  network.abstract_topology.find(make_pair(*n_it,*n1_it))  != network.abstract_topology.end())
				{
					query = query && topology(VALUE(*n_it),VALUE(*n1_it)) == ctx.bool_val(true);
				}
				else
				{
					query = query && topology(VALUE(*n_it),VALUE(*n1_it)) == ctx.bool_val(false);
				}
			}
		} 
		
		for (int index = 0; index < k ; index ++ )			
		{
			query = query && topology(n[index],n1[index]) == ctx.bool_val(true);
		}		 
			 
	}	
	
	
	

	void delta_satisfies_not_egress()
	{

		// for all num_pc

		// 	set<int> egress_nodes = network.abstract_egress_nodes[pc?? ]; 
		// for (unsigned int index = 0; index < k; index++)
		// {
		// 	for( auto eg_it = egress_nodes.begin(); eg_it != egress_nodes.end(); eg_it++)
		// 	{
		// 		query = query && ( n[index] != ctx.int_val(*eg_it) );
		// 	}	
		// }
	}

	void delta_satisfies_not_existing()
	{	
	}
	
	
	Z3_model solve_z3()
	{
		set_param("pp.min-alias-size", 1000000 );
		set_param("pp.max-depth", 1000000);
		solver s(ctx);
		query = query.simplify();
		s.add(query);		
		// cout << "\n\nQuery:\n" << s;
        // cin.get();
		
		switch(s.check())
		{
			case sat : 
			status = sat;
			model = s.get_model(); 
			return model;
			
			case unsat :
			status = unsat; 
			return 0;
			
			case unknown :
			status = unknown; 
			return 0;
		}
	}
	
	
	void execute_recursive(const recursive_definition& functionality) 
	{
		for(auto pc_it = network.abstract_pc_map.begin(); pc_it != network.abstract_pc_map.end(); pc_it++)
		{
			//string pc_str = pc_it->second;
			int pc_int = pc_it->second;
			
			set<int> egress_nodes = network.abstract_egress_nodes[pc_int];
			set<int> abstract_nodes = network.abstract_nodes;
			
			query = query && functionality.auxilary_def();
			query = query && functionality.encode_null(pc_int);
			
			for (const int &node: abstract_nodes) 
			{
				if (egress_nodes.find((int)node) != egress_nodes.end())  //if egress node
				{
					query = query && functionality.base(node,pc_int); 
				}
				else // if non-egress node
				{
					expr not_new = ctx.bool_val(true);
					for(int index = 0; index < k ; index++ )
					{
						query = query && implies( ( VALUE((int)node) == n[index] &&  VALUE(pc_int) == pc[index] ),
						                         functionality.change_rec (node, pc_int, n1[index]));
						
						not_new = not_new && ( VALUE((int)node) != n[index] ||  VALUE(pc_int) != pc[index] ) ; 
						
					}					                     	
					 
					 query = query && implies( not_new, functionality.default_rec(node, pc_int, network.abstract_rules[make_pair(node,pc_int)]));
				}
			}
			// //cout << "\n\n" << query<< "\n\n"; 
		}
	}
	
	void accept_automata(const func_decl& rho, const Automata& automata)
	{
		for(auto pc_it = network.abstract_pc_map.begin(); pc_it != network.abstract_pc_map.end(); pc_it++)
		{
			//string pc_str = *pc_it;
			int pc_int = pc_it->second; 
			
			for( auto s_it = network.abstract_source_nodes[pc_int].begin(); s_it != network.abstract_source_nodes[pc_int].end(); s_it++)
			{
				int s = *s_it; 
				
				expr for_each_s = ctx.bool_val(false);
				//cout<< "automata final:" << automata.final_states; 
				
				for( auto q_it = automata.final_states.begin(); q_it != automata.final_states.end(); q_it++)
				{
					int q = *q_it;
					for_each_s = for_each_s || rho( VALUE(s), VALUE(pc_int)) == VALUE(q); 
				}
				query = query &&  for_each_s;
				
			}
			 //log(3) << "\n\n" << query<< "\n\n"; 
		}
	}
		
		
};





#endif
