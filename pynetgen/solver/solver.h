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
#include "boost/regex.hpp"
#include <boost/algorithm/string.hpp>
#include "z3++.h"
#include "recursive_definitions.h"

#include "network.h"


using namespace z3;
using namespace std;

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

	void define_k_rules()
	{
		for (unsigned int index = 0; index < k; index++)
		{
			stringstream ns,ps,n1s;
			ns << "n_" << index;
			ps << "p_" << index;
			n1s<< "n1_" << index ;

			expr x = ctx.int_const(ns.str().c_str());
			n.push_back(x);
			query = query && (ctx.int_val(0) < x) && (x <= ctx.int_val(num_nodes)) ;

			expr y = ctx.int_const(ps.str().c_str());
			pc.push_back(y);
			query = query && (ctx.int_val(0) < y) && (y <= ctx.int_val(num_pc)) ;

			expr z = ctx.int_const(n1s.str().c_str());
			n1.push_back(z);
			query = query && (ctx.int_val(0) < z) && (z <= ctx.int_val(num_nodes) ) ; 

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
		stringstream topo_str; 
		set<pair<int,int>> abstract_topology = network.abstract_topology;

		int count=0;
		topo_str << "(define-fun topology ((node_from Int) (node_to Int)) Bool \n ";
		for ( auto at_it = abstract_topology.begin(); at_it != abstract_topology.end(); at_it++)
		{
			topo_str << "( ite ( and ( = node_from " << at_it->first << " ) ( = node_to " << at_it->second <<" )) true  \n ";
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
			topo_str << "\n (declare-const " << n[index] << " Int )";
			topo_str << "\n (declare-const " << n1[index] << " Int )";
			topo_str << "\n(assert ( topology " << n[index] << " " << n1[index] << "))";
		}
		Z3_ast asty;
		// ctx.set(":pp_min_alias_size", 1000000);
		// ctx.set(":pp_max_depth", 1000000);
		asty = Z3_parse_smtlib2_string(ctx, topo_str.str().c_str(), 0, 0, 0, 0, 0, 0);
		expr ex(ctx, asty);

		query = query && ex; 
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
		//query = query.simplify();
		s.add(query);		
		//cout << "\n\nQuery:\n" << s;
		
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
						query = query && implies( ( ctx.int_val((int)node) == n[index] &&  ctx.int_val(pc_int) == pc[index] ),
						                         functionality.change_rec (node, pc_int, n1[index]));
						
						not_new = not_new && ( ctx.int_val((int)node) != n[index] ||  ctx.int_val(pc_int) != pc[index] ) ; 
						
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
					for_each_s = for_each_s || rho( ctx.int_val(s), ctx.int_val(pc_int)) == ctx.int_val(q); 
				}
				query = query &&  for_each_s;
				
			}
			 //log(3) << "\n\n" << query<< "\n\n"; 
		}
	}
		
		
};





#endif