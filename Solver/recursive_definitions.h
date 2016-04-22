#ifndef REC_DEF_H
#define REC_DEF_H

#include "z3++.h"
#include "automata.h"

using namespace z3;

class recursive_definition
{
	public:
		virtual expr base( const int, const int) const = 0;
		virtual expr change_rec(const int,const int, const expr) const = 0;
		virtual expr default_rec(const int,const int, const int)const = 0;
		virtual expr auxilary_def() const = 0;
		virtual expr encode_null(const int) const = 0;
};

class Cyclicity : public recursive_definition
{
	public:
		context &ctx; 
		func_decl &cycle; 

		Cyclicity(context & ctx_i, func_decl& cycle_i):ctx(ctx_i), cycle(cycle_i)
		{ }
		expr base(const int node, const int pc) const
		{ 
			expr query = cycle(ctx.int_val(node), ctx.int_val(pc)) == ctx.int_val(0);
			return query;
		}
		expr change_rec(const int node,const int pc, const expr n_to) const
		{
			expr query = (cycle(ctx.int_val(node),ctx.int_val(pc)) > cycle(n_to,ctx.int_val(pc)));
			return query;
		}
		expr default_rec(const int node,const int pc, const int n_to) const
		{
			// if(n_to == 0)
			// {
			// 	return ctx.bool_val(true);
			// }
			
			expr query = (cycle(ctx.int_val(node),ctx.int_val(pc)) > cycle(ctx.int_val(n_to),ctx.int_val(pc)));
			return query;
		}
		expr auxilary_def() const 
		{
			return ctx.bool_val(true);
		}
		expr encode_null(int pc) const
		{
			return cycle(ctx.int_val(0), ctx.int_val(pc)) == ctx.int_val(0);
		}	
};


class Modified_Functionality : public recursive_definition
{
	public:
		context &ctx; 
		func_decl &rho; 
		Automata &a1; 
		func_decl & delta;
		set<int> & abstract_nodes; 
		
		// expr & delta_expr;
		// expr_vector & delta_vars;

		// stringstream delta_str;
		// int k;
		
		// Modified_Functionality(context & ctx_i, func_decl& rho_i,func_decl& delta_i, Automata& a1_i, set<int>& abstract_nodes_i, expr & delta_expri, expr_vector & delta_varsi)
		// :ctx(ctx_i), rho(rho_i), delta(delta_i), a1(a1_i), abstract_nodes(abstract_nodes_i), delta_expr(delta_expri), delta_vars(delta_varsi)
		
		Modified_Functionality(context & ctx_i, func_decl& rho_i,func_decl& delta_i, Automata& a1_i, set<int>& abstract_nodes_i)
		:ctx(ctx_i), rho(rho_i), delta(delta_i), a1(a1_i), abstract_nodes(abstract_nodes_i)
		{	
			
			// k = ki; 
			// int count=0;
			// delta_str <<  "(define-fun delta ((state Int) (node Int)) Int \n ";
			// for( auto state : a1.states)
			// {
			// 	for (auto node : abstract_nodes)
			// 	{
			// 		if( a1.transitions.find(make_pair(state,node)) != a1.transitions.end() )
			// 		{
			// 			delta_str << "( ite ( and ( = state " << state << " ) ( = node " << node <<" )) " << a1.transitions[make_pair(state,node)] << "  \n ";
			// 			count++;
			// 		}		
			// 		// else 
			// 		// 	delta_expr = ctx.int_val(0); 			
			// 	}
			// }			
			// delta_str << "0";
			// for(int i = 0; i <= count; i++)
			// {
			// 	delta_str << ")";
			// }
			// delta_str << "\n";
			// delta_str << "\n(declare-fun rho (Int Int) Int )";
			// for(unsigned index = 0; index < k; index++ )
			// {
			// 	delta_str << "\n (declare-const n1_" << index <<" Int )";				
			// }
			

			// delta_expr = ctx.int_val(0); 
			// delta_vars.push_back(ctx.int_const("state_expr"));
			// delta_vars.push_back(ctx.int_const("node_expr"));
				
			// expr state_expr = delta_vars[0];
			// expr node_expr = delta_vars[1];
		
			// for( auto state : a1.states)
			// {
			// 	for (auto node : abstract_nodes)
			// 	{
			// 		if( a1.transitions.find(make_pair(state,node)) != a1.transitions.end() )
			// 			delta_expr = ite (  state_expr == ctx.int_val(state) && node_expr == ctx.int_val(node) , ctx.int_val(a1.transitions[make_pair(state,node)])
			// 			                 ,  delta_expr);
			// 		// else 
			// 		// 	delta_expr = ctx.int_val(0); 			
			// 	}
			// }				
		}
		
		//creates delta
		expr auxilary_def() const
		{
			
			expr query = ctx.bool_val(true);
			
			for( auto tran_it = a1.transitions.begin(); tran_it != a1.transitions.end(); tran_it++)
			{
				query = query && delta(ctx.int_val(tran_it->first.first),ctx.int_val(tran_it->first.second) ) == ctx.int_val(tran_it->second) ; 
				
			}
			
			return query;
	
			//expr qu = ctx.bool_val(true);
			// for (auto node : abstract_nodes)
			// {
			// 	expr ret = ctx.bool_val(false);
			// 	for( auto state : a1.states)
			// 	{
			//		
			// 		if( a1.transitions.find(make_pair(state,node)) != a1.transitions.end() )
			// 			ret =  ret || rho(ctx.int_val(node),ctx.int_val(1)) == ctx.int_val(state); 
			//
			// 	}
			// 	qu = qu && ret; 
			// }
			//
			// cout << qu;
			//return qu;
		}
		
		//rho(n,pc) = delta(q0,n)
		expr base(const int node, const int pc) const
		{
			//expr query = rho(ctx.int_val(node), ctx.int_val(pc)) == ctx.int_val(a1.transitions[make_pair(a1.start_state,node)]);
			
			expr query = rho(ctx.int_val(node), ctx.int_val(pc)) == delta(ctx.int_val(a1.start_state), ctx.int_val(node)) ;
			return query;
		}
		
		
		expr change_rec(const int node,const int pc, const expr n_to) const
		{
			expr query = rho( ctx.int_val(node), ctx.int_val(pc) ) == delta( rho( n_to, ctx.int_val(pc)), ctx.int_val(node)) ; 
			return query;
			
			// stringstream program;
			// program <<  delta_str.str() << "\n" << "(assert " << query << ")" ; 
			// Z3_ast asty;
			// asty = Z3_parse_smtlib2_string(ctx, program.str().c_str(), 0, 0, 0, 0, 0, 0);
			// expr ex(ctx, asty);
			// //cout << program.str();
			// //cout << ex;
			// return ex;
			
			//return expr(subst(ctx, query, delta, delta_expr, delta_vars)).simplify();
			
			//return ctx.bool_val(true);
		}
		expr default_rec(const int node,const int pc, const int n_to) const
		{
			// if(n_to == 0)
			// {
			// 	return ctx.bool_val(true);
			// }
			
			expr query = (rho(ctx.int_val(node),ctx.int_val(pc)) ==   delta( rho(ctx.int_val(n_to),ctx.int_val(pc)),ctx.int_val(node))); 		
			return query;
			
			
			// stringstream program;
			// program <<  delta_str.str() << "\n" << "(assert " << query << ")" ; 
			// Z3_ast asty;
			// asty = Z3_parse_smtlib2_string(ctx, program.str().c_str(), 0, 0, 0, 0, 0, 0);
			// expr ex(ctx, asty);
			// return ex;
			
			//return expr(subst(ctx, query, delta, delta_expr, delta_vars)).simplify();
			//return ctx.bool_val(true);
		}
		
		expr encode_null(int pc) const
		{
			return rho(ctx.int_val(0), ctx.int_val(pc)) == ctx.int_val(0);
		}
}; 


class Compute_Dest : public recursive_definition
{
	public:
		context &ctx; 
		func_decl &dest; 
		Network &n;
		
		Compute_Dest(context & ctx_i, func_decl& dest_i, Network &ni):ctx(ctx_i), dest(dest_i), n(ni)
		{ }
		expr base(const int node, const int pc) const
		{ 
			expr query = dest(ctx.int_val(node), ctx.int_val(pc)) == ctx.int_val(node);
			return query;
		}
		expr change_rec(const int node,const int pc, const expr n_to) const
		{
			expr query = (dest( ctx.int_val(node), ctx.int_val(pc) ) == dest( n_to, ctx.int_val(pc))) ; 
			return query;
		}
		expr default_rec(const int node,const int pc, const int n_to) const
		{
			// if(n_to == 0)
			// {
			// 	return ctx.bool_val(true);
			// }
			
			expr query = (dest( ctx.int_val(node), ctx.int_val(pc) ) == dest( ctx.int_val(n_to), ctx.int_val(pc))) ; 
			return query;
		}
		expr auxilary_def() const 
		{
			expr query  =  ctx.bool_val(true); 
			
			for ( auto pc = 1; pc <= n.abstract_pc_map.size(); pc ++ )
			{
				for( auto src_it = n.abstract_source_nodes[pc].begin(); src_it != n.abstract_source_nodes[pc].end(); src_it ++ ) 
				{
					int src = *src_it;
					query = query &&  dest(ctx.int_val(src), ctx.int_val(pc)) == ctx.int_val( n.abstract_od[make_pair(src,pc)] );
				}
			}
			
			return query;
		}
		
		expr encode_null(int pc) const
		{
			return  dest(ctx.int_val(0), ctx.int_val(pc)) == ctx.int_val(0);
		}
};


#endif
