#ifndef SOLVER_UTILS_H_
#define SOLVER_UTILS_H_

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
#include "z3++.h"
#include <unordered_map>

using namespace std;
using namespace z3; 


int threshold = 4;
class mystreambuf: public std::streambuf
{};
mystreambuf nostreambuf;
std::ostream nocout(&nostreambuf);
#define log(x) ((x >= threshold)? std::cout : nocout)




template<typename T1, typename T2>
std::ostream &operator<<(std::ostream &stream, const std::map<T1, T2>& map)
{
	stream<<"["	;
	for (typename std::map<T1, T2>::const_iterator it = map.begin();
			 it != map.end();
			 ++it)
		{
			stream << "  " << (*it).first << " --> " << (*it).second << std::endl;
		}
		stream<<"] size:"<<map.size();
	return stream;
}

template<typename T>
std::ostream &operator<<(std::ostream &stream, const std::vector<T> & v)
{
	stream<<"["	;
	for (typename std::vector<T> ::const_iterator it = v.begin();
			 it != v.end();
			 ++it)
		{
			stream << "  " << (*it)<<" \n";
		}
		stream<<"] size:"<<v.size();
	return stream;
}

template<typename T>
std::ostream &operator<<(std::ostream &stream, const std::set<T> & v)
{
	stream<<"[";
	for (typename std::set<T> ::const_iterator it = v.begin();
			 it != v.end();
			 ++it)
		{
			stream << "  " << (*it)<<" \n ";
		}
		stream<<"] size:"<<v.size();
	return stream;
}



template<typename T1,typename T2>
std::ostream &operator<<(std::ostream &stream, const std::pair<T1,T2> & p)
{
	stream<<"("<<p.first<<","<<p.second<<")";
	return stream;
}

template<typename T1,typename T2>
std::ostream &operator<<(std::ostream &stream, const std::tuple<T1,T2> & p)
{
	stream<<"("<<get<0>(p)<<","<<get<1>(p)<<")";
	return stream;
}

template<typename T1,typename T2, typename T3>
std::ostream &operator<<(std::ostream &stream, const std::tuple<T1,T2,T3> & p)
{
	stream<<"("<<get<0>(p)<<","<<get<1>(p)<<","<<get<2>(p)<<")";
	return stream;
}

set<string> getdir (string dir )
{
		set<string> files;
		DIR *dp;
		struct dirent *dirp;
		if((dp  = opendir(dir.c_str())) == NULL) 
		{
				cout << "Error(" << errno << ") opening " << dir << endl;
				throw  string("Error: opening Dir");
		}

		while ((dirp = readdir(dp)) != NULL) 
		{
			string file_name = string(dirp->d_name);
			if(file_name.rfind(".txt") == std::string::npos)
			{ 
				continue;
			}
			files.insert(string(dirp->d_name));
		}
		closedir(dp);
		return files;
}
struct ASTComparer
{

	bool operator() (const z3::ast & e1, const z3::ast & e2) const
	{
		return z3::eq(e1, e2);;
	}

};

		/// <summary> Function object to hash a Z3 AST objects </summary>
struct ASTHasher
{

	std::size_t operator() (const z3::ast & e) const
	{
		return e.hash();
	}

};

static z3::expr subst(z3::context & ctx, const z3::expr & e, const z3::func_decl & f, const z3::expr & h, const z3::expr_vector & variables)
{

	// Check whether the number of source variables (i.e., the variables in h) and the arity of f match
	assert(variables.size() == f.arity());

	// Copy expression, which is then modified
	z3::expr result = e;

	// Create cache to store (substituted) expressions
	typedef std::unordered_map<z3::expr, z3::expr, ASTHasher, ASTComparer> ExprMap;
	ExprMap cache;

	// Initialize worklist with root node of the AST
	std::list<z3::expr> worklist;
	worklist.push_back(result);

	//
	// Process the worklist
	//
	while (!worklist.empty())
	{

		// Get worklist entry
		z3::expr cur = worklist.back();

		// We can only handle AST types AST_APP
		// (as they are the only ones that should occur in ur setting)
		assert(cur.is_app());

		// Let's assume that this AST node has been completely processed and substituted
		bool subexpressions_processed = true;

		// Process (or use) all sub-expressions of this expression
		// Hint: everything (i.e., variables, constants, functions) is a function in SMTLib2)
		for (unsigned int i = 0; i < cur.num_args(); ++i)
		{

			// Get i-th argument (sub-expression) of current expression
			z3::expr arg = cur.arg(i);

			// Sub-expression has not yet been processed
			if (cache.count(arg) == 0)
			{

				// Add sub-expression to worklist
				worklist.push_back(arg);

				// Indicate that this expression cannot be processed at this time
				subexpressions_processed = false;

			}

		}

		// If all subexpressions of this expression have been processed, process it
		if (subexpressions_processed)
		{

			// Pop expression from worklist
			worklist.pop_back();

			// Create list of expressions that are used to substitute
			z3::expr_vector dest(ctx);
			for (unsigned int i = 0; i < cur.num_args(); ++i)
			{
				dest.push_back(cache.at(cur.arg(i)));
			}

			// The current expression is the function application of f.
			// Substitute the expression with h
			if (z3::eq(f, cur.decl()))
			{

				// Copy the expression h
				z3::expr copy_of_h = h;

				// Replace the variables in copy_of_h with the processed sub-expressions of f
				z3::expr tmp = copy_of_h.substitute(variables, dest);

				// Store the resulting expression in the cache
				cache.emplace(cur, tmp);

			}

			// The current expression is not the function application of f.
			// Substitute the all subexpressions with processed subexpressions
			else
			{

				// Replace the variables in copy_of_cur with the processed sub-expressions of cur
				z3::expr tmp = cur.decl()(dest);

				// Store the resulting expression in the cache
				cache.emplace(cur, tmp);

			}

		}

	}

	// Returned processed expression
	return cache.at(e);

}




#endif
