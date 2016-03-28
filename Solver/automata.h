#ifndef AUTOMATA_H
#define AUTOMATA_H

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

using namespace std;
using namespace boost; 
using namespace boost::algorithm;


class Automata 
{

	private:	
		set<int> states;
		vector<string> states_string; 

		int start_state;
		vector<string> start_state_string;
		
		map<string,int> symbols; 
		vector<string> symbols_string;
		
		set<tuple<int,int,int>> transitions;
		vector<string> transitions_string;
		
		set<int> final_states;
		vector<string> final_state_string;

		string source_file; 

	public: 

		Automata(string input): source_file{input} {};

		void read_automata();	
		void parse_automata();
};

void Automata::read_automata()
{
	std::ifstream infile(source_file);
	std::stringstream buffer;
	buffer << infile.rdbuf();
	string buffer_str = buffer.str();
	log(3) << buffer_str;

	//BOOST REGEX EXAMPLE
    // boost::regex regex("\\[INFO\\]([\\ 0-9a-zA-z:\\n\\r])*");
    // boost::sregex_token_iterator iter(buffer_str.begin(), buffer_str.end(), regex, 0);
    // boost::sregex_token_iterator end;
    // for( ; iter != end; ++iter ) {
    //     std::cout<<*iter<<"End of regex\n";
    // }

    
    vector<string> SplitVec; 
    split( SplitVec, buffer_str, is_any_of("[INFO]"), token_compress_on ); 
    for(int i =0; i<SplitVec.size(); i++)
    {	trim(SplitVec[i]);
    	if(SplitVec[i].empty())
    		continue; 
    	
    	vector<string> key_value; 
    	split( key_value, SplitVec[i], is_any_of(":") );
    	trim(key_value[0]);
    	if(key_value[0].empty())
    		continue;
    	to_lower(key_value[0]);
    	if (key_value[0].compare("states") == 0)
    		split( states_string, key_value[1], is_any_of(" ") );
    	else if (key_value[0].compare("start") == 0)	
    		split( start_state_string, key_value[1], is_any_of(" ") );
    	else if (key_value[0].compare("symbols") == 0)
    		split( symbols_string, key_value[1], is_any_of(" ") );
    	else if (key_value[0].compare("transitions") == 0)	
    		split( transitions_string, key_value[1], is_any_of("\n\r") );
    	else if (key_value[0].compare("final") == 0)
    		split( final_state_string, key_value[1], is_any_of(" ") );
    	 
    }

    log(3) << states_string << "\n" << start_state_string << "\n" << symbols_string << "\n" << transitions_string << "\n" << final_state_string; 
}

void Automata::parse_automata()
{

	for(int i=0; i<states_string.size(); i++)
	{
		trim(states_string[i]);
		if(states_string[i].empty())
			continue;
		states.insert(stoi(states_string[i]));
	}

	for(int i=0; i<start_state_string.size(); i++)
	{	
		trim(start_state_string[i]);
		if(start_state_string[i].empty())
			continue;
		start_state = stoi(start_state_string[i]);
		break;
	}

	for(int i=0; i<final_state_string.size(); i++)
	{
		trim(final_state_string[i]);
		if(final_state_string[i].empty())
			continue;
		final_states.insert(stoi(final_state_string[i]));
	}

	int counter=1; 
	for(int i=0; i<symbols_string.size(); i++)
	{
		trim(symbols_string[i]);
		if(symbols_string[i].empty())
			continue;
		if(symbols.find(symbols_string[i]) == symbols.end())
		{
			symbols[symbols_string[i]] = counter;
			counter ++; 
		}
	}

	for(int i=0; i<transitions_string.size(); i++)
	{
		trim(transitions_string[i]);
		if(transitions_string[i].empty())
			continue;
		vector<string> rules; 
		split( rules, transitions_string[i], is_any_of(" ") );

		log(3) << "\n" << transitions_string[i] << "\n" << rules;

		int flag = 0; 
		int from;
		int to;
		string alphabet;

		for(int j =0; j <rules.size(); j++)
		{
			trim(rules[j]);
			if(rules[j].empty())
				continue; 
		
			switch(flag)
			{
				case 0: 
					from = stoi(rules[j]);
					if(states.find(from) == states.end())
						throw "State not found";
					flag++;
					break;
				case 1: 
					alphabet = 	rules[j];
					if(symbols.find(alphabet) == symbols.end())
						throw "Symbol not found";
					flag++;
					break;
				case 2: 
					to = stoi(rules[j]);
					if(states.find(to) == states.end())
						throw "State not found";
					flag++;
					break;
				case 3: 
					throw "Invalid Transition";		
			}
		}
		transitions.insert(make_tuple(from,symbols[alphabet],to));
	}
		
	log(3) << states << "\n" << start_state << "\n" << final_states << "\n" << symbols << "\n" << transitions;
}

#endif 
