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


#include "utils.h"

#include "z3++.h"

using namespace z3;
using namespace std;
using namespace boost; 
using namespace boost::algorithm;



string rocketfuel_dir = "data_set/RocketFuel";
string snapshot_dir = rocketfuel_dir + "/AS-1755";
string selected_classes_dir = rocketfuel_dir + "/selected";


int threshold = 4;

class mystreambuf: public std::streambuf
{};
mystreambuf nostreambuf;
std::ostream nocout(&nostreambuf);

#define log(x) ((x >= threshold)? std::cout : nocout)



class Network
{
    private:
    	string selected_classes_dir;

    	set<string> nodes;
    	set<string> read_nodes();
    	void display_nodes();

    	set<pair<string,string>> topology;
    	set<pair<string,string>> read_topology();
    	void display_topology();

    	set<string> selected_classes;
		set<string> read_selected_classes();
		void display_selected_classes();

    	set<tuple<string,string,string>> rules;
    	set<tuple<string,string,string>> read_rules(set<string>);
    	void display_rules();

    	set<tuple<string,string,string>> read_class(string);

    	map<string,int> abstract_nodes;
    	set<pair<int,int>> abstract_topology;
    	set<tuple<string,int,int>> abstract_rules; 
    
    public:
        void read_network();
        void set_selected_classes_dir(string input)
        {selected_classes_dir = input;}
        void create_abstract_network();
        int get_nodes_count()
        { return abstract_nodes.size();}

};


set<string> Network::read_nodes()
{
    set<string> routers;
    string line;
    std::ifstream infile(snapshot_dir + "/config.map" );
    int count = 1;
   	while (std::getline(infile, line))
    {
        std::istringstream iss(line);
        string t1, name;   
        if (!(iss >> t1 >> name  )) { break; } // error
        if(t1.compare(string("R")) != 0) { break; }
        name.erase (name.begin());
        routers.insert(name);
   	}   
    return routers; 
}

void Network::display_nodes()
{
	log(3) << endl << endl << "***NODES***" << endl;
	log(3) << nodes; 
}

set<pair<string,string>> Network::read_topology()
{
	set<pair<string,string>> from_to_pairs; 
	string line;

	std::ifstream infile(string(rocketfuel_dir + "/Topology.txt"));
	while (std::getline(infile, line))
	{
		std::istringstream iss(line);
		string fromstr, tostr;  
		if (!(iss >> fromstr >> tostr )) 
		{ 
			break; 
		} // error
		pair<string,string> from_to; 
		from_to= make_pair(fromstr,tostr);
		from_to_pairs.insert(from_to); 			
	}   
	return from_to_pairs; 
}

void Network::display_topology()
{
	log(3) << endl << endl << "***TOPOLOGY***" << endl;
	log(3) << topology;
}

set<string> Network::read_selected_classes()
{
	set<string> classes;
	classes = getdir(selected_classes_dir);
	return classes;
}

void Network::display_selected_classes()
{
	log(3) << endl << endl << "***SELECTED CLASSES***" << endl;
	log(3) << selected_classes;
}

set<tuple<string,string,string>> Network::read_class(string file) //packet from to
{
    set<tuple<string,string,string>> link; 
    string line;
    std::ifstream infile(string(string(selected_classes_dir + file )));
    while (std::getline(infile, line))
    {
        std::istringstream iss(line);
        string fromstr, tostr,  packetstr;        
        if (!(iss >> packetstr >> fromstr >> tostr ))
        {
        	break;
        } // error
        tuple<string,string,string> pair;
        pair= make_tuple (packetstr,fromstr, tostr);
        link.insert(pair);
    }   
    return link; 
}

set<tuple<string,string,string>> Network::read_rules(set<string> classes)
{
	set<tuple<string,string,string>> result; 
	for(auto class_it = classes.begin(); class_it != classes.end(); class_it++)
	{
		set<tuple<string,string,string>> returned = read_class(*class_it);
		result.insert(returned.begin(), returned.end()); 
	}
	return result;
}

void Network::display_rules()
{
	log(3) << endl << endl << "***RULES***" << endl;
	log(3) << rules;
}

void Network::read_network()
{
	nodes = read_nodes();
	display_nodes();
	topology = read_topology();
	display_topology();
	selected_classes = read_selected_classes();
	display_selected_classes();	
	rules = read_rules(selected_classes);
	display_rules();
}

void Network::create_abstract_network()
{
	int counter = 1;
	for(auto nodes_it = nodes.begin(); nodes_it != nodes.end(); nodes_it++)
	{
		abstract_nodes[*nodes_it] = counter;
		counter = counter + 1;
	}
	for(auto topology_it = topology.begin(); topology_it != topology.end(); ++topology_it)
	{
		if(abstract_nodes.find(topology_it->first) == abstract_nodes.end()) 
		{
		  abstract_nodes[topology_it->first] = counter;
		  counter++;
		} 
		if(abstract_nodes.find(topology_it->second) == abstract_nodes.end()) 
		{
		  abstract_nodes[topology_it->second] = counter;
		  counter++;
		} 

		abstract_topology.insert(make_pair(abstract_nodes[topology_it->first], abstract_nodes[topology_it->second]));
	}
	for(auto rules_it = rules.begin(); rules_it != rules.end(); ++rules_it)
	{
		string packet = std::get<0>(*rules_it);
		string node_from = std::get<1>(*rules_it);
		string node_to = std::get<2>(*rules_it);

		if(abstract_nodes.find(node_from) == abstract_nodes.end()) 
		{
		  abstract_nodes[node_from] = counter;
		  counter++;
		} 
		if(abstract_nodes.find(node_to) == abstract_nodes.end()) 
		{
		  abstract_nodes[node_to] = counter;
		  counter++;
		} 
		abstract_rules.insert(make_tuple( packet, abstract_nodes[node_from], abstract_nodes[node_to]));
		//cout << std::get<0>(*rules_it) << " " << abstract_nodes[ std::get<1>(*rules_it)] << " " << abstract_nodes[ std::get<2>(*rules_it)] << endl ; 
	}

	log(3) << abstract_nodes;
	log(3) << abstract_topology; 
	log(3) << abstract_rules; 
}


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


	public: 
		void read_automata();	
		void parse_automata();
};

void Automata::read_automata()
{
	std::ifstream infile("automata.txt");
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





int main()
{
	try{
		Network n1;
		n1.set_selected_classes_dir(string("data_set/RocketFuel/selected/"));
		n1.read_network();
		n1.create_abstract_network();

		Automata a1; 
		a1.read_automata();
		a1.parse_automata();
		
	}
	catch(...)	
	{	log(10) << "exception caught";
	}
}


