#ifndef NETWORK_H
#define NETWORK_H


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

#include "utils.h"

using namespace std;



class Network
{
    private:
       	set<string> nodes;
    	set<string> read_nodes();
    	void display_nodes();

    	set<pair<string,string>> topology;
    	set<pair<string,string>> read_topology();
    	
    	set<string> selected_classes;
		set<string> read_selected_classes();
		
    	set<tuple<string,string,string>> rules;
    	set<tuple<string,string,string>> read_rules(set<string>);
    	
    	set<tuple<string,string,string>> read_class(string);

    	map<string,int> abstract_nodes;
    	set<pair<int,int>> abstract_topology;
    	set<tuple<string,int,int>> abstract_rules; 

    	string selected_classes_dir;
    	string rocketfuel_dir;
    	string snapshot_dir;
    
    public:
        void read_network();
        void create_abstract_network();
        int get_nodes_count()
        { return abstract_nodes.size();}

        Network(string rocketfule_input, string snapshot_input, string selected_classes_input) 
        : rocketfuel_dir{rocketfule_input},
        snapshot_dir{snapshot_input},
        selected_classes_dir{selected_classes_input} {};

        void display_topology();
    	void display_selected_classes();
    	void display_rules();

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
	cout << endl << endl << "***NODES***" << endl;
	cout << nodes; 
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
	cout << endl << endl << "***TOPOLOGY***" << endl;
	cout << topology;
}

set<string> Network::read_selected_classes()
{
	set<string> classes;
	classes = getdir(selected_classes_dir);
	return classes;
}

void Network::display_selected_classes()
{
	cout << endl << endl << "***SELECTED CLASSES***" << endl;
	cout << selected_classes;
}

set<tuple<string,string,string>> Network::read_class(string file) //packet from to
{
    set<tuple<string,string,string>> link; 
    string line;
    std::ifstream infile(string(selected_classes_dir + "/"+ file ));
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
	cout << endl << endl << "***RULES***" << endl;
	cout << rules;
}

void Network::read_network()
{
	nodes = read_nodes();
	topology = read_topology();
	selected_classes = read_selected_classes();	
	rules = read_rules(selected_classes);
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
		
		log(3) << std::get<0>(*rules_it) << " " << abstract_nodes[ std::get<1>(*rules_it)] << " " << abstract_nodes[ std::get<2>(*rules_it)] << endl ; 
	}

	log(3) << abstract_nodes;
	log(3) << abstract_topology; 
	log(3) << abstract_rules; 
}



#endif 