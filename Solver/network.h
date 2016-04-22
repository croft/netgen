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
#include "z3++.h"

using namespace std;
using namespace z3;


class Network
{	
	friend class Solver;

    public:
       	set<string> nodes;
    	set<string> read_nodes();
    	void display_nodes();

    	set<pair<string,string>> topology;
    	set<pair<string,string>> read_topology();
    	void display_topology();
    	
    	set<string> selected_class_files;
    	set<string> selected_classes; 
		set<tuple<string,string,string>> read_class(string);

    	set<tuple<string,string,string>> rules;
    	set<tuple<string,string,string>> read_rules(set<string>);
    	void display_rules();
    	
    	
    	map<string,int> abstract_nodes_map;
    	set<int> abstract_nodes; 
    	set<pair<int,int>> abstract_topology;
        
    	map<pair<int,int>,int> abstract_rules; 
        map<string,int> abstract_pc_map;
        

    	//for later: add immutable nodes in/from sutomata specification... 
    	map<int,set<int>> abstract_immutable_nodes;

    	map<int,set<int>> abstract_egress_nodes; 
    	map<int,set<int>> abstract_source_nodes; 

    	string selected_classes_dir;
    	string config_map_file;
    	string topology_file;

        Network(string config_map_file_input, string topology_file_input, string selected_classes_input)
        	:config_map_file{config_map_file_input},
        	topology_file{topology_file_input},
        	selected_classes_dir{selected_classes_input} {};

    	void read_network();
        void create_abstract_network();
        
        map<pair<int,int>,int> abstract_od; 
        void Compute_OD();

};


set<string> Network::read_nodes()
{
    set<string> routers;
    string line;
    std::ifstream infile(config_map_file);
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

	std::ifstream infile(topology_file);
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
        selected_classes.insert(packetstr);
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
	selected_class_files = getdir(selected_classes_dir);
	rules = read_rules(selected_class_files);
}

void Network::create_abstract_network()
{
    int pc_counter=1;
    for (auto pc_it = selected_classes.begin(); pc_it != selected_classes.end(); pc_it ++)
    {
        abstract_pc_map[*pc_it] = pc_counter; 
        pc_counter++;
    }
 
	int counter = 1;
	for(auto nodes_it = nodes.begin(); nodes_it != nodes.end(); nodes_it++)
	{
		abstract_nodes_map[*nodes_it] = counter;
		abstract_nodes.insert(counter);
		counter = counter + 1;

	}
    
    set<int> topo_incomming;
    set<int> topo_outgoing; 
     
    
	for(auto topology_it = topology.begin(); topology_it != topology.end(); ++topology_it)
	{
		if(abstract_nodes_map.find(topology_it->first) == abstract_nodes_map.end()) 
		{
		  abstract_nodes_map[topology_it->first] = counter;
		  abstract_nodes.insert(counter);
		  counter++;
		} 
		if(abstract_nodes_map.find(topology_it->second) == abstract_nodes_map.end()) 
		{
		  abstract_nodes_map[topology_it->second] = counter;
		  abstract_nodes.insert(counter);
		  counter++;
		} 
        
        topo_incomming.insert(abstract_nodes_map[topology_it->second]);
        topo_outgoing.insert(abstract_nodes_map[topology_it->first]);   
		
		abstract_topology.insert(make_pair(abstract_nodes_map[topology_it->first], abstract_nodes_map[topology_it->second]));
	}
    
	map<int,set<int>> outgoing, incomming; 


	for(auto rules_it = rules.begin(); rules_it != rules.end(); ++rules_it)
	{
		string packet = std::get<0>(*rules_it);
		string node_from = std::get<1>(*rules_it);
		string node_to = std::get<2>(*rules_it);

		if(abstract_nodes_map.find(node_from) == abstract_nodes_map.end()) 
		{
		  abstract_nodes_map[node_from] = counter;
		  abstract_nodes.insert(counter);
		  counter++;
		} 
		if(abstract_nodes_map.find(node_to) == abstract_nodes_map.end()) 
		{
		  abstract_nodes_map[node_to] = counter;
		  abstract_nodes.insert(counter);
		  counter++;
		} 

        //if node was not part of topo insert it... else is redundant
		abstract_topology.insert(make_pair(abstract_nodes_map[node_from],abstract_nodes_map[node_to]));
        topo_incomming.insert(abstract_nodes_map[node_to]);
        topo_outgoing.insert(abstract_nodes_map[node_from]); 
        
		abstract_rules[ make_pair( abstract_nodes_map[node_from], abstract_pc_map[packet]) ] = abstract_nodes_map[node_to];

		outgoing[abstract_pc_map[packet]].insert(abstract_nodes_map[node_from]);
		incomming[abstract_pc_map[packet]].insert(abstract_nodes_map[node_to]);

		log(3) << std::get<0>(*rules_it) << " " << abstract_nodes_map[ std::get<1>(*rules_it)] << " " << abstract_nodes_map[ std::get<2>(*rules_it)] << endl ; 
	}
    
    
    log(3) << outgoing << "\n";
    log(3) << incomming << "\n";
    
    //topology contains all links.. 
    
    // for( auto pc_it = abstract_pc_map.begin(); pc_it != abstract_pc_map.end(); pc_it++ )
    // {	
    //   int pc_int = pc_it->second;
    //  
    //   // is topo_incomming superset of incoming? similarly for outgoing..
    //   outgoing[pc_int].insert(topo_outgoing.begin(),topo_outgoing.end()); 
    //   incomming[pc_int].insert(topo_incomming.begin(),topo_incomming.end()); 
    //  
    //   std::set_difference(abstract_nodes.begin(), abstract_nodes.end(), outgoing[pc_int].begin(), outgoing[pc_int].end(),
    //                       std::inserter(abstract_egress_nodes[pc_int], abstract_egress_nodes[pc_int].end()));
    //
    //   std::set_difference(abstract_nodes.begin(), abstract_nodes.end(), incomming[pc_int].begin(), incomming[pc_int].end(),
    //                       std::inserter(abstract_source_nodes[pc_int], abstract_source_nodes[pc_int].end()));
    //
    //  
    //     //cout << packet << "\n"; 
    //     //cout <<"\n" << outgoing[packet];
    // 	//cout <<"\n" << incomming[packet];
    // }

    
    set<int> not_incomming;
    set<int> not_outgoing; 
   
    std::set_difference(abstract_nodes.begin(), abstract_nodes.end(), topo_outgoing.begin(), topo_outgoing.end(),
                           std::inserter(not_outgoing, not_outgoing.end()));
    
    std::set_difference(abstract_nodes.begin(), abstract_nodes.end(), topo_incomming.begin(), topo_incomming.end(),
                      std::inserter(not_incomming, not_incomming.end()));

    for( auto pc_it = abstract_pc_map.begin(); pc_it != abstract_pc_map.end(); pc_it++ )
    {
        int pc_int = pc_it->second;
        abstract_source_nodes[pc_int] = not_incomming;
        abstract_egress_nodes[pc_int] = not_outgoing; 
        
        set<int> not_pc_outgoing;
        std::set_difference(abstract_nodes.begin(), abstract_nodes.end(), outgoing[pc_int].begin(), outgoing[pc_int].end(),
                           std::inserter(not_pc_outgoing, not_pc_outgoing.end()));
        
        
        set<int> null_nodes; 
        std::set_difference(not_pc_outgoing.begin(), not_pc_outgoing.end(), not_outgoing.begin(), not_outgoing.end(),
                           std::inserter(null_nodes, null_nodes.end()));        
        
        
        for(auto null_nodes_it = null_nodes.begin(); null_nodes_it != null_nodes.end(); null_nodes_it++ )
        {
            abstract_rules[ make_pair( *null_nodes_it, pc_int) ] = 0;
        }
    }
        
    cout << "\n\nNodes\n" << abstract_nodes;
    cout << "\n\nTopology\n" << abstract_topology; 
    cout << "\n\nRules\n" << abstract_rules; 
        
        
	cout << "\n\nSources\n" << abstract_source_nodes;
	cout << "\n\nEgress\n" << abstract_egress_nodes;
	
}


        

void Network::Compute_OD()
{
    for( auto pc_it = abstract_pc_map.begin(); pc_it != abstract_pc_map.end(); pc_it++ )
    { 
        int pc_int = pc_it->second;
        set<int> egress = abstract_egress_nodes[pc_int];
        
        //for( auto source_it = abstract_source_nodes[pc_int].begin(); source_it != abstract_source_nodes[pc_int].end(); source_it++ )
        for( auto source_it = abstract_nodes.begin(); source_it != abstract_nodes.end(); source_it++ )
        {
            int src = *source_it;
            int temp = src;  
            
            if( find( egress.begin(), egress.end(), temp) != egress.end()) 
            {
                abstract_od[make_pair(src,pc_int)] = src; 
                continue;
            }
            
            while( find( egress.begin(), egress.end(), temp) == egress.end()  && temp != 0)
            {
                temp =  abstract_rules[make_pair(temp,pc_int)];          
            } 
            
            abstract_od[make_pair(src,pc_int)] = temp;     
        }
    }
    
    cout << "\n\nAbstract OD\n" << abstract_od; 
}
    


#endif 