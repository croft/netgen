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
        set<int> abstract_nodes; 
        set<pair<int,int>> abstract_topology;
        map<pair<int,int>,int> abstract_rules; 
        
        map<int,set<int>> abstract_immutable_nodes;
        map<int,set<int>> abstract_egress_nodes; 
        map<int,set<int>> abstract_source_nodes; 
        
        map<pair<int,int>,int> abstract_od; 
        map<string,int> abstract_pc_map;

            
        void Compute_OD();    
};

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
    
    //cout << "\n\nAbstract OD\n" << abstract_od; 
}

    


#endif 