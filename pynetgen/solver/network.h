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
    /* Algorithm:
     * For each source node, search through packet class edges as a path
     * Once an egress node is reached, stop
     */
    for (auto pc_it = abstract_pc_map.begin(); pc_it != abstract_pc_map.end(); pc_it++)
    {
        int pc_int = pc_it->second;
        set<int> egress = abstract_egress_nodes[pc_int];
        set<int> sources = abstract_source_nodes[pc_int];
        map<int, int> pc_edges = map<int, int>();
        set<int> pc_egress = set<int>();

        for (auto rule : abstract_rules)
        {
            pc_edges[rule.first.first] = rule.second;
        }

        for (auto edge : pc_edges)
        {
            if (egress.find(edge.first) != egress.end())
            {
                pc_egress.insert(edge.first);
            }

            if (egress.find(edge.second) != egress.end())
            {
                pc_egress.insert(edge.second);
            }
        }

        abstract_egress_nodes[pc_int] = pc_egress;

        // drop node
        abstract_od[make_pair(0, pc_int)] = 0;

        for (auto node : egress)
        {
            abstract_od[make_pair(node, pc_int)] = node;
        }

        for (auto node : sources)
        {
            if (egress.find(node) != egress.end())
            {
                abstract_od[make_pair(node, pc_int)] = node;
                continue;
            }

            int curr = node;
            int prev = curr;

            while (pc_edges.find(curr) != pc_edges.end())
            {
                prev = curr;
                curr = pc_edges.find(curr)->second;

                if (prev == curr)
                {
                    break;
                }
            }

            if (egress.find(curr) != egress.end())
            {
                abstract_od[make_pair(node, pc_int)] = curr;
                continue;
            }
        }
    }

    /* cout << "\n\nAbstract OD\n" << abstract_od; */
}

#endif
