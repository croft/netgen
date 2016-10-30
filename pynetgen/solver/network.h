#ifndef NETWORK_H
#define NETWORK_H

#include <sys/types.h>
#include <dirent.h>
#include <errno.h>
#include <vector>
#include <queue>
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

class Network {
        friend class Solver;

       public:
        set<int> abstract_nodes;
        set<int> switches;
        set<pair<int, int>> abstract_topology;
        map<pair<int, int>, set<int>> abstract_rules;

        map<int, set<int>> abstract_immutable_nodes;
        map<int, set<int>> abstract_egress_nodes;
        map<int, set<int>> abstract_source_nodes;

        map<pair<int, int>, int> abstract_od;
        map<string, int> abstract_pc_map;
        bool dest_drop;

        void Compute_OD();
};

void Network::Compute_OD()
{
        /* Algorithm:
         * For each source node, search through packet class edges as a path
         * Once an egress node is reached, stop
         */
        /* if (dest_drop) */
        /* { */
        /* 	for (auto pc_it = abstract_pc_map.begin(); pc_it != abstract_pc_map.end(); pc_it++) */
        /* 	{ */
        /* 	    int pc_int = pc_it->second; */
        /* 	    set<int> sources = abstract_source_nodes[pc_int]; */

        /* 	    abstract_od[make_pair(0, pc_int)] = 0; */
        /* 	    for (auto node: sources) */
        /* 	    { */
        /* 		abstract_od[make_pair(node, pc_int)] = 0; */
        /* 	    } */
        /* 	} */

        /* 	return; */
        /* } */

        for (auto pc_it = abstract_pc_map.begin(); pc_it != abstract_pc_map.end(); pc_it++) {
                int pc_int = pc_it->second;
                set<int> egress = abstract_egress_nodes[pc_int];
                set<int> sources = abstract_source_nodes[pc_int];
                set<int> pc_egress = set<int>();

                // this is just so we don't have to generate all possile paths, but
                // assumes egress is node n or n-1 in path of length n
                for (auto rule : abstract_rules) {
                        for (auto link : rule.second) {
                                if (abstract_rules.find(make_pair(link, rule.first.second)) == abstract_rules.end() or link == 0) {
                                        // if it's not an egress, there's still a rule for node->0, so skip it
                                        if (link == 0 && egress.find(rule.first.first) == egress.end()) {
                                                continue;
                                        }

                                        // if it's a switch add it, otherwise, add prev hop
                                        if (switches.find(link) != switches.end()) {
                                                // actually...for now ignore it
                                                pc_egress.insert(link);
                                        }
                                        else {
                                                pc_egress.insert(rule.first.first);
                                        }
                                }
                        }
                }

                if (dest_drop) {
                        pc_egress.insert(0);
                }

                abstract_egress_nodes[pc_int] = set<int>();
                abstract_egress_nodes[pc_int] = pc_egress;

                // cout << "PC GRESS: " << pc_egress << endl;
                /* cout << "SOURCES: " << sources << endl; */

                // drop node
                abstract_od[make_pair(0, pc_int)] = 0;

                for (auto node : pc_egress) {
                        abstract_od[make_pair(node, pc_int)] = node;
                }

                if (dest_drop) {
                        for (auto node : sources) {
                                abstract_od[make_pair(node, pc_int)] = 0;
                        }

                        continue;
                }

                // DFS through paths looking for egresses
                for (auto node : sources) {
                        if (pc_egress.find(node) != pc_egress.end()) {
                                abstract_od[make_pair(node, pc_int)] = node;
                                continue;
                        }

                        queue<int> q = queue<int>();
                        q.push(node);

                        while (!q.empty()) {
                                int curr = q.back();
                                q.pop();

                                if (pc_egress.find(curr) != pc_egress.end()) {
                                        abstract_od[make_pair(node, pc_int)] = curr;
                                        break;
                                }

                                /* if (abstract_rules.find(make_pair(curr, pc_int)) == abstract_rules.end()) */
                                /* { */
                                /*     abstract_od[make_pair(node, pc_int)] = curr; */
                                /*     break; */
                                /* } */

                                for (auto nexthop : abstract_rules[make_pair(curr, pc_int)]) {
                                        q.push(nexthop);
                                }
                        }
                }
        }
}

#endif
