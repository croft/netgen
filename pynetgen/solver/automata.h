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

class Automata {
       public:
        set<int> states;
        int start_state;
        vector<int> symbols;
        // map<string,int> symbols;
        // vector<string> symbols_string;
        map<pair<int, int>, int> transitions;
        set<int> final_states;
        int dead_state;

        map<int,int> reduced_symbols;
        map<int,int> inverse_reduced_symbols;
        map<pair<int, int>, int> reduced_transitions;
        int num_reduced_symbol;
        void Compute_symbol_reduction();
        void Compute_transition_reduction(); 
        
        
        friend std::ostream &operator<<(std::ostream &stream, const Automata &a1)
        {
                stream << "\nAutomata \nstates:" << a1.states;
                stream << "\nstart state: " << a1.start_state;
                stream << "\nsymbols:" << a1.symbols;
                stream << "\ntransitions: " << a1.transitions;
                stream << "\nfinal_states: " << a1.final_states;
                stream << "\ndead_state: " << a1.dead_state;
        }
};

void Automata::Compute_symbol_reduction()
{       
        std::deque<int> workspace(symbols.begin(),symbols.end());
        int K = -1;
        
        while(!workspace.empty())
        {       
                int element = workspace.front();
                workspace.pop_front();
                K = K + 1;
                reduced_symbols[element] = K;
                inverse_reduced_symbols[K] = element;
                
                //for all other elements in queue
                for (auto symbol_it = workspace.begin(); symbol_it != workspace.end(); ) 
                {       
                        //if element matches with some other symbol for all states
                        int flag = true;
                        for(auto st: states)
                        {
                                if(transitions[make_pair(st,*symbol_it)] != transitions[make_pair(st,element)])
                                {
                                        flag = false;
                                        break;
                                }
                        }        
                        
                        //if so delete the symbol from workspace, and assign it the index of element
                        if(flag == true)
                        {
                                 reduced_symbols[*symbol_it] = K;
                                 symbol_it = workspace.erase(symbol_it);
                        }
                        //else move on to the next symbol 
                        else
                        {
                                symbol_it++;
                        }
                }     
        }
        num_reduced_symbol = K;
}

void Automata::Compute_transition_reduction()
{
        Compute_symbol_reduction();
                        
        for( auto st : states)
        {
                for( auto mp : inverse_reduced_symbols)
                {
                        //reduced_transition[state, reduced_symbol] = transitions[state,symbol]
                        //correctness assured by the fact that all equivalence symbols, map to same state
                        reduced_transitions[make_pair(st, mp.first)] = transitions[make_pair(st, mp.second)];
                }
        }                
}


#endif

        // void Network::Compute_AlphabetCongruence()
        // {
        //       index = 0;
        //       set<int> result;
        //         for all alphabet: 10000
        //                 empty string
        //                 25 : for all state: 5
        //                         concat string 5
        //                 insert(result,string) :log(5)
        //                 uniq[collection], check and insert (10)

        //                 if(insrted)
        //                         index++;

        //                         result[alphabet] = k;

        // workspace = all alphabets...10000
        // while (workspace != empty) 10
        //         pick one form workspace
        //         50,000
        //         for all alphabet
        //                 for all q
        //                         check if delta is is_same: concat really not helpful...
        //         remove all alphabet 10000
        // }