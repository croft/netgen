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
public:
    set<int> states;
    int start_state;
    vector<int> symbols;
    //map<string,int> symbols;
    //vector<string> symbols_string;
    map<pair<int,int>,int> transitions;
    set<int> final_states;
    int dead_state;
    
    
    friend std::ostream& operator<< (std::ostream& stream, const Automata& a1) {
        stream << "\nAutomata \nstates:" << a1.states;
        stream << "\nstart state: " << a1.start_state;
        stream << "\nsymbols:" <<  a1.symbols;
        stream << "\ntransitions: " << a1.transitions;
        stream << "\nfinal_states: " << a1.final_states;
        stream << "\ndead_state: " << a1.dead_state;
    }
        
        
};

#endif
