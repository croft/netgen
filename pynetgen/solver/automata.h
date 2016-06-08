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
};

#endif
