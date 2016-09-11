#include <boost/python.hpp>
#include <boost/type_traits/integral_constant.hpp>
#include <string>
#include <iostream>
#include <vector>
#include <tuple>
#include <set>
#include <thread>
#include <mutex>
#include <ctime>
#include <math.h>
#include "utils.h"
#include "solver.h"
#include "network.h"
#include "automata.h"
#include "z3++.h"
#include "recursive_definitions.h"
#include "config.h"

using namespace std;
namespace py = boost::python;
using namespace z3;

int SIZE;

#if THEORY == LIA
#define SORT     ctx.int_sort()
#elif THEORY == BV
#define SORT     ctx.bv_sort(SIZE)
#elif THEORY == LRA
#define SORT     ctx.real_sort()
#endif


// -----------------------------------------------------------------------------
// PYTHON TYPES CONVERSION
// -----------------------------------------------------------------------------
template <typename T>
std::vector<T> pylist_to_vector(const py::object& obj)
{
    std::vector<T> vect(len(obj));
    for (unsigned long i = 0; i < vect.size(); i++)
    {
        vect[i] = py::extract<T>(obj[i]);
    }

    return vect;
}

template <typename T>
std::set<T> pylist_to_set(const py::object& obj)
{
    std::set<T> st;
    for (unsigned long i = 0; i < len(obj); i++)
    {
        st.insert(py::extract<T>(obj[i]));
    }

    return st;
}

// std::vector<tuple<int,int>> pylist_to_tuplist2(const py::object& obj) {
//     std::vector<tuple<int,int>> vect(len(obj));
//     int j, k;
//     for (unsigned long i = 0; i < vect.size(); i++)
//     {
//      j = py::extract<int>(obj[i][0]);
//      k = py::extract<int>(obj[i][1]);
//      vect[i] = make_tuple(j, k);
//      //cout << vect[i] << endl;
//     }

//     return vect;
// }

std::vector<std::tuple<int,int,int>> pylist_to_tuplist3(const py::object& obj)
{
    std::vector<std::tuple<int,int,int>> vect(len(obj));
    int j, k, m;
    for (unsigned long i = 0; i < vect.size(); i++)
    {
        j = py::extract<int>(obj[i][0]);
        k = py::extract<int>(obj[i][1]);
        m = py::extract<int>(obj[i][2]);
        vect[i] = make_tuple(j, k, m);
        //cout << vect[i] << endl;
    }

    return vect;
}

std::map<std::pair<int,int>,int> pylist_to_map_pair(const py::object& obj)
{
    std::map<std::pair<int,int>,int> mpr;
    int j, k, m;
    for (unsigned long i = 0; i < len(obj); i++)
    {
        j = py::extract<int>(obj[i][0]);
        k = py::extract<int>(obj[i][1]);
        m = py::extract<int>(obj[i][2]);

        mpr[make_pair(j,k)] =  m;
        //cout << vect[i] << endl;
    }

    return mpr  ;
}

std::set<std::pair<int,int>> pylist_to_set_pair(const py::object& obj)
{
    std::set<std::pair<int,int>> spr;
    int j, k;
    for (unsigned long i = 0; i < len(obj); i++)
    {
        j = py::extract<int>(obj[i][0]);
        k = py::extract<int>(obj[i][1]);
        spr.insert(make_pair(j,k));
        //cout << vect[i] << endl;
    }

    return spr  ;
}

// -----------------------------------------------------------------------------

typedef std::vector<std::tuple<int, int>> model_t;

class AbstractNetwork
{
public:
    Automata a1;
    Network n1;
    set<int> pcids;
    set<int> immutables;
    set<int> egresses;
    set<int> sources;
    std::vector<std::tuple<int,int,int>> arules;

    AbstractNetwork() {}

    AbstractNetwork(const AbstractNetwork &net);

    AbstractNetwork(py::list _nodes,
                    py::list _switches,
                    py::list _sources,
                    py::list _egresses,
                    py::list _immutables,
                    py::list _topology,
                    py::list _classes,
                    py::list _fsa,
                    py::list _states,
                    py::list _symbols,
                    py::list _finals,
                    int _initial,
                    int _dead,
                    int _drop);

    void set_pc(int pcid);
};

AbstractNetwork::AbstractNetwork(const AbstractNetwork &net)
{
    a1 = net.a1;
    n1.abstract_nodes = net.n1.abstract_nodes;
    n1.switches = net.n1.switches;
    n1.abstract_topology = net.n1.abstract_topology;
    n1.dest_drop = net.n1.dest_drop;
    pcids = net.pcids;
    immutables = net.immutables;
    egresses = net.egresses;
    sources = net.sources;
    arules = net.arules;
}

void AbstractNetwork::set_pc(int pcid)
{
    n1.abstract_pc_map = map<string,int>();
    n1.abstract_pc_map["1"] = 1;

    n1.abstract_immutable_nodes = map<int,set<int>>();
    n1.abstract_egress_nodes = map<int,set<int>>();
    n1.abstract_source_nodes = map<int,set<int>>();

    n1.abstract_immutable_nodes[1] = immutables;
    n1.abstract_egress_nodes[1] = egresses;
    n1.abstract_source_nodes[1] = sources;

    n1.abstract_rules = map<pair<int,int>,set<int>>();
    n1.abstract_od = map<pair<int,int>,int>();

    for (auto tup : arules)
    {
        if (std::get<1>(tup) == pcid)
        {
            int from = std::get<0>(tup);
            int pcid = std::get<1>(tup);
            int to = std::get<2>(tup);

            // hardcode current PC to 1
            pair<int, int> key = make_pair(from, 1);

            if (n1.abstract_rules.find(key) == n1.abstract_rules.end())
            {
                n1.abstract_rules[key] = set<int>();
            }

            n1.abstract_rules[key].insert(to);
        }
    }

    // n1.abstract_egress_nodes[1] = set<int>();
    // for (auto tup : n1.abstract_rules)
    // {
    //     if (egresses.find(tup.first.first) != egresses.end())
    //     {
    //         n1.abstract_egress_nodes[1].insert(tup.first.first);
    //     }
    //     if (egresses.find(tup.second) != egresses.end())
    //     {
    //         n1.abstract_egress_nodes[1].insert(tup.second);
    //     }
    // }
    // cout << "PRE EGRESSES: " << n1.abstract_egress_nodes[1] << endl;

    n1.abstract_egress_nodes[1] = egresses;
    n1.Compute_OD();

    n1.abstract_egress_nodes[1] = set<int>();

    // per-packet class egresses are just ODs
    for (auto tup : n1.abstract_od)
    {
        if (tup.second != 0)
        {
            n1.abstract_egress_nodes[1].insert(tup.second);
        }
    }

    if (n1.dest_drop)
    {
        n1.abstract_egress_nodes[1].insert(0);
    }

    // cout << "RULES : " << n1.abstract_rules << endl;
    // cout << "OD: " << n1.abstract_od << endl;
    // cout << "EGRESSES: " << n1.abstract_egress_nodes[1] << endl;
}

AbstractNetwork::AbstractNetwork(py::list _nodes,
                                 py::list _switches,
                                 py::list _sources,
                                 py::list _egresses,
                                 py::list _immutables,
                                 py::list _topology,
                                 py::list _classes,
                                 py::list _fsa,
                                 py::list _states,
                                 py::list _symbols,
                                 py::list _finals,
                                 int _initial,
                                 int _dead,
                                 int _drop)
{
    a1.states = pylist_to_set<int>(_states);
    a1.symbols = pylist_to_vector<int>(_symbols);
    a1.transitions = pylist_to_map_pair(_fsa);
    a1.final_states = pylist_to_set<int>(_finals);
    a1.start_state = _initial;
    a1.dead_state = _dead;

    n1.switches = pylist_to_set<int>(_switches);
    n1.abstract_nodes =  pylist_to_set<int>(_nodes);
    n1.abstract_topology = pylist_to_set_pair(_topology);
    n1.dest_drop = _drop == 1;

    arules = pylist_to_tuplist3(_classes);
    immutables = pylist_to_set<int>(_immutables);
    sources = pylist_to_set<int>(_sources);
    egresses = pylist_to_set<int>(_egresses);

    pcids = set<int>();
    for (auto cls: arules)
    {
        pcids.insert(std::get<1>(cls));
    }
}

class ISolver
{
public:
    virtual py::list solve() = 0;
    virtual py::list get_perf_counters() = 0;
};

class SolverBase : public ISolver
{
public:
    SolverBase(AbstractNetwork _network) { network = _network; }
    py::list get_perf_counters();

protected:
    AbstractNetwork network;
    std::vector<std::tuple<int, std::string, double>> perfCounters;
};

py::list SolverBase::get_perf_counters()
{
    py::list ret;

    for (auto counter: perfCounters)
    {

        ret.append(py::make_tuple(get<0>(counter),
                                  get<1>(counter),
                                  get<2>(counter)));
    }

    return ret;
}

const int NUM_THREADS = 10;
std::mutex pcidq_lock;
std::mutex cache_lock;
std::mutex solutions_lock;

// class MultiThreadedCachingSolver : public SolverBase
// {
// public:
//     MultiThreadedCachingSolver(AbstractNetwork _network) : SolverBase(_network) { }
//     py::list solve();

// protected:
//     AbstractNetwork thread_nets[NUM_THREADS];
//     std::vector<model_t> cache;
//     py::list solutions;
//     std::vector<int> pcid_queue;

//     int next_pcid();
//     void solver_thread(int id);
//     void iterative_solve(int pcid, AbstractNetwork _network, model_t& ret);
//     void cached_solve(int pcid, model_t prev_model, AbstractNetwork _network, model_t& ret);
// };

// int MultiThreadedCachingSolver::next_pcid()
// {
//     pcidq_lock.lock();
//     int next = 0;
//     if (!pcid_queue.empty())
//     {
//         next = pcid_queue.back();
//         pcid_queue.pop_back();
//     }

//     pcidq_lock.unlock();
//     return next;
// }

// void MultiThreadedCachingSolver::solver_thread(int id)
// {
//     cout << "Starting thread " << id;
//     int cache_misses = 0;
//     int solves = 0;
//     int cache_hits = 0;

//     AbstractNetwork _network = thread_nets[id];
//     int pcid = next_pcid();
//     while (pcid > 0)
//     {
//         model_t result;

//         cache_lock.lock();
//         int len = cache.size();
//         cache_lock.unlock();

//         int model_size = 0;
//         bool skip_cache = false;

//         if (cache.size() > 0)
//         {
//             model_size = cache.back().size();
//             skip_cache = model_size == 1;
//         }

//         // if prev model k=1, skip
//         // only try as many prev solutions as k
//         // start at back of cache
//         for (int i = 0; i < len && !skip_cache && i < model_size; i++)
//         {
//             cache_lock.lock();
//             model_t prev_model = cache[len-i-1];
//             cache_lock.unlock();

//             cached_solve(pcid, prev_model, _network, result);
//             if (result.empty())
//             {
//                 cache_misses++;
//             }
//             else
//             {
//                 cache_hits++;
//                 break;
//             }

//             cout << id << " done cache" << endl;
//         }

//         if (result.empty())
//         {
//             solves++;
//             iterative_solve(pcid, _network, result);

//             if (!result.empty())
//             {
//                 cache_lock.lock();
//                 //if (cache.size() < 5)
//                 {
//                     cache.push_back(result);
//                 }
//                 cache_lock.unlock();
//             }
//         }

//         if (result.empty())
//         {
//             cout << "No model found" << endl;
//         }
//         else
//         {
//             solutions_lock.lock();
//             for (auto tup : result)
//             {
//                 solutions.append(py::make_tuple(pcid,
//                                                 std::get<0>(tup),
//                                                 std::get<1>(tup)));
//             }
//             solutions_lock.unlock();
//         }

//         pcid = next_pcid();
//     }

//     return;
// }

// void MultiThreadedCachingSolver::iterative_solve(int pcid, AbstractNetwork _network, model_t& ret)
// {
//     clock_t begin, end;
//     double elapsed_ms;
//     _network.set_pc(pcid);

//     for(int k=1; k <= _network.n1.abstract_nodes.size() ; k++)
//     {
//         std::cout << "Starting phase(MultiThreadedCachingSolver::iterative_solve): " << k << endl;
//         context ctx;
//         Solver s1(ctx, _network.n1, k);

//         begin = clock();
//         s1.define_k_rules();

// #if ENCODING == MACRO
//         s1.delta_satisfies_topology();
// #elif ENCODING == UF
//         func_decl topology = z3::function("topology", SORT, SORT, ctx.bool_sort());
//         s1.delta_satisfies_topology_uf(topology);
// #endif
//         s1.delta_satisfies_non_mutable();
//         s1.delta_satisfies_not_egress();
//         s1.delta_satisfies_not_existing();

//         func_decl cycle = z3::function("cycle", SORT, SORT, SORT);
//         s1.execute_recursive(Cyclicity(ctx,cycle));

//         func_decl dest = z3::function("dest", SORT, SORT, SORT);
//         s1.execute_recursive(Compute_Dest(ctx, dest, _network.n1));

//         func_decl rho = z3::function("rho", SORT, SORT, SORT);
//         func_decl delta = z3::function("delta", SORT, SORT, SORT);
//         s1.execute_recursive(Modified_Functionality(ctx,
//                                                     rho,
//                                                     delta,
//                                                     _network.a1,
//                                                     _network.n1.abstract_nodes));
//         s1.accept_automata(rho,_network.a1);

//         end = clock();
//         elapsed_ms = double(end - begin) / (CLOCKS_PER_SEC/1000);
//         perfCounters.push_back(make_tuple(k, "query constr", elapsed_ms));

//         cout << "solving" << endl;
//         begin = clock();
//         Z3_model m = s1.solve_z3();
//         end = clock();
//         elapsed_ms = double(end - begin) / (CLOCKS_PER_SEC/1000);
//         perfCounters.push_back(make_tuple(k, "z3 solve", elapsed_ms));

//         if(m)
//         {
//             model m1(ctx, m);
//             // cout << "\n\nModel\n" << m1;
//             cout << "Model found" << endl;
//             for( int index = 0; index < k; index++)
//             {
//                 int int_to, int_from;
//                 Z3_get_numeral_int(ctx, m1.eval(s1.n[index], true), &int_to);
//                 Z3_get_numeral_int(ctx, m1.eval(s1.n1[index], true), &int_from);
//                 ret.push_back(std::make_tuple(int_to, int_from));
//             }

//             break;
//         }
//     }
// }

// void MultiThreadedCachingSolver::cached_solve(int pcid, model_t prev_model, AbstractNetwork _network,
//     model_t& ret)
// {
//     clock_t begin, end;
//     double elapsed_ms;
//     _network.set_pc(pcid);
//     int k = prev_model.size();

//     context ctx;
//     Solver s1(ctx, _network.n1, k);

//     begin = clock();

//     s1.define_k_rules();
//     s1.define_prev_model(prev_model);

// // #if ENCODING == MACRO
// //     s1.delta_satisfies_topology();
// // #elif ENCODING == UF
// //     func_decl topology = z3::function("topology", SORT, SORT, ctx.bool_sort());
// //     s1.delta_satisfies_topology_uf(topology);
// // #endif
    
//     s1.delta_satisfies_topology();
    
//     s1.delta_satisfies_non_mutable();
//     s1.delta_satisfies_not_egress();
//     s1.delta_satisfies_not_existing();

//     func_decl cycle = z3::function("cycle", SORT, SORT, SORT);
//     s1.execute_recursive(Cyclicity(ctx, cycle));

//     func_decl dest = z3::function("dest", SORT, SORT, SORT);
//     s1.execute_recursive(Compute_Dest(ctx, dest, _network.n1));

//     func_decl rho = z3::function("rho", SORT, SORT, SORT);
//     func_decl delta = z3::function("delta", SORT, SORT, SORT);
//     s1.execute_recursive(Modified_Functionality(ctx,
//                                                 rho,
//                                                 delta,
//                                                 _network.a1,
//                                                 _network.n1.abstract_nodes));
//     s1.accept_automata(rho, _network.a1);

//     end = clock();
//     elapsed_ms = double(end - begin) / (CLOCKS_PER_SEC/1000);
//     perfCounters.push_back(make_tuple(k, "check query constr", elapsed_ms));

//     cout << "checking" << endl;
//     begin = clock();
//     Z3_model m = s1.solve_z3();
//     end = clock();
//     elapsed_ms = double(end - begin) / (CLOCKS_PER_SEC/1000);
//     perfCounters.push_back(make_tuple(k, "check z3", elapsed_ms));

//     if(m)
//     {
//         model m1(ctx, m);
//         cout << "Check SAT" << endl;
//         for( int index = 0; index < k; index++)
//         {
//             int int_to, int_from;
//             Z3_get_numeral_int(ctx, m1.eval(s1.n[index], true), &int_to);
//             Z3_get_numeral_int(ctx, m1.eval(s1.n1[index], true), &int_from);
//             ret.push_back(std::make_tuple(int_to, int_from));
//         }
//     }
//     else
//     {
//         cout << "Check UNSAT" << endl;
//     }
// }

// py::list MultiThreadedCachingSolver::solve()
// {
//     SIZE = ceil((float)log2(network.n1.abstract_nodes.size()))+2;
//     std::thread threads[NUM_THREADS];

//     for (auto pcid : network.pcids)
//     {
//         pcid_queue.push_back(pcid);
//     }

//     for (int i = 0; i < NUM_THREADS; i++)
//     {
//         // give thread private abstractnetwork
//         thread_nets[i] = AbstractNetwork(network);
//         threads[i] = std::thread(&MultiThreadedCachingSolver::solver_thread, this, i);
//     }

//     for (int i = 0; i < NUM_THREADS; i++)
//     {
//         threads[i].join();
//     }

//     cout << "CACHE SIZE: " << cache.size() << endl;

//     return solutions;
// }

// class DefaultSolver : public SolverBase
// {
// public:
//     DefaultSolver(AbstractNetwork _network) : SolverBase(_network) { }
//     py::list solve();
// };

// py::list DefaultSolver::solve()
// {
//     py::list ret;
//     SIZE = ceil((float)log2(network.n1.abstract_nodes.size()))+2;
//     cout << "\nSIZE = " << SIZE << "\n";
//     clock_t begin, end;
//     double elapsed_ms;

//     for (auto pcid : network.pcids)
//     {
//         network.set_pc(pcid);

//         for(int k=1; k <= network.n1.abstract_nodes.size() ; k++)
//         {
//             std::cout << "Starting phase(DefaultSolver::solve): " << k << endl;
//             context ctx;
//             Solver s1(ctx, network.n1, k);

//             begin = clock();
//             s1.define_k_rules();

// #if ENCODING == MACRO
//             s1.delta_satisfies_topology();
// #elif ENCODING == UF
//             func_decl topology = z3::function("topology", SORT, SORT, ctx.bool_sort());
//             s1.delta_satisfies_topology_uf(topology);
// #endif
//             s1.delta_satisfies_non_mutable();
//             s1.delta_satisfies_not_egress();
//             s1.delta_satisfies_not_existing();

//             // func_decl eqstate = z3::function("eqstate", SORT, SORT);
//             // s1.define_eqstate(eqstate);


//             func_decl cycle = z3::function("cycle", SORT, SORT, SORT);
//             s1.execute_recursive(Cyclicity(ctx, cycle));

//             func_decl dest = z3::function("dest", SORT, SORT, SORT);
//             s1.execute_recursive(Compute_Dest(ctx, dest, network.n1));

//             func_decl rho = z3::function("rho", SORT, SORT, SORT);
//             func_decl delta = z3::function("delta", SORT, SORT, SORT);
//             s1.execute_recursive(Modified_Functionality(ctx,
//                                                         rho,
//                                                         delta,
//                                                         network.a1,
//                                                         network.n1.abstract_nodes));
//             s1.accept_automata(rho, network.a1);

//             end = clock();
//             elapsed_ms = double(end - begin) / (CLOCKS_PER_SEC/1000);
//             perfCounters.push_back(make_tuple(k, "query constr", elapsed_ms));

//             cout << "solving" << endl;
//             begin = clock();
//             Z3_model m = s1.solve_z3();
//             end = clock();
//             elapsed_ms = double(end - begin) / (CLOCKS_PER_SEC/1000);
//             perfCounters.push_back(make_tuple(k, "z3 solve", elapsed_ms));

//             // if (pcid > 1 && k == 2)
//             if (k == 2)
//             {
//                 // cout << network.n1.abstract_rules << endl;
//                 //s1.print_query();
//             }

//             if(m)
//             {
//                 model m1(ctx, m);
//                 // cout << "\n\nModel\n" << m1;
//                 cout << "Model found" << endl;
//                 for( int index = 0; index < k; index++)
//                 {
//                     const char* from = Z3_get_numeral_string (ctx, m1.eval(s1.n[index], true));
//                     const char* to = Z3_get_numeral_string(ctx, m1.eval(s1.n1[index], true));

//                     ret.append(py::make_tuple(pcid, from, to));
//                 }

//                 break;
//             }
//         }
//     }

//     return ret;
// }

class CachingSolver : public SolverBase
{
public:
    CachingSolver(AbstractNetwork _network) : SolverBase(_network) { }
    py::list solve();

protected:
    std::vector<model_t> cache;
    model_t iterative_solve(int pcid);
    model_t cached_solve(int pcid, model_t prev_model);
};

model_t CachingSolver::iterative_solve(int pcid)
{
    model_t ret = model_t();
    clock_t begin, end;
    double elapsed_ms;
    network.set_pc(pcid);

    for(int k=1; k <= network.n1.abstract_nodes.size() ; k++)
    {
        std::cout << "Starting phase: " << k << endl;
        context ctx;
        Solver s1(ctx, network.n1, k);

        begin = clock();
        s1.define_k_rules();

#if TOPO == MACROTOPO
        s1.delta_satisfies_topology();
#elif TOPO == UFTOPO
        func_decl topology = z3::function("topology", SORT, SORT, ctx.bool_sort());
        s1.delta_satisfies_topology_uf(topology);
#endif        
        
#if STATE == EQSTATE     
        map<int,int> mapping; 
        mapping[0] = 0; 
        mapping[1] = 1; 
        
        for( int i = 0; i<= network.n1.abstract_nodes.size(); i++)
        {  
               mapping[i] = i; 
        }
         
        func_decl eqstate = z3::function("eqstate", SORT, SORT);
        s1.define_eqstate(eqstate,mapping);
#endif
        
        s1.delta_satisfies_non_mutable();
        s1.delta_satisfies_not_egress();
        s1.delta_satisfies_not_existing();

        func_decl cycle = z3::function("cycle", SORT, SORT, SORT);
        s1.execute_recursive(Cyclicity(ctx,cycle));

        func_decl dest = z3::function("dest", SORT, SORT, SORT);
        s1.execute_recursive(Compute_Dest(ctx, dest, network.n1));

        func_decl rho = z3::function("rho", SORT, SORT, SORT);
        func_decl delta = z3::function("delta", SORT, SORT, SORT);
        
#if STATE == EQSTATE     
        s1.execute_recursive(Modified_Functionality(ctx,
                                                    rho,
                                                    delta,
                                                    network.a1,
                                                    network.n1.abstract_nodes,
                                                    eqstate));
        
#elif STATE == WOEQSTATE
         s1.execute_recursive(Modified_Functionality(ctx,
                                                    rho,
                                                    delta,
                                                    network.a1,
                                                    network.n1.abstract_nodes));
         
#endif         
         
        s1.accept_automata(rho,network.a1);

        end = clock();
        elapsed_ms = double(end - begin) / (CLOCKS_PER_SEC/1000);
        perfCounters.push_back(make_tuple(k, "query constr", elapsed_ms));

        cout << "solving" << endl;
        begin = clock();
        Z3_model m = s1.solve_z3();
        end = clock();
        elapsed_ms = double(end - begin) / (CLOCKS_PER_SEC/1000);
        perfCounters.push_back(make_tuple(k, "z3 solve", elapsed_ms));

        // if (k == 2)
        // {
        //     s1.print_query();
        // }

        if(m)
        {
            model m1(ctx, m);
            // cout << "\n\nModel\n" << m1;
            cout << "Model found" << endl;
            for( int index = 0; index < k; index++)
            {
                int int_to, int_from;
                Z3_get_numeral_int(ctx, m1.eval(s1.n[index], true), &int_to);
                Z3_get_numeral_int(ctx, m1.eval(s1.n1[index], true), &int_from);
                ret.push_back(std::make_tuple(int_to, int_from));
            }

            break;
        }
    }

    return ret;
}

//     s1.define_prev_model(prev_model);
model_t CachingSolver::cached_solve(int pcid, model_t prev_model)
{
    model_t ret = model_t();
    clock_t begin, end;
    double elapsed_ms;
    network.set_pc(pcid);
    int k = prev_model.size();

    context ctx;
    Solver s1(ctx, network.n1, k);

    begin = clock();

    s1.define_k_rules();
    s1.define_prev_model(prev_model);

#if TOPO == MACROTOPO
    s1.delta_satisfies_topology();
#elif TOPO == UFTOPO
    func_decl topology = z3::function("topology", SORT, SORT, ctx.bool_sort());
    s1.delta_satisfies_topology_uf(topology);
#endif        
        
#if STATE == EQSTATE     
    map<int,int> mapping; 
    mapping[0] = 0; 
    mapping[1] = 1; 
    
    for( int i = 0; i<= network.n1.abstract_nodes.size(); i++)
    {  
           mapping[i] = i; 
    }
     
    func_decl eqstate = z3::function("eqstate", SORT, SORT);
    s1.define_eqstate(eqstate,mapping);
#endif
    
    s1.delta_satisfies_non_mutable();
    s1.delta_satisfies_not_egress();
    s1.delta_satisfies_not_existing();

    func_decl cycle = z3::function("cycle", SORT, SORT, SORT);
    s1.execute_recursive(Cyclicity(ctx, cycle));

    func_decl dest = z3::function("dest", SORT, SORT, SORT);
    s1.execute_recursive(Compute_Dest(ctx, dest, network.n1));

    func_decl rho = z3::function("rho", SORT, SORT, SORT);
    func_decl delta = z3::function("delta", SORT, SORT, SORT);
    
#if STATE == EQSTATE     
    s1.execute_recursive(Modified_Functionality(ctx,
                                                rho,
                                                delta,
                                                network.a1,
                                                network.n1.abstract_nodes,
                                                eqstate));
    
#elif STATE == WOEQSTATE
     s1.execute_recursive(Modified_Functionality(ctx,
                                                rho,
                                                delta,
                                                network.a1,
                                                network.n1.abstract_nodes));
     
#endif         
     
    s1.accept_automata(rho,network.a1);
        

    end = clock();
    elapsed_ms = double(end - begin) / (CLOCKS_PER_SEC/1000);
    perfCounters.push_back(make_tuple(k, "check query constr", elapsed_ms));

    cout << "checking" << endl;
    begin = clock();
    Z3_model m = s1.solve_z3();
    end = clock();
    elapsed_ms = double(end - begin) / (CLOCKS_PER_SEC/1000);
    perfCounters.push_back(make_tuple(k, "check z3", elapsed_ms));

    if(m)
    {
        model m1(ctx, m);
        cout << "Check SAT" << endl;
        for( int index = 0; index < k; index++)
        {
            int int_to, int_from;
            Z3_get_numeral_int(ctx, m1.eval(s1.n[index], true), &int_to);
            Z3_get_numeral_int(ctx, m1.eval(s1.n1[index], true), &int_from);
            ret.push_back(std::make_tuple(int_to, int_from));
        }
    }
    else
    {
        cout << "Check UNSAT" << endl;

    }

    return ret;
}

py::list CachingSolver::solve()
{
    py::list ret;
    SIZE = ceil((float)log2(network.n1.abstract_nodes.size()))+2;
    cout << "\nSIZE = " << SIZE << "\n";
    clock_t begin, end;
    double elapsed_ms;

    int solves = 0;
    int cache_hits = 0;
    int cache_misses = 0;

    for (auto pcid : network.pcids)
    {
        model_t result = model_t();

        // iterate backwards
        //for (auto model : cache)
        for (int i = cache.size(); i > 0; i--)
        {
            model_t model = cache[i-1];
            result = cached_solve(pcid, model);
            if (result.empty())
            {
                cache_misses++;
            }
            else
            {
                cache_hits++;
                break;
            }
        }

        if (result.empty())
        {
            solves++;
            result = iterative_solve(pcid);

            if (!result.empty())
            {
                cache.push_back(result);
            }
        }

        if (result.empty())
        {
            cout << "No model found" << endl;
        }
        else
        {
            for (auto tup : result)
            {

                ret.append(py::make_tuple(pcid,
                                          std::get<0>(tup),
                                          std::get<1>(tup)));
            }
        }
    }

    perfCounters.push_back(make_tuple(0, "cache_hits", cache_hits));
    perfCounters.push_back(make_tuple(0, "cache_misses", cache_misses));
    perfCounters.push_back(make_tuple(0, "solves", solves));
    perfCounters.push_back(make_tuple(0, "total_classes", network.pcids.size()));

    cout << "--------------------------------" << endl;
    cout << "   Total: " << network.pcids.size() << endl;
    cout << "   Solves: " << solves << endl;
    cout << "   Cache Hits: " << cache_hits << endl;
    cout << "   Cache Misses: " << cache_misses << endl;
    cout << "--------------------------------" << endl;
    return ret;
}

BOOST_PYTHON_MODULE(cppsolver)
{
    py::class_<AbstractNetwork>("AbstractNetwork",
                                py::init<py::list,
                                py::list,
                                py::list,
                                py::list,
                                py::list,
                                py::list,
                                py::list,
                                py::list,
                                py::list,
                                py::list,
                                py::list,
                                int,
                                int,
                                int>());

    // py::class_<DefaultSolver>("DefaultSolver",
    //                       py::init<AbstractNetwork>())
    // .def("solve", &DefaultSolver::solve)
    // .def("get_perf_counters", &DefaultSolver::get_perf_counters);


    py::class_<CachingSolver>("CachingSolver",
                          py::init<AbstractNetwork>())
    .def("solve", &CachingSolver::solve)
    .def("get_perf_counters", &CachingSolver::get_perf_counters);

    // py::class_<MultiThreadedCachingSolver>("MultiThreadedCachingSolver",
    //                       py::init<AbstractNetwork>())
    // .def("solve", &MultiThreadedCachingSolver::solve)
    // .def("get_perf_counters", &MultiThreadedCachingSolver::get_perf_counters);

}
