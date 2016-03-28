/*
 * utils.h
 *
 *  Created on: Jan 22, 2016
 *      Author: me
 */

#ifndef SOLVER_UTILS_H_
#define SOLVER_UTILS_H_

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


using namespace std;



template<typename T1, typename T2>
std::ostream &operator<<(std::ostream &stream, const std::map<T1, T2>& map)
{
  for (typename std::map<T1, T2>::const_iterator it = map.begin();
       it != map.end();
       ++it)
    {
      stream << (*it).first << " --> " << (*it).second << std::endl;
    }
  return stream;
}

template<typename T>
std::ostream &operator<<(std::ostream &stream, const std::vector<T> & v)
{
	stream<<"["	;
  for (typename std::vector<T> ::const_iterator it = v.begin();
       it != v.end();
       ++it)
    {
      stream << (*it)<<" \n ";
    }
    stream<<"] size:"<<v.size();
  return stream;
}

template<typename T>
std::ostream &operator<<(std::ostream &stream, const std::set<T> & v)
{
	stream<<"["	;
  for (typename std::set<T> ::const_iterator it = v.begin();
       it != v.end();
       ++it)
    {
      stream << (*it)<<" \n ";
    }
    stream<<"] size:"<<v.size();
  return stream;
}



template<typename T1,typename T2>
std::ostream &operator<<(std::ostream &stream, const std::pair<T1,T2> & p)
{
	stream<<"("<<p.first<<","<<p.second<<")";
  return stream;
}

template<typename T1,typename T2>
std::ostream &operator<<(std::ostream &stream, const std::tuple<T1,T2> & p)
{
	stream<<"("<<get<0>(p)<<","<<get<1>(p)<<")";
  return stream;
}

template<typename T1,typename T2, typename T3>
std::ostream &operator<<(std::ostream &stream, const std::tuple<T1,T2,T3> & p)
{
	stream<<"("<<get<0>(p)<<","<<get<1>(p)<<","<<get<2>(p)<<")";
  return stream;
}






#endif /* SOLVER_UTILS_H_ */
