#include <map>
#include <unordered_map>
#include <set>
#include <unordered_set>
#include <tuple>
#include <vector>
#include <queue>
#include <utility>
#include <algorithm>
#include <functional>

#include <ctime>
#include <iostream>
#include <fstream>
#include <sstream>
#include <string>
#include <cstring>
#include <stdlib.h>
#include <limits.h>
#include  "z3++.h"

using namespace z3;
using namespace std;


#define QUOTE(S) #S
#define MAX_PREFIX 255


//TF fields///---------------------------------------------------------------------------------------------------

class fields
{  public :
	int vlan;      //exact /  * = -1
    string ip_src; //range
    string ip_dst; //range
    int ip_proto;  //exact /  * = -1
    int tcp_src;   //exact /  * = -1
    int tcp_dst;   //exact /  * = -1
    int tcp_ctrl;  //exact /  * = -1

  string print()
    {
     stringstream ss;
      ss<<"vlan = "       <<vlan
       	<<"\t ip_src = "  <<ip_src
    	<<"\t ip_dst = "  <<ip_dst
    	<<"\t ip_proto = "<<ip_proto
    	<<"\t tcp_src = " <<tcp_src
    	<<"\t tcp_dst = " <<tcp_dst
    	<<"\t tcp_ctrl = "<<tcp_ctrl;
      return ss.str();
    }

    fields& operator= (const fields & fld)

    { vlan     = fld.vlan;
      ip_src   = fld.ip_src;
      ip_dst   = fld.ip_dst;
      ip_proto = fld.ip_proto;
      tcp_src  = fld.tcp_src;
      tcp_dst  = fld.tcp_dst;
      tcp_ctrl = fld.tcp_ctrl;
      return *this;
    }

    bool operator==(const fields &other) const
        {

    	return ( vlan == other.vlan
    	     &&  ! ip_src.compare(other.ip_src)
    	     &&  ! ip_dst.compare(other.ip_dst)
             &&  ip_proto == other.ip_proto
             &&  tcp_ctrl == other.tcp_ctrl
             &&  tcp_src == other.tcp_src
             &&  tcp_dst == other.tcp_dst
    	  	);
        }

   /*bool operator<(const fields &other) const
    {
    		 if (vlan < other.vlan) return true;
    	else if (vlan > other.vlan) return false ;
    	else if (ip_src.compare(other.ip_src) < 0  ) return true ;
    	else if (ip_src.compare(other.ip_src) > 0  ) return false ;
    	else if (ip_dst.compare(other.ip_dst) < 0  ) return true ;
    	else if (ip_dst.compare(other.ip_dst) > 0  ) return false ;
    	else if (ip_proto < other.ip_proto) return true;
    	else if (ip_proto > other.ip_proto) return false ;
    	else if (tcp_src < other.tcp_src) return true;
    	else if (tcp_src > other.tcp_src) return false ;
    	else if (tcp_dst < other.tcp_dst) return true;
    	else if (tcp_dst > other.tcp_dst) return false ;
    	else if (tcp_ctrl < other.tcp_ctrl) return true;
    	else if (tcp_ctrl > other.tcp_ctrl) return false ;
    	else return false;
    }*/

//and of fields--------------------------------------------------------

    int exact_and(int i, int j) throw( bool)
    {
    	if( i != j && i>=0 && j>=0 ) throw false;
    	else return max(i,j);
     }

    string range_and(string s1,string s2 ) throw (bool)
    {
    	stringstream s3;

    	if(s1.length() != s2.length())
    		throw false;

    	for(unsigned i = 0 ; i< s1.length() ; i ++ )
    	{
    		if( (s1[i] == '1' && s2[i]== '0') ||  (s1[i] == '0' && s2[i]== '1')  )
    			throw false;

    		s3<<min(s1[i],s2[i]);
    	}

    	return s3.str();
    }

    friend fields fields_and(fields, fields) throw (bool) ;
    //friend because, I want to write filed_and(f1,f2) instead of f1.field_and(f2)
};

namespace std {
    template <>
        class hash<fields>{
        public :
        size_t operator()(const fields &x ) const
        {
            return ( std::hash<int>()(x.vlan)
            	   ^ std::hash<int>()(x.ip_proto)
            	   ^ std::hash<int>()(x.tcp_src)
            	   ^ std::hash<int>()(x.tcp_dst)
            	   ^ std::hash<int>()(x.tcp_ctrl)
            	   ^ std::hash<string>()(x.ip_src)
            	   ^ std::hash<string>()(x.ip_dst)
            	   );
        }
    };
}

fields fields_and(fields f1, fields f2) throw (bool)
{
	fields f3 ;

	f3.vlan     = f1.exact_and(f1.vlan    , f2.vlan    );
	f3.ip_src   = f1.range_and(f1.ip_src  , f2.ip_src  );
	f3.ip_dst   = f1.range_and(f1.ip_dst  , f2.ip_dst  );
	f3.ip_proto = f1.exact_and(f1.ip_proto, f2.ip_proto);
	f3.tcp_src  = f1.exact_and(f1.tcp_src , f2.tcp_src );
	f3.tcp_dst  = f1.exact_and(f1.tcp_dst , f2.tcp_dst );
	f3.tcp_ctrl = f1.exact_and(f1.tcp_ctrl, f2.tcp_ctrl);

    return f3;
}


//Parse TF files//----------------------------------------------------------------------------------------------

class dep_rule
{public :
	  int rule;
	  fields match;
	  int nports;
	  vector<int> ports;
	  string print()
	  {
		  std::stringstream ss;
          ss << " rule = " << rule <<" match = "<<match.print()<<" nport="<<nports<<" ports = ";
          for(size_t i = 0; i < ports.size(); ++i)
               ss <<" " << ports[i];
          return ss.str();
	  }
};

class rule_match  //make it set
{  public :

	fields match;
	string mask, rewrite ;
	vector<int> out ;
	vector<dep_rule> deps;
	string print()
	{
		std::stringstream ss;
	   	ss << "match = " << match.print() <<" mask = "<<mask<<" rewrite= "<<rewrite;
	   	ss<<" out = ";
	   	for(size_t i = 0; i < out.size(); ++i)
	   	ss<<" "<<out[i];
		ss<<" dependencies = " ;
		for(size_t i = 0; i < deps.size(); ++i)
			ss<<" "<<deps[i].print();
		return ss.str();
	}
};

class rules
{ public :
	std::multimap <int,rule_match> rule;
	std::set<int> nodes;
    string print()
    {
    	std::stringstream ss;

    	for ( auto it = rule.begin(); it != rule.end(); ++it )
    	    ss <<"\nin = "<< it->first << " " << it->second.print();
    	return ss.str();
    }

};

int bitstring_to_int(string bitString,int sLength)
{
   int tempInt;
   int num=0;
   for(int i=0; i<sLength; i++)
   {
	  if(bitString[i] == 'x') cout<<"error\n";

       tempInt=bitString[i]-'0';
       num |= (1 << (sLength-1-i)) * tempInt;
   }
   	return num;
}

fields match_to_field(string match)
{
	fields ret ;
	ret.vlan     = (match.compare(0  ,16,"xxxxxxxxxxxxxxxx") == 0) ?  -1 : bitstring_to_int(match.substr(0 ,16),16);
	ret.ip_src   =  match.substr (16 ,32);
	ret.ip_dst   =  match.substr (48 ,32);
	ret.ip_proto = (match.compare(80 ,8 ,"xxxxxxxx")         == 0) ?  -1 : bitstring_to_int(match.substr(80,  8), 8);
	ret.tcp_src  = (match.compare(88 ,16,"xxxxxxxxxxxxxxxx") == 0) ?  -1 : bitstring_to_int(match.substr(88, 16),16);
	ret.tcp_dst  = (match.compare(104,16,"xxxxxxxxxxxxxxxx") == 0) ?  -1 : bitstring_to_int(match.substr(104,16),16);
	ret.tcp_ctrl = (match.compare(120,8 ,"xxxxxxxx")         == 0) ?  -1 : bitstring_to_int(match.substr(120, 8), 8);

	return ret;
//x - times 8
//format["vlan_pos"] = 0      format["vlan_len"] = 2
//format["ip_src_pos"] = 2    format["ip_src_len"] = 4
//format["ip_dst_pos"] = 6    format["ip_dst_len"] = 4
//format["ip_proto_pos"] = 10 format["ip_proto_len"] = 1
//format["tcp_src_pos"] = 11  format["tcp_src_len"] = 2
//format["tcp_dst_pos"] = 13  format["tcp_dst_len"] = 2
//format["tcp_ctrl_pos"] = 15 format["tcp_ctrl_len"] = 1
//format["length"] = 16

}

vector<int> string_to_array(string str)
{
	vector<int> nodes;
		string token;
  try{


	if ( str[0] == '[' )
	{ str = str.substr (1, str.size() -2);
	}

	stringstream formula(str) ;

	while (getline(formula, token, ','))
	{
	  	nodes.push_back(atoi(token.c_str())); //stoi
	}


  }
  catch(std::exception &ex)
  {cout<<"exception found";}
  return nodes;
}

vector<dep_rule> read_deps (string s)
{
  char *save;
  vector<dep_rule> res ;
  char *depstr;
  for ( depstr = strtok_r ((char *)s.c_str(), "#", &save);
		  depstr;
		  depstr = strtok_r (NULL, "#", &save))
  {
    char *save2;
    vector<int> ports;
    dep_rule tmp;

    tmp.rule = atoi (strtok_r (depstr, ";", &save2)) + 1;
    tmp.match = match_to_field( strtok_r (NULL, ";", &save2)) ; //new added
    tmp.ports = string_to_array(strtok_r (NULL, ";", &save2));
    tmp.nports = tmp.ports.size();

    res.push_back(tmp);
  }
  return res;
}

rules parse_tf (string name)
{

  FILE *in = fopen(name.c_str(), "r");
  char *line = NULL;
  int len;
  size_t n;

  rules table;

  if (!in || (len = getline (&line, &n, in)) == -1)
    { cout<<"cannot open file";
      exit(0);
    }

  char prefix[MAX_PREFIX + 1];
  int tflen;
  int res;
  res= sscanf (line, "%d$%" QUOTE (MAX_PREFIX) "[^$]$", &tflen, prefix);
  if (res < 1)
	  { printf("Can't read len from first line \"%s\".", line);
	    exit(0);
	  }

  getline (&line, &n, in); /* Skip next line */
  while ((len = getline (&line, &n, in)) != -1)
  {
    char *save;
    string type,affected;
    vector<int> in;

    rule_match r;

    type = strtok_r(line, "$", &save);
    in = string_to_array(strtok_r (NULL, "$", &save));

    r.match = match_to_field( strtok_r (NULL, "$", &save)) ;
    r.mask = strtok_r (NULL, "$", &save);
    r.rewrite = strtok_r (NULL, "$", &save);
    /*inv_match =*/ strtok_r (NULL, "$", &save);
    /*inv_rewrite =*/ strtok_r (NULL, "$", &save);
    r.out = string_to_array(strtok_r (NULL, "$", &save));
    affected = strtok_r (NULL, "$", &save);
    /*influence = */strtok_r (NULL, "$", &save);
    /*
    file = strtok_r (NULL, "$", &save);
    lines = strtok_r (NULL, "$", &save);
    id = strtok_r (NULL, "$", &save);
    if (!id) { id = file; file = lines = NULL; }

    if (file) {
      r->file = xstrdup (file);
      lines[strlen (lines) - 1] = 0;
      r->lines = xstrdup (lines);
    }

    if (strcmp (type, "link"))
    {
      r->match = array_from_str (match);
      if (!strcmp (type, "rw"))
      {
        r->mask = array_from_str (mask);
        r->rewrite = array_from_str (rewrite);
      }
    }
*/
    r.deps = read_deps(affected);

    for(unsigned int i = 0; i<in.size();i++ )
    {
    	table.rule.insert({in[i], r});
    	table.nodes.insert(in[i]);
    }
  }
  fclose (in);
  return table;
}


//my representation//---------------------------------------------------------------------------------------------

class packet
{
public :
  fields pos;
  unordered_set<fields> neg;
  //using my custom hash function... for fields because of unordered... set would require to define < for fields

  bool operator==(const packet &other) const
         {
                if( pos == other.pos)
                {
                	if(neg.size() == other.neg.size() )
                	{
                        for( auto it1 = neg.begin() ; it1 != neg.end() ; ++it1  )
                		{
                			if(	other.neg.find(*it1) == other.neg.end()) //*it1 not found in other.neg
                               return false;
                		}
                       return true ;

                	}
                	else return false;

                }
                else return false;

         }


  string print()
  { std::stringstream ss;
	ss<<"pos = "<< pos.print() <<" neg = ";
	for(auto it = neg.begin(); it != neg.end() ; ++it)
		{ fields fld = *it;
		ss<<" /= " << fld.print();
		}
	return ss.str();
  }
};

namespace std {
    template <>
        class hash<packet>{
        public :
        size_t operator()(const packet &x ) const
        {
        	std::size_t hval = 	std::hash<fields>()(x.pos);

        	for(auto it = x.neg.begin(); it!= x.neg.end() ; ++it )
        	{
        		hval ^= std::hash<fields>()(*it);
        	}

            return hval;
        }
    };
}


class loc_packet
{
public:
	int node ;
	packet pk;

	loc_packet(){}
	loc_packet(int n, packet p)
	{ node = n;
	  pk = p ;
	}
	string print()
	{
		std::stringstream ss;
		ss<<"out = "<< node <<" "<< pk.print();
		return ss.str();
	}

};

class rules_compact //TODO: ordering by number of negetive rules
{
 public :
	unordered_multimap<int, loc_packet> rule;  //TODO :  hence changed to  multi map
	set<int> nodes;

	string print()
	{
		stringstream ss;
		for ( auto it = rule.begin(); it != rule.end(); ++it )
		    ss <<"\nin = "<< it->first << " " << it->second.print();
		 return ss.str();
	}
};


rules_compact compact_rules(rules table)
{

	rules_compact table_c;

	table_c.nodes = table.nodes;


	for ( auto it = table.rule.begin(); it != table.rule.end(); ++it )
	{	//  it->first   it->second ;

		unordered_set<fields> s_fld;

		for( auto it1 = (it->second.deps).begin(); it1 != (it->second.deps).end() ; ++it1 )
		{
			s_fld.insert(it1->match);
		}


	   	for( auto it2 =  it->second.out.begin() ; it2!=  it->second.out.end(); ++it2)
	   	{
	   		loc_packet lpk;

	   		lpk.pk.pos = (it->second).match ;
	   		lpk.pk.neg = s_fld;
	   		lpk.node = *it2;

	   		table_c.rule.insert({it->first,lpk});
	   	}

	}

	return table_c;
}

packet packet_and( packet p1 , packet p2 )
{
	packet p3;

	p3.pos = fields_and( p1.pos,p2.pos);
	p3.neg   = unordered_set<fields> (p1.neg);
	p3.neg.insert(p2.neg.begin(),p2.neg.end() );

    return p3;
}

void no_neg( fields pos, unordered_set<fields> neg) throw (bool)
{
	int count = 0 , total = 0;

	for( auto it = neg.begin(); it!= neg.end() ; ++it )
	{
		++total ;

		try{
			fields_and( pos, *it ) ;
		   }
		catch ( bool val)
		{ ++count; }

	}

	if(count != total ) //sone neg got satistied
		 throw false ;  // stop

}



//display function//-----------------------------------------------------------------------------------------

typedef set<pair<int,int>> dot_graph;

void write_to_Dot(dot_graph edges, string file, string type)
{ //  style=solid dashed dotted bold invis

    stringstream ss;

    ss<<file<<".dot";
	ofstream out(ss.str());

	out<<"strict digraph network {\n";

	ss<<"ratio = compress ; \n";
	ss<<"rotate=90 ; \n";
	for( auto it = edges.begin(); it!= edges.end(); ++it)
		  out<< it->first << " -> "<< it->second <<" [style=solid] ;\n" ;
     out<<"}";
     out.close();

     ss.str("");
     ss<<"circo -T"<<type<<" "<<file<<".dot -o "<<file<<"."<<type;

     system(ss.str().c_str());

}

void write_to_Dot(dot_graph edges, string file, string type, dot_graph all )
{


     write_to_Dot(edges,file, type);


	 stringstream ss;

	 ss<<"diff_"<<file<<".dot";
	 ofstream out(ss.str());
	 out<<"strict digraph network {\n";
	 ss<<"ratio = compress ; \n";
	 ss<<"rotate=90 ; \n";
	 for( auto it = edges.begin(); it!= edges.end(); ++it)
		 out<< it->first << " -> "<< it->second <<" [style=solid] ;\n" ;

	 for( auto it = all.begin(); it!= all.end(); ++it)
	 { 	if( edges.find(*it) == edges.end() ) //does not belongs to edges...
			out<< it->first << " -> "<< it->second <<" [style=dotted] ;\n" ;
	 }

	 out<<"}";
	 out.close();

	 ss.str("");
	 ss<<"circo -T"<<type<<" "<<"diff_"<<file<<".dot -o "<<"diff_"<<file<<"."<<type;

	 system(ss.str().c_str());

  }

dot_graph table_compact_to_dot( rules_compact table_c)
{
	dot_graph edges;

	for ( auto it = table_c.rule.begin(); it != table_c.rule.end(); ++it )
			 edges.insert(make_pair(it->first,   it->second.node )) ;

    return edges;

}



//reachability on my representation to symbolic reachability//------------------------------------------------

namespace std {
template <>
        class hash < std::pair< int,int> >{
        public :
        size_t operator()(const pair< int, int> &x ) const
        {
        	size_t h =   std::hash<int>()(x.first) ^ std::hash<int>()(x.second);
            return  h ;
        }
    };
}

class symbolic_rules
{
public :
	map < pair<int,int> , int > rules ;
	unsigned no_nodes;
	unsigned no_packet ;
	map< pair<int,int>, int > final;

	vector<pair<int,int>> edges;
	vector<int> terminal;
	unsigned K;

	unsigned to;
	unsigned from;
	unsigned source;
	unsigned pac;

};

void write_to_Dot(	symbolic_rules  rules, string file, string type )
{

	 stringstream ss;

	ss<<file<<".dot";
	ofstream out(ss.str());

	out<<"digraph network {\n";


	ss<<"ratio = compress ; \n";
	ss<<"rotate=90 ; \n";

	for( auto it = rules.rules.begin(); it!= rules.rules.end(); ++it)
		  out<< it->first.first << " -> "<< it->first.second <<" [label="<<it->second<<"] ;\n" ;

	out<<"}";
	 out.close();

	 ss.str("");
	 ss<<"circo -T"<<type<<" "<<file<<".dot -o "<<file<<"."<<type;

	 system(ss.str().c_str());

}


typedef unordered_multimap<packet,vector<int> > EqClass ;

EqClass reachability ( loc_packet pk ,  rules_compact table_c)
{

	/*Data Structure
	 * reach   : temporary workspace to compute reachability
	 * classes : final set of classes
	 * edges   : optional for dot display
	 */

	queue < pair<loc_packet, vector<int> > >  reach ; //vector to reconstruct the visited path for symbolic computation

    unordered_multimap<packet,vector<int> > classes; // hash defined on packets///

    dot_graph edges ;


    //------------------------------------------------------------------------------

	reach.push( make_pair(pk,vector<int>()) );


	while(!reach.empty())
	{

		pair<loc_packet, vector<int> > tmp = reach.front();
		reach.pop();


		loc_packet currLocPk  = tmp.first ;  //currlocpk.node,  currlocpk.pk
		vector<int> vi = tmp.second ; //visited


		vector<int> visited = vi;
		visited.push_back(currLocPk.node); // all visited nodes till this node...


	    if( table_c.rule.count(currLocPk.node) == 0 ) //  pendent vertex,  equal range size is zero of node
	    {
	    	//for extra added.... for duplicate removal
	    	bool flagc = false;
	    	for(auto iter = classes.find(currLocPk.pk); iter!= classes.end() ; ++iter )
	    	{
	    		if( iter->second ==  visited )
	    			 flagc = true ;
	    	}

	    	if(flagc == false)
	    		classes.insert({currLocPk.pk, visited});

	    }

	    else //current node has some rules
	    {

	    	bool flag = false ; //any rule matched?


	    	auto range = table_c.rule.equal_range(currLocPk.node);
			for(auto it = range.first; it != range.second; ++it )
			{// it->first = currLocPk.node    it->second = (locpk) packet rule and next hop

			  loc_packet branch = 	it->second ;
			  // branch.node next hop
			  // branch.pk edge packet label

			  if( std::find(visited.begin(), visited.end(), branch.node) != visited.end() )
			  {  //if found then skip,  !=end => found, == end =>not found
				  continue; //found //redundant
			  }

			  else
			  {
				  packet p1;


					  try{ // have only one output node, changed in rule_comapct

						  p1 = packet_and (branch.pk, currLocPk.pk);  // if( currlockpk.pk.pos does not matches with all branch.pk.neg )

						  no_neg(currLocPk.pk.pos, branch.pk.neg); //no negetives matches matches...

						}
					  catch(bool bVal) {continue;}  //skip this rule to next rule


				    reach.push( make_pair( loc_packet( branch.node, p1), visited ) ) ;
					flag = true; //atleast one rule matched...

					edges.insert(make_pair(currLocPk.node,branch.node )) ;

			  }

			}//foreach rule

			if(flag == false) // no rule matched...
				{ // final.push_back(currLocPk);

				    // extra added for duplicate removal
					bool flagc = false;
				 	for(auto iter = classes.find(currLocPk.pk); iter!= classes.end() ; ++iter )
				    	{
				    		if( iter->second ==  visited )
				    			 flagc = true ;
				    	}

				    	if(flagc == false)
				    		classes.insert({currLocPk.pk, visited});

				}

	    }//equal range = no of rules,  size not zero

	} //while

//-------------------------------------------------------------------


	//display-------
    write_to_Dot(edges,"a", "svg", table_compact_to_dot(table_c));//,pk.node);


    return classes;

}

//--------------------------------------------------------------------------------------------------------------


template<typename T>
bool findVec(vector<T> data , T ele)
{
    for(int i = 0 ; i< data.size(); i++)
    	if( data[i] == ele)
    		return true; //found

    return false; //not-found
}



symbolic_rules  generate_symbolic_graph( EqClass classes, unsigned source, unsigned from, unsigned to , vector<int> through)
{

    int counter = 0 ;
    int counter_node = 0  ;
    int countpk;

    unsigned pac;

    symbolic_rules symbolic_graph;


    unordered_map<packet,int> pktoInt; //retreive edge lables form symbolic numbers
    unordered_map<int,int> nodetoInt;  //original -> symbolic


    map<pair<int,int>, vector<int>> sorted_edges;//for svg file


    auto it = classes.begin() ;
    auto it2 = classes.begin() ;//just to get the type;


	for ( ;  it != classes.end();  it = it2) //iterate over all classes
	   {
		   packet theKey = it->first; //key = packet


		   auto range = classes.equal_range(theKey);
		   for( it2 = range.first; it2 != range.second; ++it2 )  //for a class, iterate over all visited set
		   {  //it2->second;  //first = key, second =range =set<int> ;

			   vector<int> path = it2->second ;


			   //pruning only with to and from...
//			   if( ! (std::find(path.begin(), path.end(), from)!=path.end() || std::find(path.begin(), path.end(), to)!=path.end() ))
//				   continue;

			   //pruning the graph, only keeping the paths which has all ele of through
			   bool match = false;
			   for(unsigned index = 0 ;index<through.size(); index++)
				   if(  (std::find(path.begin(), path.end(), through[index])!=path.end() ) )  match = true;
			   if(match == false)
				   continue;


			   //get key for packet
			   if(pktoInt.find(theKey) == pktoInt.end()) //not found
			   {    counter++; //counter starts form 1
			        pktoInt.insert({theKey,counter});
			   	    countpk = counter;
			   }
			   else
			   {
				   countpk = pktoInt[theKey];
			   }


			   // to make nodes numbered 1,2..... get node keys
			   for(unsigned i = 0 ; i< path.size() ; i++ )
			   {
				   auto it = nodetoInt.find(path[i]);
				   if(it == nodetoInt.end()) // not found
				   {//add to dictionary
					   counter_node++ ; //starts form 1
					   nodetoInt.insert({ path[i] ,  counter_node }); //org -> symbolic
				   }

			   }


               if(! findVec(symbolic_graph.terminal, nodetoInt[path[path.size()-1]] )) //not found
            	   symbolic_graph.terminal.push_back(nodetoInt[path[path.size()-1]]);


			   for(unsigned itk = 0 ; itk < path.size() -1 ; ++itk)
			   {
				   int n, n1 ;
				   n  = nodetoInt[path[itk]] ;
				   n1 = nodetoInt[path[itk+1]];


				   symbolic_graph.final.insert({ make_pair( n , countpk ) , nodetoInt[path[path.size() -1 ]]  });

			       if( ! findVec( symbolic_graph.edges , make_pair(n, n1) ) )
			    	   symbolic_graph.edges.push_back(make_pair(n, n1));


			       symbolic_graph.rules.insert({ make_pair( n , countpk) , n1 }) ;  //visited[i] count visited[i+1]

			       sorted_edges [make_pair( n , n1 )].push_back(countpk); 			//for svg file

			   }


			   //TODO: it just selects one of the paackets
			   if(path[0] == source && path[path.size() -1 ] == from )
            	   pac = countpk ;


		   }
	   }


      symbolic_graph.no_nodes  =  counter_node;
      symbolic_graph.no_packet =  counter ;

      symbolic_graph.to = nodetoInt[to];
      symbolic_graph.source = nodetoInt[source];
      symbolic_graph.pac = pac;



      ofstream s1;
      s1.open("map.txt");
      for(auto it = pktoInt.begin() ; it!= pktoInt.end() ; ++it )
      {  packet pk = it->first ;
    	  s1<<pk.print()<<"  ->>>  " <<it->second<<"\n";
      }
      s1<<"\n\n\n\n\n\n\n";
      for(auto it = nodetoInt.begin() ; it!= nodetoInt.end() ; ++it )
          	  s1<<it->first<<"  ->>>  " <<it->second<<"\n";
       s1.close();


		stringstream ss;
		ss<<"symbolic.dot";
		ofstream out(ss.str());
		out<<"digraph network {\n";
		ss<<"ratio = compress ; \n";
		ss<<"rotate=90 ; \n";
		for(auto it= sorted_edges.begin(); it!= sorted_edges.end(); it++)
		{	out<< it->first.first << " -> "<< it->first.second <<" [label=\"";
			 for(unsigned i =0; i< it->second.size(); ++i)
			 { out<<it->second[i]<<","; }
  			 out<<"\"] ;\n";
		}
	  out<<"}";
	  out.close();
	  ss.str("");
	  ss<<"circo -Tsvg symbolic.dot -o symbolic.svg";
	  system(ss.str().c_str());



 return symbolic_graph;

 }



// auxilary macros used in smt
expr  topo_expr (expr  p1, expr  p2, vector<pair<int,int>> points)
{

	context & c = p1.ctx();

	expr ret = c.bool_val(false);

	for (int i =0 ; i< points.size() ; ++i )
	{
		ret = ret || ( ( p1 ==  c.int_val(points[i].first) && ( p2 == c.int_val( points[i].second) ) ) ) ;
	}

return ret ;
}

expr  terminal_expr (expr  p1, vector<int> terminal)
{

	context & c = p1.ctx();

	expr ret = c.bool_val(false);

	for (int i =0 ; i< terminal.size() ; ++i )
	{
		ret = ret ||  ( p1 ==  c.int_val(terminal[i]) )   ;
	}

return ret ;
}

expr  rule_expr (expr  n, expr r, 	map < pair<int,int> , int > rules )
{

	context & c = n.ctx();

	expr ret = c.bool_val(false);

	for (auto it = rules.begin(); it != rules.end(); ++it)
	{
		ret = ret || ( ( n ==  c.int_val(it->first.first) ) && ( r == c.int_val( it->first.first ) ) ) ;
	}

return ret ;
}



void check_sat(expr ex)
{
	    context & c = ex.ctx();
    	ofstream myfile;
		myfile.open ("formula.txt");
		myfile << "formula\n";
		myfile << ex <<"\n\n\n\n\n\n";
		myfile.close();

		cout<<"solver started";

		  params p(c);
		  solver s(c);
		  p.set("macro-finder", true);
		  s.set(p);
		 s.add(ex);

		if( s.check() == sat )
		{
			cout<<"\nsat\n";
			ofstream myfile1;
			myfile1.open ("sat.txt");
			myfile1 << "formula\n";

			model m = s.get_model();
			myfile1 << m << "\n";

			myfile1.close();

		}

		else
			cout<<"\nunsat\n";


}



void naive(symbolic_rules table)
{

	context c;

	unsigned no_packets = table.no_packet;
	unsigned no_nodes   = table.no_nodes;

	z3::sort I   = c.int_sort();
	z3::sort B   = c.bool_sort() ;
	func_decl R     = c.function("R"    , I, I, I ); // R : n p -> n1
	func_decl f1    = c.function("f1"   , I, I, I ); // f: In , P -> Out
	func_decl guess = c.function("guess", I, I, I ); // f: In , P -> Out

	expr initial_graph  = c.bool_val(true);
	expr size_constrain = c.bool_val(true);
	expr constrain      = c.bool_val(true);


	const unsigned K = table.K;
	expr_vector n(c);
	expr_vector p(c);
	expr_vector n1(c);


	//when to is not terminal...
	table.terminal.push_back(table.to);


	//compute R
	for( auto it = table.rules.begin(); it!= table.rules.end(); ++it ) // rules I P -> I
	{
		initial_graph =  initial_graph
				     &&  R   ( c.int_val(it->first.first) , c.int_val(it->first.second) ) == c.int_val(it->second) ;

	}



// compute guessed table and f1 of the guessed part...
	for (unsigned i = 0; i < K; i++)
	{
		stringstream ns,ps,n1s;
		ns << "n_" << i;
		ps << "p_" << i;
		n1s<< "n1_" << i ;

		expr x = c.int_const(ns.str().c_str());
		n.push_back(x);
		size_constrain = size_constrain && 0 < x && x <= no_nodes ;

		expr y = c.int_const(ps.str().c_str());
		p.push_back(y);
		size_constrain = size_constrain && 0 < y && y <= no_packets ;

		expr z = c.int_const(n1s.str().c_str());
		n1.push_back(z);
		size_constrain = ((size_constrain) && (0 < z) && (z <= no_nodes)) ; //no need to drop rules, 0 < z...


		constrain = constrain && !terminal_expr( n[i], table.terminal)         //cannot add/mod rule from ending vetex
		                      && ite( terminal_expr( n1[i], table.terminal) ,
		                    		  f1( n[i], p[i]  ) == n1[i],
		                    		  f1( n[i], p[i]  ) == f1( n1[i], p[i])    //TODO: ???? what happens if n1[i], p[i] does not exits,
		                    		 )                                          // then an default value is placed

				              && guess( n[i], p[i]) == n1[i]
                              && topo_expr( n[i],  n1[i], table.edges);

	}


//compute T -- if something got added it got added from guess,
//             if something is modified, it is also added from guess and masked here...
// so all calls to rules actually belong in rules...

   for(unsigned iteg = 0; iteg < table.edges.size() ; iteg++)  //compute for all edges and all packets
   {

	  for( unsigned itp = 1 ; itp <= no_packets ;  itp++ )
	  {

		expr citn = c.int_val(table.edges[iteg].first);
		expr citp = c.int_val(itp);


		expr temp  = c.bool_val(true);
		for( unsigned itk = 0 ; itk < K ; ++itk )
		{
			temp = temp && (( citn != n[itk]) || ( citp !=  p[itk]) );      //true when no match, false when matched
		}

       pair<int,int> np = make_pair(table.edges[iteg].first, itp) ; //node-packet pair



       bool inrule = false;
       try{
    	   table.rules.at(np); //throws exception if edge-packet pair not in rule
    	   inrule = true;
    	   }
       catch(std::out_of_range xx)
       {  inrule=false;  }



       if(inrule==true)
       {
		 if( !( findVec( table.terminal, table.rules.at(np)) )) // n1 not terminal

			 constrain = constrain && ite( temp ,
									  f1( citn, citp ) == f1(  R(citn, citp), citp )
							       && f1(citn,citp ) > c.int_val(0) && f1(citn,citp) <= c.int_val(no_nodes), // c.int_val(table.rules.at(np)), citp) ,   // true  if no match in table...
									  c.bool_val(true)   					//false if match in table
									 );
		 else

			 constrain = constrain && ite( temp ,
										   f1( citn, citp ) ==  R(citn, citp)
										&& f1(citn,citp ) > c.int_val(0) && f1(citn,citp) <= c.int_val(no_nodes),   // c.int_val(table.rules.at(np)) , // true  if no match in table...
										   c.bool_val(true)   					//false if match in table
										 );

       }

       else  constrain = constrain && ite( temp, //not found in rule or guessed...
				                        f1(citn, citp) == c.int_val(0),
				                        c.bool_val(true)
				                      );



	  }
	}//end of all edge all packet


   //modified functionality of source
	constrain = constrain && f1( c.int_val(table.source), c.int_val(table.pac))  == c.int_val(table.to) ;


	//all other functionality remains the same
	for( auto ipac = table.final.begin(); ipac!=table.final.end(); ++ipac )
	{

		if( ipac->first.second == table.pac) continue; // the graph can change for pac, hence skip it//

		constrain = constrain && f1( c.int_val(ipac->first.first), c.int_val(ipac->first.second))  == c.int_val(ipac->second) ;

	}


    // complete formula
	expr ex =  exists( n,  exists( p,  exists( n1,
			          initial_graph && size_constrain && constrain )));

    check_sat(ex);

}




int main() { try {
	const clock_t begin_time = clock();

	rules table;
	table = parse_tf("network.tf");

	FILE *out1 = fopen("parse.txt", "w");
	fprintf(out1, "%s", table.print().c_str());
	fclose(out1);


	rules_compact table_c;
    table_c = compact_rules(table);

    cout<<table_c.nodes.size();

	FILE *out = fopen("parse_c.txt", "w");
	fprintf(out, "%s", table_c.print().c_str());
	fclose(out);

	//all edges
	write_to_Dot(table_compact_to_dot(table_c) ,"all", "svg");


	loc_packet lpk;
	lpk.node = 1200000;
	lpk.pk.pos.vlan = -1 ;
	//00001010000000000000 00 11111 101 xx
	lpk.pk.pos.ip_dst = string(32,'x');
	lpk.pk.pos.ip_src = string(32,'x');
	lpk.pk.pos.ip_proto = -1;
	lpk.pk.pos.tcp_ctrl = -1;
	lpk.pk.pos.tcp_dst =  -1;
	lpk.pk.pos.tcp_src =  -1;
	lpk.pk.neg = unordered_set<fields>();



	EqClass all = reachability(lpk, table_c);

	//select a path which matches any of these
	vector<int> through;
	//through.push_back(1000000);
	through.push_back(1000001);
	through.push_back(1000435);
	through.push_back(1000373);
	through.push_back(1000311);
	through.push_back(1000249);
	through.push_back(1000187);


	symbolic_rules sym_table = generate_symbolic_graph(all, 1200000, 1000055, 1000437,through);
	sym_table.K = 6 ;

	naive(sym_table);


//		loc_packet lpk;
//		lpk.node = 1200000;
//		lpk.pk.pos.vlan = -1 ;
//		//00001010000000000000 00 11111 101 xx
//		lpk.pk.pos.ip_dst = "xxxxxxxxxxxxxxxxxxxxx0x1111xxxxx"; //string(32,'x');
//		lpk.pk.pos.ip_src = string(32,'x');
//		lpk.pk.pos.ip_proto = 6;
//		lpk.pk.pos.tcp_ctrl = -1;
//		lpk.pk.pos.tcp_dst =  346;
//		lpk.pk.pos.tcp_src =  354;
//		lpk.pk.neg = unordered_set<fields>();


//	symbolic_rules custom ;
//
//	custom.source = 1;
//	custom.to = 7;
//	custom.pac =  1 ;
//
//	custom.no_nodes = 14;
//	custom.no_packet = 7 ;
//
//
//	custom.rules.insert({make_pair(1,1),8});
//	custom.rules.insert({make_pair(1,2),8});
//	custom.rules.insert({make_pair(1,3),8});
//	custom.rules.insert({make_pair(1,4),8});
//
//	custom.rules.insert({make_pair(8,1),9});
//	custom.rules.insert({make_pair(8,2),9});
//	custom.rules.insert({make_pair(8,3),9});
//	custom.rules.insert({make_pair(8,4),9});
//
//	custom.rules.insert({make_pair(9,1),10});
//	custom.rules.insert({make_pair(9,2),10});
//	custom.rules.insert({make_pair(9,3),10});
//
//	custom.rules.insert({make_pair(9,4),13});
//
//
//	custom.rules.insert({make_pair(10,1),11});
//	custom.rules.insert({make_pair(10,2),11});
//
//	custom.rules.insert({make_pair(10,3),12});
//
//	custom.rules.insert({make_pair(11,1),14});
//	custom.rules.insert({make_pair(11,2),14});
//
//
//	custom.rules.insert({make_pair(1,5),2});
//	custom.rules.insert({make_pair(1,6),2});
//	custom.rules.insert({make_pair(1,7),2});
//
//	custom.rules.insert({make_pair(2,5),4});
//
//	custom.rules.insert({make_pair(2,6),3});
//	custom.rules.insert({make_pair(2,7),3});
//
//	custom.rules.insert({make_pair(3,7),5});
//	custom.rules.insert({make_pair(3,6),6});
//
//	custom.rules.insert({make_pair(6,6),7});
//
//
//	custom.edges.push_back(make_pair(1,2));
//	custom.edges.push_back(make_pair(2,3));
//	custom.edges.push_back(make_pair(3,5));
//	custom.edges.push_back(make_pair(3,6));
//	custom.edges.push_back(make_pair(6,7));
//
//	custom.edges.push_back(make_pair(2,4));
//
//	custom.edges.push_back(make_pair(1,8));
//	custom.edges.push_back(make_pair(8,9));
//	custom.edges.push_back(make_pair(9,10));
//	custom.edges.push_back(make_pair(10,11));
//	custom.edges.push_back(make_pair(11,14));
//
//	custom.edges.push_back(make_pair(10,12));
//	custom.edges.push_back(make_pair(9,13));
//
//
//	custom.terminal.push_back(14);
//	custom.terminal.push_back(12);
//	custom.terminal.push_back(13);
//	custom.terminal.push_back(4);
//	custom.terminal.push_back(7);
//	custom.terminal.push_back(5);
//
//
//	custom.final.insert({make_pair(1,1),14});
//	custom.final.insert({make_pair(1,2),14});
//	custom.final.insert({make_pair(1,3),12});
//	custom.final.insert({make_pair(1,4),13});
//	custom.final.insert({make_pair(1,5),4});
//	custom.final.insert({make_pair(1,6),7});
//	custom.final.insert({make_pair(1,7),5});
//
//
//	custom.final.insert({make_pair(8,1),14});
//	custom.final.insert({make_pair(8,2),14});
//	custom.final.insert({make_pair(8,3),12});
//	custom.final.insert({make_pair(8,4),13});
//
//
//	custom.final.insert({make_pair(10,1),14});
//	custom.final.insert({make_pair(10,2),14});
//	custom.final.insert({make_pair(10,3),12});
//
//	custom.final.insert({make_pair(11,1),14});
//	custom.final.insert({make_pair(11,2),14});
//
//	custom.final.insert({make_pair(2,5),4});
//	custom.final.insert({make_pair(2,6),7});
//	custom.final.insert({make_pair(2,7),5});
//
//
//	custom.final.insert({make_pair(3,6),7});
//	custom.final.insert({make_pair(3,7),5});
//
//	custom.final.insert({make_pair(6,6),7});
//
//
//	custom.K = 10;
//	naive(custom);


//	symbolic_rules custom ;
//
//	custom.rules.insert({make_pair(1,2),2});
//
//	custom.rules.insert({make_pair(2,1),3});
//	custom.rules.insert({make_pair(2,2),5});
//
//	custom.rules.insert({make_pair(5,2),6});
//	custom.rules.insert({make_pair(6,2),8});
//
//	custom.rules.insert({make_pair(3,1),4});
//	custom.rules.insert({make_pair(4,1),7});
//
//	//custom.rules.insert({make_pair(3,2),4});
//	//custom.rules.insert({make_pair(4,2),7});
//
//
//	custom.edges.push_back(make_pair(1,2));
//	custom.edges.push_back(make_pair(2,3));
//	custom.edges.push_back(make_pair(3,4));
//	custom.edges.push_back(make_pair(2,5));
//	custom.edges.push_back(make_pair(5,6));
//	custom.edges.push_back(make_pair(6,8));
//	custom.edges.push_back(make_pair(4,7));
//	custom.edges.push_back(make_pair(4,9));
//	custom.edges.push_back(make_pair(9,10));
//	custom.edges.push_back(make_pair(10,11));
//
//
//	custom.terminal.push_back(7);
//	custom.terminal.push_back(8);
//	custom.terminal.push_back(11);
//
//
//    custom.K = 6;
//	naive(custom);


	cout << "total time = " << float( clock () - begin_time ) /  CLOCKS_PER_SEC;

   } catch (z3::exception & ex){ cout << "unexpected z3   error: " << ex << "\n"; }
	return 0;
}







