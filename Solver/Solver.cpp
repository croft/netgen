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



#include "z3++.h"

using namespace z3;
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
      stream << (*it)<<" , ";
    }
    stream<<"]";
  return stream;
}


template<typename T1,typename T2>
std::ostream &operator<<(std::ostream &stream, const std::pair<T1,T2> & p)
{
	stream<<"("<<p.first<<","<<p.second<<")"; 
  return stream;
}



int getdir (string dir, vector<string> &files)
{
    DIR *dp;
    struct dirent *dirp;
    if((dp  = opendir(dir.c_str())) == NULL) {
        cout << "Error(" << errno << ") opening " << dir << endl;
        return errno;
    }

    while ((dirp = readdir(dp)) != NULL) {
        files.push_back(string(dirp->d_name));
    }
    closedir(dp);
    return 0;
}




set<tuple<string,string,string>> readClass(string file) //packet from to
{
    
    set<tuple<string,string,string>> link;
    
    string line;
    
    std::ifstream infile(string(string("selected/" + file )));
    while (std::getline(infile, line))
    {
        
        std::istringstream iss(line);
        string fromstr, tostr,  packetstr;
        
        if (!(iss >> packetstr >> fromstr >> tostr )) { break; } // error
        
        
        tuple<string,string,string> pair;
        pair= make_tuple (packetstr,fromstr, tostr);
        
        link.insert(pair);
        
    }   
    
    return link; 
    
}


set<tuple<string,string,string>> readAllClasses()
{
    
    string dir = string("selected/");
    vector<string> files = vector<string>();
    
    getdir(dir,files);
    
    set<tuple<string,string,string>> alllinks;
    
    
    for( int i = 0; i< files.size(); i++ )
    {
        string temp = files[i];
      
        temp.erase ( temp.begin(), temp.end()-4);
//cout<<temp<<"\n";
        
        if(temp.compare(string(".txt")) != 0 ) { continue; }
        
        
        set<tuple<string,string,string>> links;
        
        links = readClass(files[i]);
        
        alllinks.insert(links.cbegin(), links.cend());
    
    }
    
    return alllinks;
    
}






void constructTopo()
{

	//ofstream topofile;
    //topofile.open ("topo", ios::out | ios::app );
  
    set<tuple<string,string> >allpairs; 


    string dir = string("../AS-1755/");
    vector<string> files = vector<string>();

    getdir(dir,files);

    vector<string> packet; 
	vector<string> from; 


    for (unsigned int i = 0;i < files.size();i++) 
    {
    	
    	string line;

    	std::ifstream infile(string("../AS-1755/" + files[i]).c_str());
   		while (std::getline(infile, line))
		{

    		std::istringstream iss(line);
    		string packetstr, tostr, fromstr; 
    		string t1, t2, t3, t4, t5, t6; 

    		//cout<<line; 
			//0 I 10.0.2.92 255.255.255.252 10.0.0.1 10.0.0.2 124 1
    		if (!(iss >> t1 >> t2 >> t3 >> t4 >> fromstr >> tostr >> t5 >> t6 )) { break; } // error

   				
   				tuple<string,string> pair; 
   				pair= make_tuple (fromstr,tostr);

   				allpairs.insert(pair); 
   				
   		}   


    }

    for( auto it = allpairs.begin() ; it != allpairs.end() ; ++it)
		cout<<"\n"<< get<0>(*it)<<"  "<<get<1>(*it) ;

}


set<tuple<string,string>> readTopo() // from to
{

	set<tuple<string,string>> allpairs; 

		string line;

    	std::ifstream infile(string("topo"));
   		while (std::getline(infile, line))
		{

    		std::istringstream iss(line);
    		string fromstr, tostr;  

    		if (!(iss >> fromstr >> tostr )) { break; } // error

   				
   				tuple<string,string> pair; 
   				pair= make_tuple (fromstr,tostr);

   				allpairs.insert(pair); 
   				
   		}   

   	 return allpairs; 

}




map<string, int> readNodes()
{

	map<string,int> routers; 

	string line;

    std::ifstream infile("../AS-1755/config.map" );
   	

    int count = 1; 

   	while (std::getline(infile, line))
	{

    	std::istringstream iss(line);
    	string t1, name; 

    	if (!(iss >> t1 >> name  )) { break; } // error

    	if(t1.compare(string("R")) != 0) { break; }

		name.erase (name.begin()); 

    	routers[ name ] = count; 

    	count = count +1; 

   	}   

   return routers; 

}


expr  topo_expr (expr  p1, expr  p2, vector<pair<int,int>> points)
{

	context & c = p1.ctx();

	expr ret = c.bool_val(false);

	for (unsigned int i =0 ; i< points.size() ; ++i )
	{
		ret = ret || ( p2 ==  c.int_val(points[i].first) && ( p1 == c.int_val( points[i].second) ) ) || ( p1 ==  c.int_val(points[i].first) && ( p2 == c.int_val( points[i].second) ) )  ;
	}

return ret ;
}


expr  is_egress (expr  p1, vector<int> terminal)
{

	context & c = p1.ctx();

	expr ret = c.bool_val(false);

	for (unsigned int i =0 ; i< terminal.size() ; ++i )
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


expr  is_firewall (expr  p1, vector<int> firewall)
{

	context & c = p1.ctx();

	expr ret = c.bool_val(false);

	for (unsigned int i =0 ; i< firewall.size() ; ++i )
	{
		ret = ret ||  ( p1 ==  c.int_val(firewall[i]) )   ;
	}

return ret ;
}



expr is_existing ( expr n, expr n1, map<pair<int,int>,int> abs_R)
{

	context & c = n.ctx();

	expr ret = c.bool_val(false);

	for ( auto it = abs_R.begin() ; it != abs_R.end() ; ++it )
	{
		ret = ret ||  ( n ==  c.int_val( (it->first).first) && ( n1 == c.int_val(it->second)) )
                  || ( n1 ==  c.int_val( (it->first).first) && ( n == c.int_val(it->second)))  ;
	}

return ret ;
}


expr in_R(expr n, expr p ,map<pair<int,int>,int> abs_R)
{

	context & c = n.ctx();

	expr ret = c.bool_val(false);

	for ( auto it = abs_R.begin() ; it != abs_R.end() ; ++it )
	{
		ret = ret ||  ( n ==  c.int_val( (it->first).first) && ( p == c.int_val( (it->first).second) ))  ;
	}

return ret ;
}

map<string,int> enumerateClass()
{
    
    
    map<string,int> abs_p;

    int count = 1 ;
    
    
    string dir = string("selected/");
    vector<string> files = vector<string>();
    
    
    getdir(dir,files);
    
    for(int i = 0; i< files.size(); i ++ )
    {
        
        string temp = files[i];
        
        temp.erase ( temp.begin(), temp.end()-4);
        //cout<<temp<<"\n";
        
        if(temp.compare(string(".txt")) != 0 ) { continue; }
        
        
        files[i].erase(files[i].end()-4,files[i].end() );
        
        abs_p[ files[i] ] = count ;
        count = count +1;
            
    }

    return abs_p;
    
}

int main()
{


    
    long double totaltime = 0;
    
    
    
    
	//get nodes
	map<string,int> routers; 
	
	routers = readNodes(); //starts at 1

    
    
    
    //    int through = 35;
    //    int to = 51;
    //    string file = "3155";
    
    
    //    int through = 169;
    //    int to = 35;
    //    string file = "3157";
    
    
//        int through = 165;
//        int to = 166;
//        string file = "3164";


//    int through = 48;
//    int to = 166;
//    string file = "3162";

    int through = 165;
    int to = 166;
    string file = "3157";

 

  	//constructTopo();
	vector<pair<int,int>> abs_topo;  //commutative

	set<tuple<string,string>> topo;  //commutative
	topo = readTopo(); 

	for( auto it = topo.begin(); it != topo.end() ; ++it )
	{

		if( routers.find(get<0>(*it) ) == routers.end() ||  routers.find(get<1>(*it) ) == routers.end() ) { continue; }

		abs_topo.push_back(make_pair(routers[get<0>(*it)],routers[ get<1>(*it)])); 

	}
	

    map<string,int> abs_p;
    
    

	//construct R
	map<pair<int,int>,int> abs_R; 

    
    
    
//    vector<string> files = vector<string>();
//    
//    getdir(string("selected/"),files);

    
//    for( int ft = 0; ft < files.size(); ft++ )
//    {
//        
    
//        string ss;
//        ss = files[ft];
//        
//        ss.erase(ss.begin(), ss.end()-4);
//        
//        if(ss.compare(string(".txt")) != 0 ) { continue; }
//        
    
        
        
        set<tuple<string,string,string>> link;
  
        link = readClass(file + string(".txt"));
    

        //cout<<files[ft]<<"\n";
      
        
//        ss = files[ft];
//        
//        ss.erase(ss.end()-4, ss.end());
//        
        abs_p[file] = 1;
    
        
        
    	for( auto it = link.begin(); it!= link.end(); ++it ) // rules I P -> I  // packet fixed to 1
    	{
    		if( routers.find(get<1>(*it) ) == routers.end() ||  routers.find(get<2>(*it) ) == routers.end() ) { continue; }
    
    		abs_R[make_pair(routers[get<1>(*it)], abs_p[get<0>(*it)] )] = routers[get<2>(*it)] ;
    		
    	}

    
    
    
    
    
    
    
    
//    set<tuple<string,string,string>> alllink;
//    alllink = readAllClasses();
//    
//    abs_p = enumerateClass();
//    
//    
//	for( auto it = alllink.begin(); it!= alllink.end(); ++it ) // rules I P -> I  // packet fixed to 1
//	{
//		if( routers.find(get<1>(*it) ) == routers.end() ||  routers.find(get<2>(*it) ) == routers.end() ) { continue; }
//
//		abs_R[make_pair(routers[get<1>(*it)], abs_p[get<0>(*it)] )] = routers[get<2>(*it)] ;
//		
//	}
    
    
    

    


	//construct firewall
    
    

	//construct egresss
	vector<int> abs_egress; 
    vector<int> abs_src;

    
    bool outgoing[200], incomming[200];
    for( int i = 1; i<= routers.size(); i ++)
    {   outgoing[i] =  false;
        incomming[i] =  false;
    }
    
    for( auto it = abs_R.begin(); it != abs_R.end() ; ++it )
    {
        
        //cout<<"\""<<it->first.first<<"\"  -- \""<<it->second <<"\" ;\n";
        
        if( it->first.first == it->second)
            abs_egress.push_back(it->second);
        
        outgoing [ it->first.first ] = true;
        incomming[ it-> second ] = true;
        
    }
    
    for( int i = 1; i < routers.size() ; i ++ )
    {
        
        if( outgoing[i] == false)
            abs_egress.push_back(i);
        
        if(incomming[i] == false)
            abs_src.push_back(i);
        
    }
    


    
    
    map<int,int> abs_od;
    
    for( int i = 0; i< abs_src.size(); i ++ )
    {
        
        int temp = abs_src[i];
        
        if( find(abs_egress.begin(), abs_egress.end(), temp ) != abs_egress.end() ) continue;
        
        while( find(abs_egress.begin(), abs_egress.end(), temp) == abs_egress.end() )
        {
            
           // cout<<temp <<" ";
            temp = abs_R[make_pair(temp,1)];
            
        }
        //cout<<"\n";
        abs_od[abs_src[i]] = temp;
        
        
    }

//        
//        int x;
//        x = routers.size() + 1;
//        routers["10.1.9.0"] = x;
//
//        
//        
//        abs_topo.push_back(make_pair(66,x));
//        abs_topo.push_back(make_pair(4,x));
//        abs_topo.push_back(make_pair(32,x));
//        abs_topo.push_back(make_pair(31,x));
//        abs_topo.push_back(make_pair(65,x));
//        abs_topo.push_back(make_pair(x,3));

        vector<int> abs_fw;
        abs_fw.push_back(through);

    
    
//        abs_topo.push_back(make_pair(127,x));
//        
    
    
    
    
    
    int packet = 1;
    unsigned no_packets = 1; 	//packet size set to 1
    unsigned no_nodes   = routers.size();

   
   // cout<<"\nrouters :\n"<< routers;
   // cout<<"\nabs_topo :"<<abs_topo;
   // cout<<"\n\nabs_R : \n"<<abs_R;
   // cout<<"\nabs_fw : "<<abs_fw;
   // cout<<"\nabs_egress : "<<abs_egress;
  //  cout<<"\nabs_src : "<<abs_src<<"\n";
        
    
    
    
 
    for( int loop = 1 ; loop < 10000 ; )
    {

        
     //   cout<<"\nStarting loop"<<loop;
        
        
        const unsigned K = loop;
        

        context c; 



        z3::sort I   = c.int_sort();
        z3::sort B   = c.bool_sort();

        expr b = c.bool_val(true); 


        expr_vector n(c);
        expr_vector p(c);
        expr_vector n1(c);


        func_decl f1    = c.function("f1"  , I, I, B ); // f: N , P -> Bool
        func_decl cycle = c.function("cycle ", I , I);  // cycle : Node -> Int
        func_decl f_od  = c.function("f_od", I, I , I);  // f_od : Node , P -> Egress
        func_decl guess = c.function("guess", I, I, I ); // change: N , P -> N1
        func_decl R = c.function("R", I, I, I ); // change: N , P -> N1
        
        
        
        for( auto it = abs_R.begin() ;  it !=  abs_R.end(); it++ )
        {
            
            b = b && R ( c.int_val((it->first).first) , c.int_val((it->first).second) ) == c.int_val(it->second) ;
            
        }
        
        
        

        b = b && f1(c.int_val(0),c.int_val(1)) == c.bool_val(false);
        b = b && f_od(c.int_val(0),c.int_val(1) ) ==c.int_val(0) ;
        b = b && cycle ( c.int_val(0) ) ==  c.int_val(0);

        
        
        
        // CASE1: f1(n,p) = false if n \in Egress
        for( unsigned int i = 0 ;i < abs_egress.size(); i ++ )
        {

            b = b && f1( c.int_val(abs_egress[i]), c.int_val(packet) ) == c.bool_val(false); 

            b = b && f_od ( c.int_val(abs_egress[i]), c.int_val(packet) ) ==  c.int_val(abs_egress[i]) ; 

            b = b && cycle ( c.int_val(abs_egress[i]) ) ==  c.int_val(0);

        }




        // CASE2: f1(n,p) = f1( n1, p) || fw(n)  if (n,p,n1) \in change
        for (unsigned int i = 0; i < K; i++)
        {
            stringstream ns,ps,n1s;
            ns << "n_" << i;
            ps << "p_" << i;
            n1s<< "n1_" << i ;

            //synthesised nodes cant be drop nodes or 0... 

            expr x = c.int_const(ns.str().c_str());
            n.push_back(x);
            b = b && (c.int_val(0) < x) && (x <= c.int_val(no_nodes)) ;


            expr y = c.int_const(ps.str().c_str());
            p.push_back(y);
            b = b && (c.int_val(0) < y) && (y <= c.int_val(no_packets)) ;


            expr z = c.int_const(n1s.str().c_str());
            n1.push_back(z);
            b = b && (c.int_val(0) < z) && (z <= c.int_val(no_nodes) ) ; 



            b = b && ! is_egress( n[i], abs_egress) 	// n : cannot add/mod rule from egress
            
                // n[i] is mutable

                 // && topo_expr ( n[i],  n1[i], abs_topo) // topo ....  select ( T , mk_pair( n[i],  n1[i] ) ) ;
                  
                 // && ! is_existing ( n[i], n1[i], abs_R) // try w/o it

                  && f1( n[i], p[i]  ) == ( f1( n1[i], p[i]) ||   is_firewall( n[i], abs_fw) )
                  
                  && cycle ( n[i]) > cycle( n1[i])

                  && f_od ( n[i], p[i] ) == f_od( n1[i] , p[i] )
                  && f_od ( n[i], p[i] ) >= c.int_val(1) && f_od ( n[i], p[i] ) <= c.int_val(no_nodes) //0 would mean unlinking
                  
            
                  && guess ( n[i], p[i]) == n1[i]  		 // pretty printing
                  
                  ; 

                    
        }





        // CASE3: o/w
        for (unsigned int i = 1 ; i <= no_nodes ; i ++ ) //1 or zero ???? 
        {


            //for(unsigned j = 0 ; j< packets.size(); j ++ )
            unsigned j = packet; 

            expr citn = c.int_val(i); 
            expr citp = c.int_val(j); 

            
            expr temp  = c.bool_val(true);
            for( unsigned itk = 0 ; itk < K ; ++itk )
            {
                temp = temp && (( citn != n[itk]) || ( citp !=  p[itk]) );      //true when no match, false when matched
            }		

            
            
            if ( abs_R.find(make_pair(i,j)) != abs_R.end() )
            {
            
            

            if (   (find(abs_egress.begin(), abs_egress.end(), (int)i ) == abs_egress.end() ))
                // (n,p) \in R and n !in Egress   abs_R.find(make_pair(i,1)) != abs_R.end() &&
             {

        
                b = b &&  ite ( temp   ,
                               //temp && in_R(citn,citp, abs_R)  ,

                                   //  f1(citn, citp) ==  (  f1(  R( c.int_val(i) ,c.int_val(j) ),citp ) ||  is_firewall(citn, abs_fw) ) // do in c++
                               f1(citn, citp) ==  (  f1(  R( c.int_val(i) ,c.int_val(j) ),citp ) ||  ( find( abs_fw.begin(), abs_fw.end(), (int) i ) != abs_fw.end() ) ) // do in c++
                               
                               &&  ( f1( citn, citp) == c.bool_val(true) || f1( citn, citp) == c.bool_val(false) )
                

                                &&  cycle ( citn ) >  cycle ( R( c.int_val(i) ,c.int_val(j) ) ) //c.int_val(abs_R[ make_pair(i,j)])  )
                                
                                
                                &&  f_od (citn, citp ) == f_od ( R( c.int_val(i) ,c.int_val(j) ), citp )
                              //  &&  f_od ( citn, citp  ) >= c.int_val(0) && f_od ( citn, citp  ) <= c.int_val(no_nodes) // ???? test without it///

                                , c.bool_val(true) ); 

            }
            
         }
        

        }



        
        
        //modified functionality of source
        
        for(int i = 0; i< abs_src.size(); i++ )
        {
            b = b && f1( c.int_val(abs_src[i]), c.int_val(1))  == c.bool_val(true) ;
            
            b = b && f_od( c.int_val(abs_src[i]) , c.int_val(1) )  == c.int_val(to); //c.int_val( abs_od[abs_src[i]] ); //119);
        
        }


        
        
        
        
         expr ex =  exists( n,  exists( p,  exists( n1, b )));



       // cout<<"calling z3"<<"\n";
         solver s (c); 


        
      //  clock_t tStart = clock();
        

        
         s.add(ex);
     
        clock_t tStart = clock();


        if( s.check() == sat )
         {
             

             cout<<((double)(clock() - tStart)/CLOCKS_PER_SEC);;
             model m = s.get_model();
             //  cout<<m;
             
             cout <<"\n"<< loop ;
             
             exit(0);
            
         }

         else {
             
           //  cout<<"unsat"<<"\n";
            
             loop  = loop + 1 ;
             
         }
            
        
        
    }
    
    
    //sanity checks
    //od in range
    //cycle inr ange
    
   // cout<<totaltime;

    return 0;
    
}




/*
 
 //		else if ( abs_R.find(make_pair(i,1)) == abs_R.end() &&   (find(abs_egress.begin(), abs_egress.end(), (int)i ) == abs_egress.end() ) )
 //		{
 //			 b = b && f_od( citn, citp ) == c.int_val(0);
 //
 //			 cout<<" in "<< i <<"\n\n";
 //
 //			 b = b &&  ite ( temp && ! is_firewall(citn, abs_fw)  ,
 //			    b = b && f1(citn, citp) == c.bool_val(false),
 //			    c.bool_val(true) );
 //		}

 */



/*
	Z3_symbol     proj_names[2];
	proj_names[0] = Z3_mk_string_symbol(c, "get_x");
    proj_names[1] = Z3_mk_string_symbol(c, "get_y");

  
    Z3_sort       proj_sorts[2];
    proj_sorts[0] = I.operator Z3_sort();
    proj_sorts[1] = I.operator Z3_sort();


	Z3_func_decl  mk_tuple_decl;
    Z3_func_decl  proj_decls[2];
    z3::sort pair ( c,   Z3_mk_tuple_sort(c, c.str_symbol("mk_pair") , 2, proj_names, proj_sorts, & mk_tuple_decl, proj_decls) ) ;
  

    func_decl get_x ( c,  proj_decls[0]); 
    func_decl get_y ( c,  proj_decls[1]); 
    func_decl mk_pair ( c, mk_tuple_decl); 


	//express R
	sort twodarray = c.array_sort(pair,I); 
	expr R = c.constant("R", twodarray );

	expr def_valR (c,Z3_mk_array_default(c, R)); 
	b = b && def_valR == c.int_val(0);



	//express T 
	sort twodset = c.array_sort(pair,B); 
	expr T = c.constant("T", twodset);

	expr def_valT (c,Z3_mk_array_default(c, T)); 
	b = b && def_valT == c.bool_val(false);

	for( auto it = topo.begin(); it != topo.end() ; ++it )
	{

		if( routers.find(get<0>(*it) ) == routers.end() ||  routers.find(get<1>(*it) ) == routers.end() ) { continue; }

		b = b &&  select(T, mk_pair(c.int_val( routers[ get<0>(*it) ]),c.int_val( routers[ get<1>(*it) ]))) == c.bool_val(true) ; 


	}


   	for( auto iteg = link.begin() ; iteg < link.end(); ++iteg)  //compute for all edges and all packets
   	{// for every node...   


	  //for( unsigned itp = 1 ; itp <= no_packets ;  itp++ )
	  //{


		expr citn = c.int_val( routers[get<1>(*iteg)] );
		expr citp = c.int_val(1); //set to 1 //c.int_val(itp);
		
		
		expr temp  = c.bool_val(true);
		for( unsigned itk = 0 ; itk < K ; ++itk )
		{
			temp = temp && (( citn != n[itk]) || ( citp !=  p[itk]) );      //true when no match, false when matched
		}		

		
		if( n1 != dest)// change to egress

			b = b && ite( ! temp ,  //match
						  f1(citn, citp) = f1( R (citn,citp),citp ) || fw(citn) , 
						  c.bool_val(true)
						)
		else

			b = b && ite( ! temp ,  //match
						  f1(citn, citp) =  fw(citn) , 
						  c.bool_val(true)
						)


	}


	goal g(c);
    g.add(ex);
    std::cout << g << "\n";
    tactic t1(c, "simplify");
    apply_result r = t1(g);
    std::cout << r << "\n";

	*/