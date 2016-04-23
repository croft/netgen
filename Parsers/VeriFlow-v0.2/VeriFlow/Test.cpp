/*
 * Test.cpp
 *
 *  Created on: Jul 15, 2012
 *      Author: khurshid
 *
 * This file is protected by the VeriFlow Research License Agreement
 * available at http://www.cs.illinois.edu/~khurshi1/projects/veriflow/veriflow-research-license-agreement.txt.
 * A copy of this agreement is also included in this package.
 *
 * Copyright (c) 2012-2013 by
 * The Board of Trustees of the University of Illinois.
 * All rights reserved.
 */

#include <sys/types.h>
#include <unistd.h>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <iostream>
#include <fstream>
#include <string>
#include <vector>
#include <map>
#include <sys/time.h>
#include <dirent.h>
#include "Test.h"
#include "Trie.h"
#include "VeriFlow.h"
#include "Rule.h"
#include "EquivalenceClass.h"
#include "../veriflow-util/openflow.h"
#include "../veriflow-util/StringTokenizer.h"
#include <sstream>

using namespace std;


extern VeriFlow veriflow;
void testRocketfuelRouteViewsDataset()
{
	string baseDir = "data";
	DIR *dp;
	struct dirent *dirp;
	vector< string > deviceFileList;

	if((dp = opendir(baseDir.c_str())) == NULL)
	{
		fprintf(stderr, "Error opening %s\n", baseDir.c_str());
		return;
	}

	while((dirp = readdir(dp)))
	{
		if((strcmp(dirp->d_name, ".") == 0) || (strcmp(dirp->d_name, "..") == 0)||dirp->d_name[0]!='R')
		{
			continue;
		}

		string fileName = baseDir + "/" + dirp->d_name;
		deviceFileList.push_back(fileName);

	}

	closedir(dp);

//	fprintf(stdout, "Total device count: %lu\n", deviceFileList.size());
//	fflush(stdout);

	char buffer[1024];



	for(unsigned int i = 0; i < deviceFileList.size(); i++)
	{
		fprintf(stdout, "[%u] Processing %s\n", i, deviceFileList[i].c_str());
		fflush(stdout);
		ifstream fin(deviceFileList[i].c_str());
		while(fin.eof() == false)
		{
			fin.getline(buffer, 1023);
			if(strlen(buffer) == 0)
			{
				continue;
			}


			StringTokenizer st(buffer, " ");
			Rule rule;


			rule.type = FORWARDING;
			rule.fieldValue[DL_SRC] = "0:0:0:0:0:0";
			rule.fieldMask[DL_SRC] = "0:0:0:0:0:0";
			rule.fieldValue[DL_DST] = "0:0:0:0:0:0";
			rule.fieldMask[DL_DST] = "0:0:0:0:0:0";
			rule.fieldValue[NW_SRC] = "0.0.0.0";
			rule.fieldMask[NW_SRC] = "0.0.0.0";
			st.nextToken();
			st.nextToken();
			rule.fieldValue[NW_DST] = st.nextToken();
			if(rule.fieldValue[NW_DST].find('/') != string::npos)
			{
				rule.fieldValue[NW_DST] = rule.fieldValue[NW_DST].substr(0, rule.fieldValue[NW_DST].find('/'));
			}

			rule.fieldMask[NW_DST] = st.nextToken();
			rule.wildcards = OFPFW_ALL;
			rule.location = st.nextToken();
			rule.nextHop = st.nextToken();
			st.nextToken();

			rule.priority = atoi(st.nextToken().c_str());


			veriflow.addRule(rule);
		}

		fin.close();
	}
}






void Test::test()
{
  //Test::testVerification();
	FILE* fout = fopen("time.out", "w");
	struct timeval t, t1;
	gettimeofday(&t, NULL);
	testRocketfuelRouteViewsDataset();
	vector< EquivalenceClass > vFinalPacketClasses;
	vector< vector< Trie* > > vFinalTries;
	
	veriflow.getAllEquivalenceClasses(vFinalPacketClasses, vFinalTries);

	cout<<"Number of classes: "<<vFinalPacketClasses.size()<<endl;

	for(unsigned  i =0;  i< vFinalPacketClasses.size(); i++ )
	{
		//cout<<itr->toString();		
		//cout<<endl;
	 	ForwardingGraph *g=veriflow.getForwardingGraph(vFinalTries[i], vFinalPacketClasses[i]);
		cout<<"Writing Graph "<<i<<endl;
		stringstream filename; 
		filename<<"class/"<<i<<".txt"; 
		ofstream myfile(filename.str().c_str(),std::ofstream::out); 

	  	for(unordered_map<string,list<ForwardingLink> >::const_iterator itr2=g->links.begin();itr2!=g->links.end();itr2++)
		{
		 	  myfile<<i<<" "<<itr2->first<<" "<<itr2->second.front().rule.nextHop<<endl;
			   
		}

		myfile.close(); 

	}
	cout<<"done"; 

	//	ForwardingGraph *g=veriflow.getForwardingGraph(vFinalTries[1],vFinalPacketClasses[1]);
	//	cout<<g->toString();

  




  
	gettimeofday(&t1, NULL);
	fprintf(fout, "%f\n", t1.tv_sec - t.tv_sec + 1E-6 * (t1.tv_usec - t.tv_usec));
	fclose(fout);

}
