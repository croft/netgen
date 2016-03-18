/*
 * This file is protected by the VeriFlow Research License Agreement
 * available at http://www.cs.illinois.edu/~khurshi1/projects/veriflow/veriflow-research-license-agreement.txt.
 * A copy of this agreement is also included in this package.
 *
 * Copyright (c) 2012-2013 by
 * The Board of Trustees of the University of Illinois.
 * All rights reserved.
 */

#ifndef LOG_H_
#define LOG_H_

#include <sys/types.h>
#include <unistd.h>
#include <cstdio>

using namespace std;

void LOG(FILE* fp, char* msg);

#endif /* LOG_H_ */
