/*
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
#include <sys/socket.h>
#include <netinet/in.h>
#include <arpa/inet.h>
#include "socks.h"

SocksAuthMethodRequest createSocksAuthMethodRequest(char ver, char mc, char m)
{
	SocksAuthMethodRequest req;
	req.version = ver;
	req.methodCount = mc;
	req.method = m;

	return req;
}

SocksAuthMethodResponse createSocksAuthMethodResponse(char ver, char m)
{
	SocksAuthMethodResponse res;
	res.version = ver;
	res.method = m;

	return res;
}

SocksConnRequest createSocksConnRequest(char ver, char cmd, char addrType, const char* ipAddr, unsigned short int port)
{
	SocksConnRequest req;
	req.version = ver;
	req.command = cmd;
	req.reserved = 0;
	req.addressType = addrType;
	req.ipAddress = (unsigned int)inet_addr(ipAddr);
	req.port = htons(port);

	return req;
}

SocksConnResponse createSocksConnResponse(char ver, char status, char addrType, const char* ipAddr, unsigned short int port)
{
	SocksConnResponse res;
	res.version = ver;
	res.status = status;
	res.reserved = 0;
	res.addressType = addrType;
	res.ipAddress = (unsigned int)inet_addr(ipAddr);
	res.port = htons(port);

	return res;
}
