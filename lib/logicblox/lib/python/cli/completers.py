"""
Copyright 2013 LogicBlox, Inc.

All rights reserved.

Redistribution and use in source and binary forms, with or 
without modification, are permitted provided that the following 
conditions are met:

Redistributions of source code must retain the above copyright 
notice, this list of conditions and the following disclaimer.

Redistributions in binary form must reproduce the above copyright 
notice, this list of conditions and the following disclaimer 
in the documentation and/or other materials provided with the 
distribution.

Neither the name of LogicBlox nor the names of its contributors 
may be used to endorse or promote products derived from this 
software without specific prior written permission.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS 
"AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT 
LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS 
"""
import dbcommands.lb_all_commands as lb_all_commands

def WorkspaceCompleter(prefix, action, parser, parsed_args):
    return lb_all_commands.get_list_workspaces(parsed_args)

def BranchCompleter(prefix, action, parser, parsed_args):	
    ### assumes that parsed_args has an argument named workspace
    if hasattr(parsed_args, 'workspace'):
        if not hasattr(parsed_args, 'all'):
            setattr(parsed_args, 'all', False)
        return lb_all_commands.get_list_branches(parsed_args)

def PredicateCompleter(prefix, action, parser, parsed_args):
    ### assumes that parsed_args has an argument named workspace
    if hasattr(parsed_args, 'workspace'):
        return lb_all_commands.get_list_predicates(parsed_args)
