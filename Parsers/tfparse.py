#!/usr/bin/env python

from utils.load_stanford_backbone import *
from utils.load_internet2_backbone import *
from headerspace.applications import *
from headerspace.hs import *
from headerspace.tf import *
from config_parser.cisco_router_parser import ciscoRouter
from config_parser.juniper_parser import juniperRouter
from config_parser.transfer_function_to_openflow import OpenFlow_Rule_Generator
import random, time, sqlite3, os, json, socket, struct, sys
from argparse import ArgumentParser
from graphviz import Graph

ip_intf = {}
edge_ports = set()
ip_count = 0
topo_map = {}

stanford_topo = [("bbra_rtr","te7/3","goza_rtr","te2/1"),
                 ("bbra_rtr","te7/3","pozb_rtr","te3/1"),
                 ("bbra_rtr","te1/3","bozb_rtr","te3/1"),
                 ("bbra_rtr","te1/3","yozb_rtr","te2/1"),
                 ("bbra_rtr","te1/3","roza_rtr","te2/1"),
                 ("bbra_rtr","te1/4","boza_rtr","te2/1"),
                 ("bbra_rtr","te1/4","rozb_rtr","te3/1"),
                 ("bbra_rtr","te6/1","gozb_rtr","te3/1"),
                 ("bbra_rtr","te6/1","cozb_rtr","te3/1"),
                 ("bbra_rtr","te6/1","poza_rtr","te2/1"),
                 ("bbra_rtr","te6/1","soza_rtr","te2/1"),
                 ("bbra_rtr","te7/2","coza_rtr","te2/1"),
                 ("bbra_rtr","te7/2","sozb_rtr","te3/1"),
                 ("bbra_rtr","te6/3","yoza_rtr","te1/3"),
                 ("bbra_rtr","te7/1","bbrb_rtr","te7/1"),
                 ("bbrb_rtr","te7/4","yoza_rtr","te7/1"),
                 ("bbrb_rtr","te1/1","goza_rtr","te3/1"),
                 ("bbrb_rtr","te1/1","pozb_rtr","te2/1"),
                 ("bbrb_rtr","te6/3","bozb_rtr","te2/1"),
                 ("bbrb_rtr","te6/3","roza_rtr","te3/1"),
                 ("bbrb_rtr","te6/3","yozb_rtr","te1/1"),
                 ("bbrb_rtr","te1/3","boza_rtr","te3/1"),
                 ("bbrb_rtr","te1/3","rozb_rtr","te2/1"),
                 ("bbrb_rtr","te7/2","gozb_rtr","te2/1"),
                 ("bbrb_rtr","te7/2","cozb_rtr","te2/1"),
                 ("bbrb_rtr","te7/2","poza_rtr","te3/1"),
                 ("bbrb_rtr","te7/2","soza_rtr","te3/1"),
                 ("bbrb_rtr","te6/1","coza_rtr","te3/1"),
                 ("bbrb_rtr","te6/1","sozb_rtr","te2/1"),
                 ("boza_rtr","te2/3","bozb_rtr","te2/3"),
                 ("coza_rtr","te2/3","cozb_rtr","te2/3"),
                 ("goza_rtr","te2/3","gozb_rtr","te2/3"),
                 ("poza_rtr","te2/3","pozb_rtr","te2/3"),
                 ("roza_rtr","te2/3","rozb_rtr","te2/3"),
                 ("soza_rtr","te2/3","sozb_rtr","te2/3"),
                 ("yoza_rtr","te1/1","yozb_rtr","te1/3"),
                 ("yoza_rtr","te1/2","yozb_rtr","te1/2"),
             ]

internet2_topo = [("chic","xe-0/1/0","newy32aoa","xe-0/1/3"), #05667
                  ("chic","xe-1/0/1","kans","xe-0/1/0"), #05568
                  ("chic","xe-1/1/3","wash","xe-6/3/0"), #05250
                  ("hous","xe-3/1/0","losa","ge-6/0/0"), #05559
                  ("kans","ge-6/0/0","salt","ge-6/1/0"), #05138
                  ("chic","xe-1/1/2","atla","xe-0/1/3"), #05638
                  ("seat","xe-0/0/0","salt","xe-0/1/1"), #05565
                  ("chic","xe-1/0/2","kans","xe-0/0/3"), #05781
                  ("hous","xe-1/1/0","kans","xe-1/0/0"), #05560
                  ("seat","xe-0/1/0","losa","xe-0/0/0"), #05564
                  ("salt","xe-0/0/1","losa","xe-0/1/3"), #05571
                  ("seat","xe-1/0/0","salt","xe-0/1/3"), #05573
                  ("newy32aoa","et-3/0/0-0","wash","et-3/0/0-0"), #06126
                  ("newy32aoa","et-3/0/0-1","wash","et-3/0/0-1"), #06126-2
                  ("chic","xe-1/1/1","atla","xe-0/0/0"), #05419
                  ("losa","xe-0/1/0","seat","xe-2/1/0"), #05572
                  ("hous","xe-0/1/0","losa","ge-6/1/0"), #05581
                  ("atla","xe-0/0/3","wash","xe-1/1/3"), #05251
                  ("hous","xe-3/1/0","kans","ge-6/2/0"), #05561
                  ("atla","ge-6/0/0","hous","xe-0/0/0"), #05423
                  ("chic","xe-1/0/3","kans","xe-1/0/3"), #05976
                  ("losa","xe-0/0/3","salt","xe-0/1/0"), #05563
                  ("atla","ge-6/1/0","hous","xe-1/0/0"), #05562
                  ("atla","xe-1/0/3","wash","xe-0/0/0"), #06366
                  ("chic","xe-2/1/3","wash","xe-0/1/3"), #05637
                  ("atla","xe-1/0/1","wash","xe-0/0/3"), #05133
                  ("kans","xe-0/1/1","salt","ge-6/0/0"), #05566
                  ("chic","xe-1/1/0","newy32aoa","xe-0/0/0"), #05239
              ]

def ip2int(addr):
    return struct.unpack("!I", socket.inet_aton(addr))[0]

def int2ip(addr):
    return socket.inet_ntoa(struct.pack("!I", addr))

def wc2ip(wc):
    if wc == 0:
        return int2ip(int("1"*32, 2))

    return int2ip(int("1"*32, 2) ^ int("1"*wc, 2))

def next_ip():
    global ip_count
    base = 16777217 # ip=1.0.0.1
    base += ip_count
    ip_count +=1
    return int2ip(base)

def make_rocketfile(tf, ntf, router_type, portmap, dest):
    ofg = OpenFlow_Rule_Generator(tf, router_type.HS_FORMAT())
    rules = ofg.generate_of_rules()
    lines = []

    # print dir(tf.rules[120]['action'])
    # for k in ['rewrite', 'out_ports', 'match', 'mask', 'action']:
    #     print tf.rules[120][k]
    # print rules[120]
    # return

    goza = []
    gozb = []

    for rule in rules:
        dst = int2ip(rule['ip_dst_match'])
        wc = wc2ip(rule['ip_dst_wc'])
        outports = rule['out_ports']
        location = tf.prefix_id
        priority = 1

        # print rule['transport_src_new'], \
        #     rule['transport_dst_new'], \
        #     rule['ip_src_new'], \
        #     rule['ip_dst_new'], \
        #     rule['ip_proto_new'], \
        #     rule['vlan_match'], \
        #     rule['vlan_new']
        for k in rule.keys():
            if 'new' in k:
                if k != 'vlan_new' and rule[k] is not None:
                    print k, rule[k]

        nexthops = []
        for port in outports:
            if port in edge_ports:
                # TODO
                pass
            else:
                p = str(port - router_type.PORT_TYPE_MULTIPLIER)
                if p in portmap.keys():
                    portname = portmap[p].split("-")[1]
                    if portname in topo_map[location].keys():
                        nexthop = topo_map[location][portname]
                        nexthops.append(nexthop)
                    else:
                        # TODO
                        pass

        line = "- - {0} {1} {2} {3} - {4}\n".format(dst, wc, location,
                                                    ",".join(nexthops), priority)

        lines.append(line)

        if len(nexthops) == 1:
            line = "{0} {1} {2}".format(line.strip(), rule['vlan_match'], rule['vlan_new'])
            if nexthops[0] == 'gozb_rtr':
                gozb.append(line.strip())
            elif nexthops[0] == 'goza_rtr':
                goza.append(line.strip())

        # for nexthop in nexthops:
        #     line = "- - {0} {1} {2} {3} - {4}\n".format(dst, wc, location,
        #                                                 nexthop, priority)
        #     lines.append(line)

    if len(goza) > 1:
        print "\n---------------------------------------\n"
        print "\n".join(sorted(goza))
    if len(gozb) > 1:
        print "\n---------------------------------------\n"
        print "\n".join(sorted(gozb))

    with open(os.path.join(dest, "R_" + tf.prefix_id), 'w') as f:
        f.writelines(lines)

def make_topofile(topo, dest):
    with open(os.path.join(dest, "topo.txt"), 'w') as f:
        f.writelines(["{0} {1}\n".format(rtr1, rtr2) for
                      rtr1, intf1, rtr2, intf2 in topo])

def make_graph(topo, dest):
    g = Graph(format='svg')
    for rtr1, intf1, rtr2, intf2 in topo:
        g.node(rtr1)
        g.node(rtr2)
        g.edge(rtr1, rtr2)

    g.render(os.path.join(dest, "topo.gv"))

def main():
    parser = ArgumentParser(description="TF Parser")
    parser.add_argument("--stanford", "-s", dest="stanford",
                        action="store_true", default=False,
                        help="Parse Stanford topology")
    parser.add_argument("--internet2", "-i", dest="internet2",
                        action="store_true", default=False,
                        help="Parse Internet2 topology")
    parser.add_argument("--test", "-t", dest="test",
                        action="store_true", default=False,
                        help="Test parse on file")

    args = parser.parse_args()

    if len(sys.argv) == 1:
        parser.print_help()
        sys.exit(0)

    if not os.path.isdir("data"):
        os.makedirs("data")

    if args.stanford and args.internet2:
        print "Select either --stanford and --internet2"
        sys.exit(0)

    tflist = []

    if args.stanford:
        router = ciscoRouter(1)
        ntf = load_stanford_backbone_ntf()
        ttf = load_stanford_backbone_ttf()
        (port_map, port_reverse_map) = load_stanford_backbone_port_to_id_map()
        tflist = ntf.tf_list
        topo = stanford_topo

    if args.internet2:
        router = juniperRouter(1)
        ntf = load_internet2_backbone_ntf()
        ttf = load_internet2_backbone_ttf()
        (port_map, port_reverse_map) = load_internet2_backbone_port_to_id_map()
        tflist = ntf.tf_list
        topo = internet2_topo

    if args.test:
        router = ciscoRouter(1)
        tf = TF(1)
        # ntf = load_stanford_backbone_ntf()
        ntf = None
        tf.load_object_from_file("../data_set/tf_stanford_backbone/bbra_rtr.tf")
        (port_map, port_reverse_map) = load_stanford_backbone_port_to_id_map()
        tflist = [tf]
        topo = stanford_topo

    for rtr in port_map.keys():
        for port in port_map[rtr].values():
            edge_ports.add(int(port) +
                           router.PORT_TYPE_MULTIPLIER *
                           router.OUTPUT_PORT_TYPE_CONST)

    for rtr1, intf1, rtr2, intf2 in topo:
        if rtr1 not in topo_map:
            topo_map[rtr1] = {}
        topo_map[rtr1][intf1] = rtr2

        if rtr2 not in topo_map:
            topo_map[rtr2] = {}
        topo_map[rtr2][intf2] = rtr1

    for tf in tflist:
        make_rocketfile(tf, ntf, router, port_reverse_map, "data")

    make_topofile(topo, "data")
    make_graph(topo, "data")

if __name__ == "__main__":
    main()
