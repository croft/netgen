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

def ip2int(addr):
    return struct.unpack("!I", socket.inet_aton(addr))[0]

def int2ip(addr):
    return socket.inet_ntoa(struct.pack("!I", addr))

def wc2ip(wc):
    if wc == 0:
        return int2ip(int("1"*32, 2))

    return int2ip(int("1"*32, 2) ^ int("1"*wc, 2))

def make_rocketfile(tf, router_type, portmap, dest):
    ofg = OpenFlow_Rule_Generator(tf, router_type.HS_FORMAT())
    rules = ofg.generate_of_rules()
    lines = []
    for rule in rules:
        dst = int2ip(rule['ip_dst_match'])
        wc = wc2ip(rule['ip_dst_wc'])
        outports = rule['out_ports']
        location = tf.prefix_id
        priority = 1
        for nexthop in outports:
            line = "- - {0} {1} {2} {3} - {4}\n".format(dst, wc, location,
                                                        nexthop, priority)
            lines.append(line)

    with open(os.path.join(dest, tf.prefix_id), 'w') as f:
        f.writelines(lines)
    
def main():
    parser = ArgumentParser(description="TF Parser")
    parser.add_argument("--standford", "-s", dest="stanford",
                        action="store_true", default=False,
                        help="Parse Stanford topology")
    parser.add_argument("--internet2", "-i", dest="internet2",
                        action="store_true", default=False,
                        help="Parse Internet2 topology")
    parser.add_argument("--test", "-t", dest="test",
                        action="store_true", default=False,
                        help="Test parse on file")

    args = parser.parse_args()

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

    if args.internet2:
        router = juniperRouter(1)
        ntf = load_internet2_backbone_ntf()
        ttf = load_internet2_backbone_ttf()
        (port_map, port_reverse_map) = load_internet2_backbone_port_to_id_map()
        tflist = ntf.tf_list

    if args.test:
        router = ciscoRouter(1)
        tf = TF(1)
        tf.load_object_from_file("../data_set/tf_stanford_backbone/bbra_rtr.tf")
        (port_map, port_reverse_map) = load_stanford_backbone_port_to_id_map()
        tflist = [tf]

    for tf in tflist:
        make_rocketfile(tf, router, port_reverse_map, "data")

if __name__ == "__main__":
    main()
