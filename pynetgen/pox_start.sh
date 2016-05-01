#!/bin/bash

PYTHONPATH=.:~/src/netgen/pynetgen
./pox.py \
    log.level --DEBUG \
    openflow.of_01 --port=6633 \
    forwarding.l2_learning \
    host_tracker \
    openflow.discovery \
    topology \
    pox_netgen
