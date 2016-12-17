## Networks and Policies

### Topologies

Networks with dataplane state:
* Veriflow Rocketfuel AS 1755 (from BGP replay)
* Stanford
* Internet2

Topologies:
* Fattree
* 10 Rocketfuel topos:
  * AS 1221 (#nodes: 5023, #edges: 21526)
  * AS 1239 (#nodes: 16943, #edges: 71620)
  * AS 1755 (#nodes: 957, #edges: 3914)
  * AS 2914 (#nodes: 10830, #edges: 52140)
  * AS 3257 (#nodes: 1223, #edges: 4600)
  * AS 3356 (#nodes: 5328, #edges: 36526)
  * AS 3967 (#nodes: 1480, #edges: 7218)
  * AS 4755 (#nodes: 592, #edges: 2204)
  * AS 6461 (#nodes: 2720, #edges: 10312)
  * AS 7018 (#nodes: 20593, #edges: 78984)

Generating dataplane state:
* Random: N paths created between random pairs of nodes, rules compressed
* RouteViews: RIB feeds replayed by randomly assigning IPs to nodes, rules compressed
* Note: rules are compressed to avoid only exact-match rules, resulting in one packet class per flow



### Policy Types

* Reachability: a valid path should exist from node _src_ to _dst_
* Path length: a valid path should exist from node _src_ to _dst_ within _N_ hops
* Shortest path: a path from _src_ to _dst_ takes the shortest path
* Multipath: more than one path exists from _src_ to _dst_
* Segmentation: a set of nodes _src_ should not be able to reach a set of nodes _dst_
* Waypoint: traffic starting from _src_ should traverse node _w_
* Symmetry: a path from _src_ to _dst_ takes the same path as _dst_ to _src_
* Asymmetry: a path from _src_ to _dst_ uses a different path than _dst_ to _src_
