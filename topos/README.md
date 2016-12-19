## Networks and Policies

### Topologies

Networks with dataplane state:

* Veriflow Rocketfuel AS 1755 (from BGP replay)
* Stanford
* Internet2

Topologies:

* Fattree
* 10 Rocketfuel topos:

  1. AS 1221 (#nodes: 5023, #edges: 21526)
  2. AS 1239 (#nodes: 16943, #edges: 71620)
  3. AS 1755 (#nodes: 957, #edges: 3914)
  4. AS 2914 (#nodes: 10830, #edges: 52140)
  5. AS 3257 (#nodes: 1223, #edges: 4600)
  6. AS 3356 (#nodes: 5328, #edges: 36526)
  7. AS 3967 (#nodes: 1480, #edges: 7218)
  8. AS 4755 (#nodes: 592, #edges: 2204)
  9. AS 6461 (#nodes: 2720, #edges: 10312)
  10. AS 7018 (#nodes: 20593, #edges: 78984)

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


### Specifications

* Reachability requirement in the presence of migration. Assume traffic from Vi can reach Vj, where Vi and Vj are two virtual machines that reside in the DC. Vi is connected to the DC via a set of edge switches {S1,S2, ...}, and Vj is connected to the DC via {D1,D2,...}. Now, if Vj migrates to a new location {D1',D2',...}, The NetGen policy will be like: match{src_IP = Vi_IP}, {S1,S2,...}: .*(D1+D2+...) => .*(D1'+D2'+...)
* Waypoint requirement in the face of middle-box scaling-out/in. Assume traffic from Vi to Vj is required to pass a firewall FW. Originally, the FW is implemented in two locations F1,F2. Now, if the DC adds a third one (for better performance) F3, the NetGen policy could be:
match(*), {S1,S2,...}: .* (F1+F2).* => .* (F1+F2+F3).* A similar NetGen policy can be used for the case of scaling in firewall implementation from three to two.
* Change of waypoint policy with new functionality. Assume the original waypoint requirement is FW >> LB (traffic sequentially passes firewall and load balancer). Now, a monitoring middlebox is introduced and the intention is to have LB and the monitor (MN) to process traffic in either order. The NetGen policy will be like:
match(*): {S1,S2,...}: .* FW LB .* => .* FW ((LB MN) + (MN LB)) .*
