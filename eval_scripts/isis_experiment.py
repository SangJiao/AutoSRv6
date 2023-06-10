#!/usr/bin/env python
# -*- coding: utf-8 -*-
'''
@Project ：AutoSRv6 
@File ：isis_experiment.py
@Author ：Lucky
@Date ：2023/3/9 10:59
'''

import argparse
import logging
import random
import sys
import os
import glob
from timeit import default_timer as timer
from synet.utils.topo_gen import read_topology_zoo_netgraph
from synet.utils.smt_context import VALUENOTSET
from synet.synthesis.ospf_heuristic import OSPFSyn as OSPFCEGIS
from synet.synthesis.ospf import OSPFSyn as OSPFConcrete
from synet.synthesis.connected import ConnectedSyn


def main():

    # Generate new random number seed if need
    seed = random.randint(0, sys.maxsize)
    print ("Generated new seed", seed)
    # This random generator MUST be used everywhere!!!!
    ospfRand = random.Random(seed)
    f = open('output/isis_time.csv', 'a')  # 打开数据文件
    for i in range(5):
        for topo_size in ['small', 'mid', 'large']:
            topo_files = 'topos/' + topo_size
            for topo_file in glob.glob(topo_files+'/*.graphml'):
                topo_name = os.path.basename(topo_file).strip('.graphml')
                req_file = topo_files + '/' + topo_name + '_ospf_reqs.py'
                with open(req_file, 'r') as fd:
                    exec (fd.read())
                for req_size in [2,4,8,16]:
                    for req_type in ['simple', 'order']:
                        if req_type == 'simple':
                            if req_size == 6:
                                print ("666666666666666")
                                reqs = eval('reqs_%s_%d' % (req_type, 8))
                                reqs = reqs[:6]
                                vals = eval('edges_cost_%s_%d' % (req_type, 8))
                            else:
                                reqs = eval('reqs_%s_%d' % (req_type, req_size))
                                vals = eval('edges_cost_%s_%d' % (req_type, req_size))
                        if req_type == 'order':
                            if req_size == 6:
                                print ("666666666666 order")
                                reqs = eval('reqs_%s_%d_2' % (req_type, 8))
                                reqs = reqs[:6]
                                vals = eval('edges_cost_%s_%d_2' % (req_type, 8))
                            else:
                                reqs = eval('reqs_%s_%d_2' % (req_type, req_size))
                                vals = eval('edges_cost_%s_%d_2' % (req_type, req_size))

                        for fixed in [0, 0.5]:
                            print ('%d,%s,%s,isis\n' % (req_size, req_type, topo_size))
                            topo = read_topology_zoo_netgraph(topo_file)

                            for node in topo.nodes():
                                topo.enable_ospf(node, 100)
                            # Initially all costs are empty
                            for src, dst in topo.edges():
                                topo.set_edge_ospf_cost(src, dst, VALUENOTSET)
                            # how many is fixed
                            fixed_edges = ospfRand.sample(vals, int(round(len(vals) * fixed)))
                            for src, dst, cost in fixed_edges:
                                print ("Fixing", src, dst, cost)
                                topo.set_edge_ospf_cost(src, dst, cost)
                            # Establish basic connectivity
                            conn = ConnectedSyn([], topo, full=True)
                            conn.synthesize()

                            t1 = timer()
                            print ("Syn CEGIS")
                            ospf = OSPFCEGIS(topo, gen_paths=100, random_obj=ospfRand)
                            for req in reqs:
                                ospf.add_req(req)
                            assert ospf.synthesize()
                            assert not ospf.removed_reqs

                            t2 = timer()
                            syn_time = t2-t1
                            print( "TOTAL SYN TIME:", syn_time)
                            if fixed == 1.0:
                                t1 = timer()
                                print( "Updating network graph, to assert full values")
                                ospf.update_network_graph()
                                for src, dst, cost in vals:
                                    new_cost = topo.get_edge_ospf_cost(src, dst)
                                    assert cost == new_cost, "Diff (%s, %s) old=%s new=%s" % (
                                        src, dst, cost, new_cost)
                                t2 = timer()
                                print ("Update Network graph TIME:", t2 - t1)
                            #     total_syn,req_size,req_type,topo_size,increment_type,protocol
                            if fixed == 0:
                                incre = 'false'
                            else:
                                incre = 'true'
                             #数据存入ospf_time.csv
                            f.write('%s,%d,%s,%s,%s,isis\n' % (str(syn_time), req_size, req_type, topo_size, incre))
                            # from tekton.gns3 import GNS3Topo
                            # ospf.update_network_graph()
                            # gns3 = GNS3Topo(topo)
                            # basename = os.path.basename(topo_file).strip('.graphml')
                            # out_name = "%s_%s_%s_%s" % (basename, fixed, req_type, reqsize)
                            # out_dir = 'out-configs/%s_%d' % (out_name, ospfRand.randint(0, 1000))
                            # print "Writing configs to:", out_dir
                            # gns3.write_configs(out_dir)
    f.close()


if __name__ == '__main__':
    os.chdir(r'D:\NEU\synet-plus-master')
    main()