#!/usr/bin/env python
# -*- coding: utf-8 -*-
'''
@Project ：AutoSRv6 
@File ：test2.py
@Author ：Lucky
@Date ：2022/7/25 15:25 
'''
from read_policy import *
# with open(r'./policy/new_test.txt', 'r') as file:
#     user_policy = file.read()

#balance = bandwidth_info(user_policy)

# for node in element['nodes']:
#     # print(node)
#     # 给节点添加接口信息{G1{cost:1},G2{cost}}
#     for edge in element['edges']:
#         if edge['node_1'] == node:
#             self.topo.nodes[node]['ints'] = {}
#             self.topo.nodes[node]['ints'][edge['int_1']] = {}
#             self.topo.nodes[node]['ints'][edge['int_1']]['cost'] = 1
#         elif edge['node_2'] == node:
#             self.topo.nodes[node]['ints'] = {}
#             self.topo.nodes[node]['ints'][edge['int_2']] = {}
#             self.topo.nodes[node]['ints'][edge['int_2']]['cost'] = 1
#
import networkx as nx
def creat_random_graph(scale):
    graph = nx.gnm_random_graph(scale, int(scale*1.5), directed=True)
    while len(list(nx.weakly_connected_components(graph))) != 1:
        graph = nx.gnm_random_graph(scale, int(scale*1.5), directed=True)
    return graph

gg =  creat_random_graph(5)
print(gg)