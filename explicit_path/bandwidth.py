#!/usr/bin/env python
# -*- coding: utf-8 -*-
'''
求解带宽预留显示路径
Input:  topo,link默认bandwidth为1000,  policy:[[src,dst,100],[src1,dst1,500],.....]
Output: 求解src到dst满足带宽约束的显示路径
@Project ：SRv6CS 
@File ：bandwidth.py
@Date ：2022/7/19 15:02 
'''
import random
import time

import networkx as nx
import z3

# pol = [['a', 'd', 200], ['b', 'd', 1000]]
#
# g = nx.DiGraph()
# g.add_edge('a', 'b')
# g.add_edge('b', 'd')
# g.add_edge('a', 'c')
# g.add_edge('c', 'd')
#
# for ner in g['c'].items():
#     print(ner)


class BandWidth:
    def __init__(self, topo, policy):
        assert (isinstance(topo, nx.DiGraph))
        self.topo = topo
        self.init_policy = policy
        self.policy = {}
        # for list in policy:
        for list in policy:
            key = (list[0], list[1])
            self.policy[key] = list[2]
        self.edge_key_var = {}  #key： 四元组(topo.edge,policy.key) value: z3 var

        self.solver = z3.Solver()

    def creat_z3_var(self):
        for edge in self.topo.edges:
            for key in self.policy.keys():
                temTuple = (edge[0], edge[1], key[0], key[1])
                temStr = str(edge[0])+'_'+str(edge[1])+'_'+str(key[0])+'_'+str(key[1])
                temVar = z3.Bool(temStr)
                self.edge_key_var[temTuple] = temVar

    def path_link_con(self):
        for key in self.policy.keys():
            cons = []
            all_paths = nx.all_simple_paths(self.topo, key[0], key[1])
            paths_edges = []  # 所有路径链路list
            for path in all_paths:  # 获取路径链路list
                path_edges = []
                index = 0
                max_index = len(path)-1
                while index < max_index:
                    edge_tuple = (path[index], path[index+1])
                    path_edges.append(edge_tuple)
                    index = index + 1
                paths_edges.append(path_edges)
            for path_edges in paths_edges:
                con = []
                for edge in self.topo.edges:
                    if edge in path_edges:
                        tem_z3_var = self.edge_key_var[edge[0], edge[1], key[0], key[1]]
                        con.append(z3.Not(z3.And(tem_z3_var, True)))
                    else:
                        con.append(self.edge_key_var[edge[0], edge[1], key[0], key[1]])
                cons.append(z3.Or(con))
            self.solver.append(z3.And(cons) == False)

    def edge_bandwidth_con(self):
        for edge in self.topo.edges:
            # max_edge_bandwidth = self.topo.edges[edge]['bandwidth']  # 拓扑的边是否有该属性，待确认
            max_edge_bandwidth = 1000
            vars_sum = 0
            for key in self.policy.keys():
                tem_z3_var = self.edge_key_var[edge[0], edge[1], key[0], key[1]]
                pol_need = self.policy[key]
                assert isinstance(pol_need, int)
                vars_sum += z3.If(tem_z3_var == True, pol_need, 0)
            self.solver.add(vars_sum <= max_edge_bandwidth)

    def set_paths(self):
        assert self.solver.check()
        model = self.solver.model()
        new_paths = []
        # for list in self.init_policy:
        for list in self.init_policy.paths:
            start_node = list[0]
            end_node = list[1]
            tem_list = []
            cur_node = start_node
            tem_list.append(cur_node)
            while cur_node != end_node:
                for ner, value in self.topo[cur_node].items():
                    tem_tuple = (cur_node, ner, start_node, end_node)
                    if bool(model.get_interp(self.edge_key_var[tem_tuple])):
                        cur_node = ner
                        tem_list.append(cur_node)
                        break
            new_paths.append(tem_list)
        # print(new_paths)
        self.init_policy.paths = new_paths




# k = BandWidth(g, pol)
# k.creat_z3_var()
# k.path_link_con()
# k.edge_bandwidth_con()
# k.solver.check()
# ppp = k.solver.model()
# for i in k.edge_key_var.values():
#     print(ppp.get_interp(i))
#     print(bool(ppp.get_interp(i)))
#
# print(ppp)
# print(ppp.get_interp(k.edge_key_var[('c','d','a','d')]))
#
# k.set_paths()


def set_policy(graph, num):
    assert isinstance(graph, nx.DiGraph)
    policy = []
    err_pols = []
    while len(policy) < num:
        node1 = random.choice(list(graph.nodes))
        node2 = random.choice(list(graph.nodes))
        while node1 == node2:
            node2 = random.choice(list(graph.nodes))
        tem_pol = [node1, node2, 20]
        if (node1, node2) in err_pols:
            continue
        if not nx.has_path(graph, node1, node2):
            err_pol = (node1, node2)
            err_pols.append(err_pol)
            continue
        if tem_pol in policy:
            continue
        else:
            policy.append(tem_pol)
    return policy


def creat_random_graph(scale):
    graph = nx.gnm_random_graph(scale, int(scale*1.5), directed=True)
    while len(list(nx.weakly_connected_components(graph))) != 1:
        graph = nx.gnm_random_graph(scale, int(scale*1.5), directed=True)
    return graph


test_num = 1
result_dir = {}   # key:(int graph, int req) value；time (秒)  int graph [0: small, 1: medium, 2: lager]
is_first = True
while test_num <= 1:
    small = random.randint(10, 25)
    medium = random.randint(36, 64)
    lager = random.randint(65, 81)
    req_num = 4
    while req_num < 100:
        small_graph = creat_random_graph(small)
        medium_graph = creat_random_graph(medium)
        lager_graph = creat_random_graph(lager)
        graph_list = [small_graph, medium_graph, lager_graph]
        for index in [0, 1, 2]:
            policy = set_policy(graph_list[index], req_num)
            start_time = time.time()
            tem_bandwidth = BandWidth(graph_list[index], policy)
            tem_bandwidth.creat_z3_var()
            tem_bandwidth.path_link_con()
            tem_bandwidth.edge_bandwidth_con()
            tem_bandwidth.solver.check()
            end_time = time.time()
            # print(tem_bandwidth.solver.check())
            time_cost = end_time - start_time
            if is_first:
                result_dir[(index, req_num)] = time_cost
            else:
                result_dir[(index, req_num)] += time_cost
        req_num *= 2
    is_first = False
    test_num += 1

for key in result_dir.keys():
    if key[0] == 0:
        t1 = result_dir[key]
        print("small and " + str(key[1]) + "requirements 时间开销："+ str(result_dir[key]/(test_num-1)))
    if key[0] == 1:
        print("medium and " + str(key[1]) + "requirements 时间开销：" + str(result_dir[key] / (test_num - 1)))
    if key[0] == 2:
        print("lager and " + str(key[1]) + "requirements 时间开销：" + str(result_dir[key] / (test_num - 1)))
