#!/usr/bin/env python
# -*- coding: utf-8 -*-
'''
@Project ：AutoSRv6
@File ：waypoint.py
@Author ：Lucky
@Date ：2022/4/27 7:22
'''
# !/usr/bin/env python

# -*- coding:utf-8 -*-
import random
import time
from threading import Timer
import networkx as nx
#from read_files import *

"""
航路点路径，输入waypoint列表,输出对应的路径
"""

from z3 import *


class WayPoint:
    tunnel_list = [True for i in range(1, 100)]
    tunnel_id_list = [True for i in range(200)]

    def __init__(self, graph, waypoint_list):
        self.graph = graph
        self.source = waypoint_list[0]
        self.target = waypoint_list[1]
        self.nodeslist = waypoint_list[-1]
        # self.ip_pre = waypoint_list[3]
        self.nodes = graph.nodes
        self.edges = graph.edges
        self.node_in_edges = self.generate_node_inedges()
        self.node_out_edges = self.generate_node_outedges()
        self.solver = Optimize()
        self.x_edge = self.generate_x_edge()
        self.path = []
        # print(self.nodes)
        # print(self.edges)

    def get_a_tunnel_number(self):
        for i in range(1, 100):
            if WayPoint.tunnel_list[i]:
                WayPoint.tunnel_list[i] = False
                return i

    def get_a_tunnel_id_number(self):
        for i in range(100, 200):
            if WayPoint.tunnel_id_list[i]:
                WayPoint.tunnel_id_list[i] = False
                return i

    def get_a_pri_path_number(self):
        for i in range(100, 200):
            if WayPoint.tunnel_id_list[i]:
                WayPoint.tunnel_id_list[i] = False
                return i

    def generate_x_edge(self):
        x_edge = {}
        for edge in self.edges:
            x_edge[edge[0]] = {}
        for edge in self.edges:
            x_edge[edge[0]][edge[1]] = {}
        # print(x_edge)
        return x_edge

    def generate_node_inedges(self):
        node_in_edges = {}
        for node in self.nodes:
            edges = []
            for edge in self.edges:
                if edge[1] == node:
                    edges.append(edge)
            node_in_edges[node] = edges
        return node_in_edges

    def generate_node_outedges(self):
        node_out_edges = {}
        for node in self.nodes:
            edges = []
            for edge in self.edges:
                if edge[0] == node:
                    edges.append(edge)
            node_out_edges[node] = edges
        return node_out_edges

    def get_node_inedge(self, node, x):
        degree = 0
        for edge in self.node_in_edges[node]:
            degree += x[edge]
        return degree

    def get_node_outedge(self, node, x):
        degree = 0
        for edge in self.node_out_edges[node]:
            degree += x[edge]
        return degree

    def find_path(self):
        path = []
        temp_node = self.source
        path.append(temp_node)
        while True:
            if temp_node == self.target:
                break
            for i in self.x_edge.keys():
                if i == temp_node:
                    for j in self.x_edge[i]:
                        if self.x_edge[i][j]['value'] == 1:
                            temp_node = j
                            path.append(temp_node)
        self.path = path

    def shorstest_path_solver(self):
        x = {}  # create varible
        o = {}
        for node in self.nodes:
            # if node == self.target:
            #     continue
            for edge in self.node_out_edges[node]:
                # print(edge)
                x[edge] = Int(edge[0] + ' ' + edge[1])
        for node in self.nodes:
            o[node] = Int('o_' + node)
        for i in o:
            self.solver.add(o[i] > 0, o[i] <= len(self.nodes))
        for i in x:
            self.solver.add(Or(x[i] == 0, x[i] == 1))
        edge_sum = sum(x[edge] for edge in self.edges)

        # objective
        self.solver.minimize(edge_sum)

        # add constraint 1
        self.solver.add(self.get_node_outedge(self.source, x) == 1)
        self.solver.add(self.get_node_inedge(self.source, x) == 0)
        self.solver.add(self.get_node_inedge(self.target, x) == 1)
        self.solver.add(self.get_node_outedge(self.target, x) == 0)

        # add constrain 2
        for node in self.nodes:
            if node == self.source or node == self.target:
                continue
            if node not in self.nodeslist:
                if len(self.node_in_edges[node]) == 0 or len(self.node_out_edges[node]) == 0:
                    continue

            self.solver.add(self.get_node_inedge(node, x) == self.get_node_outedge(node, x))
            if node in self.nodeslist:
                self.solver.add(self.get_node_outedge(node, x) == 1)
            else:
                self.solver.add(self.get_node_outedge(node, x) <= 1)

        # add constraint 3
        self.solver.add(o[self.source] == 1)
        self.solver.add(o[self.target] == len(self.nodes))
        for node in self.nodes:
            for edge in self.node_out_edges[node]:
                self.solver.add(o[edge[0]] - o[edge[1]] + x[edge] * len(self.nodes) <= len(self.nodes) - 1)

        # add constraint 4
        for i in range(len(self.nodeslist) - 1):
            self.solver.add(o[self.nodeslist[i]] < o[self.nodeslist[i + 1]])

        # check()
        if self.solver.check() == z3.sat:
            model = self.solver.model()
            for k in x.keys():
                self.x_edge[k[0]][k[1]]['value'] = model[x[k]]
            self.find_path()
        else:
            print('from ' + self.source + ' to ' + self.target + ' pass ' + 'nodeslist' + ' no_path---un-solved')

    def time_limit(interval):
        def wraps(func):
            def time_out():
                print('timeout------over 600s')
                os._exit(0)

            def deco(*args, **kwargs):
                timer = Timer(interval, time_out)
                timer.start()
                res = func(*args, **kwargs)
                timer.cancel()
                return res

            return deco

        return wraps

    # @time_limit(600)
    def explicit_path(self):
        # 找到显示路径的下一跳 ip address
        flag = True
        for i in self.nodeslist:
            if len(self.node_in_edges[i]) == 0 or len(self.node_out_edges[i]) == 0:
                flag = False
                print('there is no in_edge or out_edge to connect node ' + i)
        if flag:
            start_time = time.process_time()
            self.shorstest_path_solver()
            end_time = time.process_time()
            print("Finding the path takes time  " + str(format((end_time - start_time), '.4f')))
            path = self.path
            if len(path) > 0:
                print(path)
        return path


#
# import read_topo
#
# topo = read_topo.Topo('../topo/topology.json').getFromJson()
# print(topo)
#
# waypoint = WayPoint(topo,['A','H',['C','D']])
# waypoint.explicit_path()

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
        print("small and " + str(key[1]) + "requirements 时间开销："+ str(result_dir[key]/(test_num-1)))
    if key[0] == 1:
        print("medium and " + str(key[1]) + "requirements 时间开销：" + str(result_dir[key] / (test_num - 1)))
    if key[0] == 2:
        print("lager and " + str(key[1]) + "requirements 时间开销：" + str(result_dir[key] / (test_num - 1)))
