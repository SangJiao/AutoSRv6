#!/usr/bin/env python
# -*- coding: utf-8 -*-
'''
@Project ：AutoSRv6
@File ：wp.py
@Author ：Lucky
@Date ：2023/4/29 20:29
'''
import itertools
import json
import random
import time
from threading import Timer
import networkx as nx
import numpy
import copy
from z3 import *
import matplotlib.pyplot as plt
from read_topo import Topo


class WP():
    tunnel_list = [True for i in range(1, 100)]
    tunnel_id_list = [True for i in range(200)]

    def __init__(self,graph,waypoint_list,bandwidth_list=None):
        self.graph = graph
        self.source = waypoint_list[0]
        self.target = waypoint_list[1]
        self.nodeslist = waypoint_list[2]
#        self.ip_pre = waypoint_list[3]
        self.bandwidth_list = bandwidth_list
        self.nodes = graph.nodes
        self.edges = graph.edges
        self.node_in_edges = self.generate_node_inedges()
        self.node_out_edges = self.generate_node_outedges()
        self.solver = Optimize()
        self.x_edge = self.generate_x_edge()
        self.path = []
        # print(self.nodes)
        # print(self.edges)
    def generate_x_edge(self):
        x_edge = {}
        for edge in self.edges:
            x_edge[edge[0]]= {}
        for edge in self.edges:
            x_edge[edge[0]][edge[1]] = {}
       # print(x_edge)
        return x_edge

    def generate_node_inedges(self):
        node_in_edges ={}
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

    def get_node_inedge(self,node,x):
        degree = 0
        for edge in self.node_in_edges[node]:
            degree += x[edge]
        return degree

    def get_node_outedge(self,node,x):
        degree = 0
        for edge in self.node_out_edges[node]:
            degree += x[edge]
        return degree

    def find_path(self):
        print('src = '+ self.source +' ,dst = '+self.target +' waypoint = '+str(self.nodeslist))
        print('solving the path......')

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
        print('from '+ self.source + ' to '+self.target+' though '+str(self.nodeslist)+' waypoint path is' )
        print(path)
        self.path = path

    def shorstest_path_solver(self):
        x = {}                      #create varible
        o = {}
        for node in self.nodes:
            # if node == self.target:
            #     continue
            for edge in self.node_out_edges[node]:
                #print(edge)
                x[edge] = Int(edge[0]+ ' ' +edge[1])
        for node in self.nodes:
            o[node] = Int('o_'+node)
        for i in o:
            self.solver.add(o[i] > 0 ,o[i] <= len(self.nodes))
        for i in x:
            self.solver.add(Or(x[i]==0,x[i]==1))
        edge_sum = sum(x[edge] for edge in self.edges)

        #objective
        self.solver.minimize(edge_sum)

        #add constraint 1
        self.solver.add(self.get_node_outedge(self.source,x) == 1)
        self.solver.add(self.get_node_inedge(self.source,x) == 0)
        self.solver.add(self.get_node_inedge(self.target,x) == 1)
        self.solver.add(self.get_node_outedge(self.target,x) == 0)

        #add constrain 2
        for node in self.nodes:
            if node == self.source or node == self.target:
                continue
            if node not in self.nodeslist:
                if len(self.node_in_edges[node]) == 0 or len(self.node_out_edges[node]) == 0:
                    continue

            self.solver.add(self.get_node_inedge(node,x) == self.get_node_outedge(node,x))
            if node in self.nodeslist:
                self.solver.add(self.get_node_outedge(node,x) == 1)
            else:
                self.solver.add(self.get_node_outedge(node,x) <= 1)

        #add constraint 3
        self.solver.add(o[self.source] == 1)
        self.solver.add(o[self.target] == len(self.nodes))
        for node in self.nodes:
            for edge in self.node_out_edges[node]:
                self.solver.add(o[edge[0]]-o[edge[1]]+x[edge]*len(self.nodes) <= len(self.nodes) - 1 )

        #add constraint 4
        for i in range(len(self.nodeslist)-1):
            self.solver.add(o[self.nodeslist[i]] < o[self.nodeslist[i+1]])

        #check()
        if self.solver.check() == z3.sat:
            model = self.solver.model()
            for k in x.keys():
                self.x_edge[k[0]][k[1]]['value'] = model[x[k]]
            self.find_path()

        else:
            print('from '+self.source+' to '+ self.target + ' pass '+ 'nodeslist' +' no_path---un-solved')


G = nx.Graph()        # 无多重边有向图
G.add_nodes_from(['A', 'B', 'C', 'D', 'E', 'F', 'G', 'H'])  # 添加多个节点
G.add_edges_from([['A', 'B'], ['A', 'E'], ['E', 'B'],['C', 'B'],['F', 'B'],['C', 'E'],['C', 'F'],['C', 'D'],['E', 'F'],['G', 'F'],['D', 'H'],['D', 'G'],['G', 'H']])  # 添加多条边
a = 10
b = 1
for e in G.edges():
   # print(e)

    #print('(2001:DB8:'+str(a)+'::'+str(b) +', 0, False)')
    a += 10
    b += 1
    G[e[0]][e[1]]['weight'] = random.randint(1,4)
  #  G.edges[i]['weight']=weights[edge]

# print(G.nodes)
# print(G.edges)
# nx.draw(G)
# plt.show()

wp = WP(G,['A','H',['C','E']])
# print('src = '+ 'A' +' ,dst = '+'H' +' waypoint = '+'C')
# print('solving the path......')
wp.shorstest_path_solver()