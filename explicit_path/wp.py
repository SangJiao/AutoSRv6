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
            print('from '+self.source+' to '+ self.target + ' pass '+ self.nodeslist[0] +' no_path')


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

g = nx.read_graphml('../real_topo/Aarnet.graphml')

# 随机选择三个不同的节点
nodes = list(g.nodes())  # 获取所有节点列表
selected_nodes = random.sample(nodes, k=3)
src1 = selected_nodes[0]
dst1 = selected_nodes[1]
waypoint1 = selected_nodes[2]

# 输出节点的名称
src_label = g.nodes[src1]['label']
dst_label = g.nodes[dst1]['label']
waypoint_label = g.nodes[waypoint1]['label']
g = g.to_undirected()
print('src = ' + src_label + ', dst = ' + dst_label + ', waypoint = ' + waypoint_label)
print('solving the path......')

# 使用 WP 类来解决路径
nx.draw(g, with_labels=True)

# 显示图形
plt.show()
wp1 = WP(g, [src1, dst1, waypoint1])
wp1.shorstest_path_solver()
#node_names = [g.nodes[node]['label'] for node in selected_nodes]
#print("选择的节点：", node_names)


# 读取图形数据
g = nx.read_graphml('../real_topo/Aarnet.graphml')

# 随机选择三个不同的节点
nodes = list(g.nodes())  # 获取所有节点列表
selected_nodes = random.sample(nodes, k=3)
src1 = selected_nodes[0]
dst1 = selected_nodes[1]
waypoint1 = selected_nodes[2]
src_label = g.nodes[src1]['label']
dst_label = g.nodes[dst1]['label']
waypoint_label = g.nodes[waypoint1]['label']

print('src = ' + src_label + ', dst = ' + dst_label + ', waypoint = ' + waypoint_label)
print('Solving the path......')


# 绘制图形
nx.draw(g, with_labels=True)

# 显示图形
plt.show()


def find_path_with_waypoint(graph, src1, dst1, waypoint):
    # 找到源节点到 waypoint 节点的最短路径
    src_to_waypoint_path = nx.shortest_path(graph, source=src1, target=waypoint)

    # 找到 waypoint 节点到目标节点的最短路径
    waypoint_to_dst_path = nx.shortest_path(graph, source=waypoint, target=dst1)

    # 组合两条路径
    path = src_to_waypoint_path + waypoint_to_dst_path[1:]  # [1:] 去除重复的 waypoint 节点

    return path

# 读取图形文件
graph = nx.read_graphml('../real_topo/Aarnet.graphml')

# 调用函数查找路径
nodes = list(g.nodes())  # 获取所有节点列表
selected_nodes = random.sample(nodes, k=3)
src1 = selected_nodes[0]
dst1 = selected_nodes[1]
waypoint1 = selected_nodes[2]
src_label = g.nodes[src1]['label']
dst_label = g.nodes[dst1]['label']
waypoint_label = g.nodes[waypoint1]['label']


path = find_path_with_waypoint(graph, src1, dst1, waypoint1)
print('src1 = ' + src_label + ', dst = ' + dst_label + ', waypoint = ' + waypoint_label)
print('Solving the path......')
path_labels = [g.nodes[node]['label'] for node in path]
print(' -> '.join(path_labels))  # 将路径节点标签用箭头连接并打印