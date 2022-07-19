#!/usr/bin/env python
# -*- coding: utf-8 -*-
'''
@Project ：AutoSRv6
@File ：srv6_mapping.py
@Date ：2022/4/7 15:08
输入计算的路径和topo，输出Segment List
'''
import operator
import random

import networkx as nx


class PathEncoding:
    def __init__(self, graph, pathlist,random_obj=None):
        self.graph = graph
        self.node = graph.nodes
        self.edges = graph.edges
        self.random_gen = random_obj or random.Random()
        self.random_gen = random_obj or random.Random()
        self.path_list = pathlist
        self.path_list_length = len(pathlist)
        self.left = 0
        self.right = 0
        self.segment_list = []
        self.sub_path = []
        self.res_path = {}


    def is_dijkstra_path(self, path, source, target):
        """
        function：判断给定的路径与最小权值路径的比较结果
        select the shortest paths based on dijkstra algorithm
        return：相同返回true
        """
        dijkastra_path = nx.shortest_path(self.graph, source, target, 'weight')
        if operator.eq(path, dijkastra_path):
            return True
        else:
            return False


    def srv6_mapping(self, path):
        """
        function：将单条严格显示路径映射成SRv6 Segment List
        return：SRv6 segment_list
        """
        if len(path) < 2:
            print('输入路径不正确')
            return []
        self.left = len(path)-2
        self.right = len(path)-1
        self.segment_list.append(path[-1])
        while self.left >= 0:
            sub_path = [path[self.right]]
            dif = self.right - self.left
            if dif == 1:
                sub_path.insert(0, path[self.left])

            while self.left >= 0 and self.is_dijkstra_path(sub_path, path[self.left], path[self.right]):
                self.left -= 1
                sub_path.insert(0, path[self.left])

            if (self.right - self.left) > 1:
                if self.left > 0:
                    self.segment_list.insert(0, path[self.left + 1])
                self.right = self.left + 1
                continue
            else:
                self.segment_list.insert(0, [path[self.left], path[self.right]])
                if self.segment_list[0][-1] == self.segment_list[1]:
                    self.segment_list.remove(self.segment_list[1])
                self.left -= 1
                self.right -= 1
                continue
        return self.segment_list


    def generate_res_path(self):
        """
        function：将全部的严格显示路径映射成SRv6 Segment List
        return：SRv6 segment_list dict res_path
        """
        for i in range(len(self.path_list)):
            self.segment_list = []
            print('path')
            print(self.path_list[i])
            self.res_path[i] = self.srv6_mapping(self.path_list[i])
            print('item')
            print(self.res_path[i])
        return self.res_path


    def random_walk_path(self, source, target):
        """
        在source节点和target节点之间生成随机路径
        若不存在可达路径，返回None
        """
        G = self.graph
        visited = [source]
        while True:
            children = G[visited[-1]]
            none_visited_children = []
            for child in children:
                if child not in visited:
                    none_visited_children.append(child)
            # Check if we hit a dead end
            if not none_visited_children:
                # Just abort at dead end
                return None
            # Select one random next hop
            next_node = self.random_gen.choice(none_visited_children)
            visited.append(next_node)
            if next_node == target:
                # We reached our destination
                return visited


    def random_dijkstra_path(self, source, target, max_weight=1000000):
        """
        在source节点和target节点之间找到基于dijkastra算法计算出的路径
        首先给图中的网络边生成随机权值
        基于该算法输出source和targrt之间的路径
        """
        G = nx.DiGraph()
        for src, dst in self.graph.edges():
            G.add_edge(src, dst)
        for src, dst in G.edges():
            w = self.random_gen.randint(1, max_weight)
            G[src][dst]['test-weight'] = w
        return nx.shortest_path(G, source, target, 'test-weight')

    def get_path_key(self,src, dst):
        """
        用于路径排序字典
        """
        return src, dst


    def generate_random_paths(self, source, target, dijsktra_prob, random_obj):
        """
        生成不重复的随机路径集
        """
        generated_paths = []
        counter = 0
        while True:
            # First give a priority to the counter examples (if any)
            key = self.get_path_key(source, target)
            if self.graph.get(key, None):
                p = self.graph[key].pop()
            else:
                if random_obj.random() < dijsktra_prob:
                    p = self.random_dijkstra_path(source, target)
                else:
                    p = self.random_walk_path(source, target)
            if not p or p in generated_paths:
                # Path already generated or random walk hit a dead end
                # Try again
                counter += 1
                if counter > 10:
                    counter = 0
                    yield None
                continue
            else:
                counter = 0
                generated_paths.append(p)
                yield p


    # def generate_topo(self,G):
    #     nx.draw_networkx(G, with_labels=True)
    #     pos = nx.spring_layout(G)
    #     weights = nx.get_edge_attributes(G, "weight")
    #     print(weights)
    #     # nx.draw_networkx_edge_labels(G,pos,edge_labels= weights)
    #     plt.show()
    #     g = nx.gnm_random_graph(8,12,directed=True)
    #
    #
    #     for u,v in g.edges:
    #
    #         random_weight = random.randint(1, 10)
    #         g.add_edge(u, v, weight=random_weight)
    #         g.add_edge(v, u, weight=random_weight)
    #         print(u,v,random_weight)
    #
    #     weights = nx.get_edge_attributes(g, "weight")
    #     print(len(weights))
    #     print(weights)
    #     nx.draw_networkx(g, with_labels=True)
    #     pos = nx.spring_layout(g)
    #     nx.draw_networkx_edge_labels(g,pos,edge_labels= weights)
    #     plt.show()
