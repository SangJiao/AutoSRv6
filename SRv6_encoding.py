#!/usr/bin/env python
# -*- coding: utf-8 -*-
'''
@Project ：AutoSRv6
@File ：SRv6_encoding.py
@Date ：2022/4/7 15:08
输入计算的路径和topo，输出Segment List
'''
import operator
import random
import time

import networkx as nx
import matplotlib as mpl
import matplotlib.pyplot as plt
#!/usr/bin/env python

import operator
import random

import networkx as nx
import matplotlib as mpl
import matplotlib.pyplot as plt
import time


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


    def srv6_mapping(self):
        """
        function：将单条严格显示路径映射成SRv6 Segment List
        return：SRv6 segment_list
        """
        path = self.path_list
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
        # print(self.segment_list)
        return self.segment_list


    def generate_res_path(self):
        """
        function：将全部的严格显示路径映射成SRv6 Segment List
        return：SRv6 segment_list dict res_path
        """
        for i in range(len(self.path_list)):
            self.segment_list = []
            #print('path')
            #print(self.path_list[i])
            self.res_path[i] = self.srv6_mapping(self.path_list[i])
            #print('item')
            print(self.res_path[i])
        print(self.res_path)
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


    def generate_topo(self,G):
        nx.draw_networkx(G, with_labels=True)
        pos = nx.spring_layout(G)
        weights = nx.get_edge_attributes(G, "weight")
        print(weights)
        # nx.draw_networkx_edge_labels(G,pos,edge_labels= weights)
        plt.show()

def creat_random_graph(scale):
    graph = nx.gnm_random_graph(scale, int(scale*1.5), directed=True)
    while len(list(nx.weakly_connected_components(graph))) != 1:
        graph = nx.gnm_random_graph(scale, int(scale*1.5), directed=True)
    return graph

def creat_grid_graph(scale):
    graph = nx.DiGraph()
    for node_stage in range(scale ** 2):
        graph.add_node(node_stage)
    for row_stage in range(scale):
        for col_stage in range(scale - 1):
            graph.add_edge(row_stage * scale + col_stage, row_stage * scale + col_stage + 1)
            graph.add_edge(row_stage * scale + col_stage + 1, row_stage * scale + col_stage)
    for col_stage in range(scale):
        for row_stage in range(scale - 1):
            graph.add_edge(row_stage * scale + col_stage, (row_stage + 1) * scale + col_stage)
            graph.add_edge((row_stage + 1) * scale + col_stage, row_stage * scale + col_stage)
    return graph


def grid_longest_path(scale):
    col_count = 0
    ans_path = []
    for row in range(scale):
        if col_count == -1:
            col_count = 0
        elif col_count == scale:
            col_count = scale - 1
        while scale > col_count >= 0:
            ans_path.append(row * scale + col_count)
            if row % 2 == 0:
                col_count += 1
            else:
                col_count -= 1

    return ans_path


node_sum_list = [5,7,8,10]
for node_sum in node_sum_list:
    # g = creat_random_graph(node_sum)

    # node_sum = int(input())
    # g = creat_grid_graph(node_sum)

    g = nx.read_graphml('real_topo/VtlWavenet2008.graphml')
   # print(len(g.nodes))

    # nx.draw_networkx(g)
    # pos = nx.spring_layout(g)
    # nx.draw_networkx_edge_labels(g,pos)
    # plt.show()
    SLD_total = 0
    SLD_max = 0
    SLD_mapping_total = 0
    SLD_mapping_max = 0
    total_time = 0

    test_times = 200


    # for i in range(test_times):
    #     for u,v in g.edges:
    #
    #         random_weight = random.randint(2, 10)
    #         g.add_edge(u, v, weight=random_weight)
    #         g.add_edge(v, u, weight=random_weight)
    #         #print(u,v,random_weight)
    #
    #         weights = nx.get_edge_attributes(g, "weight")
    #         #print(len(weights))
    #         #print(weights)
    #     node_list = [node for node in g.nodes]
    #     node_sample = random.sample(node_list, 2)  # random
    #     # node_sample = random.sample(range(node_sum ** 2), 2)  # grid
    #
    #     all_path_list = nx.all_simple_paths(g,node_sample[0], node_sample[1])
    #
    #     max_length = 0
    #     longest_path =None
    #     path_sum = 0
    #     for path in all_path_list:
    #         path_length = len(path)
    #         path_sum += 1
    #         # print(path_sum)
    #         if path_length > max_length:
    #             longest_path = path
    #             max_length = path_length
    #         # if path_sum > 500:
    #         #     break
    #     # tic3 = time.perf_counter()
    #     # print(tic3 - tic2)
    #     # print(longest_path)
    #
    #     # max_length = node_sum ** 2
    #     # longest_path = grid_longest_path(node_sum)
    #
    #     SLD_total += max_length
    #     SLD_max = max(SLD_max, max_length)
    #     for stage in range(max_length-1):
    #         g.edges[longest_path[stage],longest_path[stage+1]]['weight'] = random.randint(2, 20)
    #     start_tic = time.perf_counter()
    #     result = PathEncoding(g, longest_path).srv6_mapping()
    #     end_tic = time.perf_counter()
    #     SLD_mapping_total += len(result)
    #     SLD_mapping_max = max(SLD_mapping_max, len(result))
    #     total_time += (end_tic - start_tic)

    #print(node_sum,':', SLD_max,  SLD_total/test_times,  SLD_mapping_total/test_times,   total_time/test_times)
        # nx.draw_networkx(g, with_labels=True)
        # pos = nx.spring_layout(g)
        # nx.draw_networkx_edge_labels(g,pos,edge_labels= weights)
        # plt.show()

desc_file = open('output_networkx.txt', 'w', encoding='utf-8')
print('node_sum'+'  SLD_max  '+ 'SLD_average'+ '  SLD_mapping_average'+'  compression')
print("networkx topology experimental results")
for node_sum in range(10,201,5):
    g = creat_random_graph(node_sum)

    # node_sum = int(input())
    # g = creat_grid_graph(node_sum)

    # g = nx.read_graphml('real_topo/Syringa_73.graphml')
    # print(len(g.nodes))

    # nx.draw_networkx(g)
    # pos = nx.spring_layout(g)
    # nx.draw_networkx_edge_labels(g,pos)
    # plt.show()
    SLD_total = 0
    SLD_max = 0
    SLD_mapping_total = 0
    SLD_mapping_max = 0
    total_time = 0
    total_compression = 0

    test_times = 1000
    for i in range(test_times):
        for u,v in g.edges:

            random_weight = random.randint(2, 10)
            g.add_edge(u, v, weight=random_weight)
            g.add_edge(v, u, weight=random_weight)
            #print(u,v,random_weight)

            weights = nx.get_edge_attributes(g, "weight")
            #print(len(weights))
            #print(weights)
        node_list = [node for node in g.nodes]
        node_sample = random.sample(node_list, 2)  # random
        # node_sample = random.sample(range(node_sum ** 2), 2)  # grid

        shortest_path = nx.shortest_path(g, node_sample[0], node_sample[1])
        shortest_length = len(shortest_path)

        SLD_total += shortest_length
        SLD_max = max(SLD_max, shortest_length)
        for stage in range(shortest_length-1):
            g.edges[shortest_path[stage],shortest_path[stage+1]]['weight'] = random.randint(2, 20)
        start_tic = time.perf_counter()
        result = PathEncoding(g, shortest_path).srv6_mapping()
        end_tic = time.perf_counter()
        SLD_mapping_total += len(result)
        SLD_mapping_max = max(SLD_mapping_max, len(result))
        total_time += (end_tic - start_tic)
        total_compression += len(result)/shortest_length
    ans_str = map(str, [node_sum,SLD_total/test_times, SLD_max, SLD_mapping_total/test_times, SLD_mapping_max, total_time/test_times, total_compression/test_times])
    print(node_sum,  SLD_max,  SLD_total/test_times,  SLD_mapping_total/test_times, total_compression/test_times)
    desc_file.write(' '.join(ans_str))
    desc_file.flush()
    # print(node_sum,SLD_total/test_times, SLD_max, SLD_mapping_total/test_times, SLD_mapping_max, total_time/test_times)
        # nx.draw_networkx(g, with_labels=True)
        # pos = nx.spring_layout(g)
        # nx.draw_networkx_edge_labels(g,pos,edge_labels= weights)
        # plt.show()

print("grid")


desc_file = open('output_grid.txt', 'w', encoding='utf-8')
for node_sum in range(3,15):
    # g = creat_random_graph(node_sum)

    # node_sum = int(input())
    g = creat_grid_graph(node_sum)

    # g = nx.read_graphml('real_topo/Syringa_73.graphml')
    # print(len(g.nodes))

    # nx.draw_networkx(g)
    # pos = nx.spring_layout(g)
    # nx.draw_networkx_edge_labels(g,pos)
    # plt.show()
    SLD_total = 0
    SLD_max = 0
    SLD_mapping_total = 0
    SLD_mapping_max = 0
    total_time = 0
    total_compression = 0

    test_times = 1000
    for i in range(test_times):
        for u,v in g.edges:

            random_weight = random.randint(2, 10)
            g.add_edge(u, v, weight=random_weight)
            g.add_edge(v, u, weight=random_weight)
            #print(u,v,random_weight)

            weights = nx.get_edge_attributes(g, "weight")
            #print(len(weights))
            #print(weights)
        node_list = [node for node in g.nodes]
        node_sample = random.sample(node_list, 2)  # random
        # node_sample = random.sample(range(node_sum ** 2), 2)  # grid

        shortest_path = nx.shortest_path(g, node_sample[0], node_sample[1])
        shortest_length = len(shortest_path)

        SLD_total += shortest_length
        SLD_max = max(SLD_max, shortest_length)
        for stage in range(shortest_length-1):
            g.edges[shortest_path[stage],shortest_path[stage+1]]['weight'] = random.randint(2, 20)
        start_tic = time.perf_counter()
        result = PathEncoding(g, shortest_path).srv6_mapping()
        end_tic = time.perf_counter()
        SLD_mapping_total += len(result)
        SLD_mapping_max = max(SLD_mapping_max, len(result))
        total_time += (end_tic - start_tic)
        total_compression += len(result) / shortest_length
    ans_str = map(str, [node_sum**2,SLD_total/test_times, SLD_max, SLD_mapping_total/test_times, SLD_mapping_max, total_time/test_times, total_compression/test_times])
    print(node_sum**2,SLD_total/test_times, SLD_max, SLD_mapping_total/test_times, SLD_mapping_max, total_time/test_times, total_compression/test_times)
    desc_file.write(' '.join(ans_str))
    desc_file.flush()
    nx.draw_networkx(g, with_labels=True)
    pos = nx.spring_layout(g)
    nx.draw_networkx_edge_labels(g,pos,edge_labels= weights)
    plt.show()






# class PathEncoding:
#     def __init__(self, graph, pathlist, random_obj=None):
#         self.graph = graph
#         self.node = graph.nodes
#         self.edges = graph.edges
#         self.random_gen = random_obj or random.Random()
#         self.random_gen = random_obj or random.Random()
#         self.path_list = pathlist
#         self.path_list_length = len(pathlist)
#         self.left = 0
#         self.right = 0
#         self.segment_list = []
#         self.sub_path = []
#         self.res_path = {}
#
#     def is_dijkstra_path(self, path, source, target):
#         """
#         function：判断给定的路径与最小权值路径的比较结果
#         select the shortest paths based on dijkstra algorithm
#         return：相同返回true
#         """
#         dijkastra_path = nx.shortest_path(self.graph, source, target, 'weight')
#         if operator.eq(path, dijkastra_path):
#             return True
#         else:
#             return False
#
#     def srv6_mapping(self):
#         """
#         function：将单条严格显示路径映射成SRv6 Segment List
#         return：SRv6 segment_list
#         """
#         path = self.path_list
#         if len(path) < 2:
#             print('输入路径不正确')
#             return []
#         self.left = len(path) - 2
#         self.right = len(path) - 1
#         self.segment_list.append(path[-1])
#         while self.left >= 0:
#             sub_path = [path[self.right]]
#             dif = self.right - self.left
#             if dif == 1:
#                 sub_path.insert(0, path[self.left])
#
#             while self.left >= 0 and self.is_dijkstra_path(sub_path, path[self.left], path[self.right]):
#                 self.left -= 1
#                 sub_path.insert(0, path[self.left])
#
#             if (self.right - self.left) > 1:
#                 if self.left > 0:
#                     self.segment_list.insert(0, path[self.left + 1])
#                 self.right = self.left + 1
#                 continue
#             else:
#                 self.segment_list.insert(0, [path[self.left], path[self.right]])
#                 if self.segment_list[0][-1] == self.segment_list[1]:
#                     self.segment_list.remove(self.segment_list[1])
#                 self.left -= 1
#                 self.right -= 1
#                 continue
#         sl = self.segment_list
#         nl = []
#         left = 0
#         right = len(sl) - 1
#        # print('right_index:   ' + str(right))
#        # print(self.graph.edges)
#        # print(('F','H') in self.graph.edges)
#         for i in range(left, right, 1):
#             print('left:' + str(left))
#             if (left < right):
#                 if (sl[left], sl[left + 1]) in self.graph.edges:
#                     nl.append([sl[left], sl[left + 1]])
#                     if left < right - 2:
#                         left = left + 2
#                 else:
#                     nl.append(sl[left])
#                     left = left + 1
#             else:
#                 if(left == right):
#                     nl.append(sl[right])
#        # print(nl)
#         return self.segment_list
#
#     def generate_res_path(self):
#         """
#         function：将全部的严格显示路径映射成SRv6 Segment List
#         return：SRv6 segment_list dict res_path
#         """
#         for i in range(len(self.path_list)):
#             self.segment_list = []
#             # print('path')
#             # print(self.path_list[i])
#             self.res_path[i] = self.srv6_mapping(self.path_list[i])
#             # print('item')
#             print(self.res_path[i])
#         print(self.res_path)
#         return self.res_path
#
#     def random_walk_path(self, source, target):
#         """
#         在source节点和target节点之间生成随机路径
#         若不存在可达路径，返回None
#         """
#         G = self.graph
#         visited = [source]
#         while True:
#             children = G[visited[-1]]
#             none_visited_children = []
#             for child in children:
#                 if child not in visited:
#                     none_visited_children.append(child)
#             # Check if we hit a dead end
#             if not none_visited_children:
#                 # Just abort at dead end
#                 return None
#             # Select one random next hop
#             next_node = self.random_gen.choice(none_visited_children)
#             visited.append(next_node)
#             if next_node == target:
#                 # We reached our destination
#                 return visited
#
#     def random_dijkstra_path(self, source, target, max_weight=1000000):
#         """
#         在source节点和target节点之间找到基于dijkastra算法计算出的路径
#         首先给图中的网络边生成随机权值
#         基于该算法输出source和targrt之间的路径
#         """
#         G = nx.DiGraph()
#         for src, dst in self.graph.edges():
#             G.add_edge(src, dst)
#         for src, dst in G.edges():
#             w = self.random_gen.randint(1, max_weight)
#             G[src][dst]['test-weight'] = w
#         return nx.shortest_path(G, source, target, 'test-weight')
#
#     def get_path_key(self, src, dst):
#         """
#         用于路径排序字典
#         """
#         return src, dst
#
#     def generate_random_paths(self, source, target, dijsktra_prob, random_obj):
#         """
#         生成不重复的随机路径集
#         """
#         generated_paths = []
#         counter = 0
#         while True:
#             # First give a priority to the counter examples (if any)
#             key = self.get_path_key(source, target)
#             if self.graph.get(key, None):
#                 p = self.graph[key].pop()
#             else:
#                 if random_obj.random() < dijsktra_prob:
#                     p = self.random_dijkstra_path(source, target)
#                 else:
#                     p = self.random_walk_path(source, target)
#             if not p or p in generated_paths:
#                 # Path already generated or random walk hit a dead end
#                 # Try again
#                 counter += 1
#                 if counter > 10:
#                     counter = 0
#                     yield None
#                 continue
#             else:
#                 counter = 0
#                 generated_paths.append(p)
#                 yield p
#
#     def generate_topo(self, G):
#         nx.draw_networkx(G, with_labels=True)
#         pos = nx.spring_layout(G)
#         weights = nx.get_edge_attributes(G, "weight")
#         print(weights)
#         # nx.draw_networkx_edge_labels(G,pos,edge_labels= weights)
#         plt.show()
#
#
# # def creat_random_graph(scale):
# #     graph = nx.gnm_random_graph(scale, int(scale*1.5), directed=True)
# #     while len(list(nx.weakly_connected_components(graph))) != 1:
# #         graph = nx.gnm_random_graph(scale, int(scale*1.5), directed=True)
# #     return graph
# # g = creat_random_graph(25)
# #
# # for u,v in g.edges:
# #
# #     random_weight = random.randint(2, 10)
# #     g.add_edge(u, v, weight=random_weight)
# #     g.add_edge(v, u, weight=random_weight)
# #     #print(u,v,random_weight)
# #
# #     weights = nx.get_edge_attributes(g, "weight")
# #     #print(len(weights))
# #     #print(weights)
# # p = nx.all_simple_paths(g,1,8)
# # max_length = 0
# # longestpath =None
# # for i in p:
# #     if len(i) > max_length:
# #         longestpath = i
# #         max_length = len(i)
# # #print(longestpath)
# # for i in range(max_length-1):
# #     g.edges[longestpath[i],longestpath[i+1]]['weight'] = random.randint(2, 15)
# # result = PathEncoding(g,longestpath).srv6_mapping()
# # nx.draw_networkx(g, with_labels=True)
# # pos = nx.spring_layout(g)
# # nx.draw_networkx_edge_labels(g,pos,edge_labels= weights)
# # plt.show()
#
#
# def creat_random_graph(scale):
#     graph = nx.gnm_random_graph(scale, int(scale * 1.5), directed=True)
#     while len(list(nx.weakly_connected_components(graph))) != 1:
#         graph = nx.gnm_random_graph(scale, int(scale * 1.5), directed=True)
#     return graph
#
#
# def creat_grid_graph(scale):
#     graph = nx.DiGraph()
#     for node_stage in range(scale ** 2):
#         graph.add_node(node_stage)
#     for row_stage in range(scale):
#         for col_stage in range(scale - 1):
#             graph.add_edge(row_stage * scale + col_stage, row_stage * scale + col_stage + 1)
#             graph.add_edge(row_stage * scale + col_stage + 1, row_stage * scale + col_stage)
#     for col_stage in range(scale):
#         for row_stage in range(scale - 1):
#             graph.add_edge(row_stage * scale + col_stage, (row_stage + 1) * scale + col_stage)
#             graph.add_edge((row_stage + 1) * scale + col_stage, row_stage * scale + col_stage)
#     return graph
#
#
# def grid_longest_path(scale):
#     col_count = 0
#     ans_path = []
#     for row in range(scale):
#         if col_count == -1:
#             col_count = 0
#         elif col_count == scale:
#             col_count = scale - 1
#         while scale > col_count >= 0:
#             ans_path.append(row * scale + col_count)
#             if row % 2 == 0:
#                 col_count += 1
#             else:
#                 col_count -= 1
#
#     return ans_path
#
#
# G = nx.Graph()  # 无多重边有向图
# G.add_nodes_from(['A', 'B', 'C', 'D', 'E', 'F', 'G', 'H'])  # 添加多个节点
# G.add_edges_from(
#     [['A', 'B'], ['A', 'E'], ['E', 'B'], ['C', 'B'], ['F', 'B'], ['C', 'E'], ['C', 'F'], ['C', 'D'], ['E', 'F'],
#      ['G', 'F'], ['D', 'H'], ['D', 'G'], ['G', 'H']])  # 添加多条边
#
# list = ['A', 'B', 'C', 'E', 'F', 'G', 'H']
# pe = PathEncoding(G, list)
# print(pe.srv6_mapping())
#
# node_sum_list = [5,7,8,10]
# for node_sum in node_sum_list:
#     # g = creat_random_graph(node_sum)
#
#     # node_sum = int(input())
#     # g = creat_grid_graph(node_sum)
#
#     g = nx.read_graphml('real_topo/VtlWavenet2011_91.graphml')
#     print(len(g.nodes))
#
#     # nx.draw_networkx(g)
#     # pos = nx.spring_layout(g)
#     # nx.draw_networkx_edge_labels(g,pos)
#     # plt.show()
#     SLD_total = 0
#     SLD_max = 0
#     SLD_mapping_total = 0
#     SLD_mapping_max = 0
#     total_time = 0
#
#     test_times = 200
#     for i in range(test_times):
#         for u,v in g.edges:
#
#             random_weight = random.randint(2, 10)
#             g.add_edge(u, v, weight=random_weight)
#             g.add_edge(v, u, weight=random_weight)
#             #print(u,v,random_weight)
#
#             weights = nx.get_edge_attributes(g, "weight")
#             #print(len(weights))
#             #print(weights)
#         node_list = [node for node in g.nodes]
#         node_sample = random.sample(node_list, 2)  # random
#         # node_sample = random.sample(range(node_sum ** 2), 2)  # grid
#
#         all_path_list = nx.all_simple_paths(g,node_sample[0], node_sample[1])
#
#         max_length = 0
#         longest_path =None
#         path_sum = 0
#         for path in all_path_list:
#             path_length = len(path)
#             path_sum += 1
#             # print(path_sum)
#             if path_length > max_length:
#                 longest_path = path
#                 max_length = path_length
#             # if path_sum > 500:
#             #     break
#         # tic3 = time.perf_counter()
#         # print(tic3 - tic2)
#         # print(longest_path)
#
#         # max_length = node_sum ** 2
#         # longest_path = grid_longest_path(node_sum)
#
#         SLD_total += max_length
#         SLD_max = max(SLD_max, max_length)
#         for stage in range(max_length-1):
#             g.edges[longest_path[stage],longest_path[stage+1]]['weight'] = random.randint(2, 20)
#         start_tic = time.perf_counter()
#         result = PathEncoding(g, longest_path).srv6_mapping()
#         end_tic = time.perf_counter()
#         SLD_mapping_total += len(result)
#         SLD_mapping_max = max(SLD_mapping_max, len(result))
#         total_time += (end_tic - start_tic)
#
#     print(node_sum,':',SLD_total/test_times, SLD_max, SLD_mapping_total/test_times, SLD_mapping_max, total_time/test_times)
#         # nx.draw_networkx(g, with_labels=True)
#         # pos = nx.spring_layout(g)
#         # nx.draw_networkx_edge_labels(g,pos,edge_labels= weights)
#         # plt.show()
#
# desc_file = open('output_random.txt', 'w', encoding='utf-8')
# print("random")
# for node_sum in range(10,201,5):
#     g = creat_random_graph(node_sum)
#
#     # node_sum = int(input())
#     # g = creat_grid_graph(node_sum)
#
#     # g = nx.read_graphml('real_topo/Syringa_73.graphml')
#     # print(len(g.nodes))
#
#     # nx.draw_networkx(g)
#     # pos = nx.spring_layout(g)
#     # nx.draw_networkx_edge_labels(g,pos)
#     # plt.show()
#     SLD_total = 0
#     SLD_max = 0
#     SLD_mapping_total = 0
#     SLD_mapping_max = 0
#     total_time = 0
#     total_compression = 0
#
#     test_times = 1000
#     for i in range(test_times):
#         for u,v in g.edges:
#
#             random_weight = random.randint(2, 10)
#             g.add_edge(u, v, weight=random_weight)
#             g.add_edge(v, u, weight=random_weight)
#             #print(u,v,random_weight)
#
#             weights = nx.get_edge_attributes(g, "weight")
#             #print(len(weights))
#             #print(weights)
#         node_list = [node for node in g.nodes]
#         node_sample = random.sample(node_list, 2)  # random
#         # node_sample = random.sample(range(node_sum ** 2), 2)  # grid
#
#         shortest_path = nx.shortest_path(g, node_sample[0], node_sample[1])
#         shortest_length = len(shortest_path)
#
#         SLD_total += shortest_length
#         SLD_max = max(SLD_max, shortest_length)
#         for stage in range(shortest_length-1):
#             g.edges[shortest_path[stage],shortest_path[stage+1]]['weight'] = random.randint(2, 20)
#         start_tic = time.perf_counter()
#         result = PathEncoding(g, shortest_path).srv6_mapping()
#         end_tic = time.perf_counter()
#         SLD_mapping_total += len(result)
#         SLD_mapping_max = max(SLD_mapping_max, len(result))
#         total_time += (end_tic - start_tic)
#         total_compression += len(result)/shortest_length
#     ans_str = map(str, [node_sum,SLD_total/test_times, SLD_max, SLD_mapping_total/test_times, SLD_mapping_max, total_time/test_times, total_compression/test_times])
#     print(node_sum,SLD_total/test_times, SLD_max, SLD_mapping_total/test_times, SLD_mapping_max, total_time/test_times, total_compression/test_times)
#     desc_file.write(' '.join(ans_str))
#     desc_file.flush()
#     # print(node_sum,SLD_total/test_times, SLD_max, SLD_mapping_total/test_times, SLD_mapping_max, total_time/test_times)
#         # nx.draw_networkx(g, with_labels=True)
#         # pos = nx.spring_layout(g)
#         # nx.draw_networkx_edge_labels(g,pos,edge_labels= weights)
#         # plt.show()
#
# print("grid")


# desc_file = open('output_grid.txt', 'w', encoding='utf-8')
# for node_sum in range(3,15):
#     # g = creat_random_graph(node_sum)
#
#     # node_sum = int(input())
#     g = creat_grid_graph(node_sum)
#
#     # g = nx.read_graphml('real_topo/Syringa_73.graphml')
#     # print(len(g.nodes))
#
#     # nx.draw_networkx(g)
#     # pos = nx.spring_layout(g)
#     # nx.draw_networkx_edge_labels(g,pos)
#     # plt.show()
#     SLD_total = 0
#     SLD_max = 0
#     SLD_mapping_total = 0
#     SLD_mapping_max = 0
#     total_time = 0
#     total_compression = 0
#
#     test_times = 10
#     for i in range(test_times):
#         for u,v in g.edges:
#
#             random_weight = random.randint(2, 10)
#             g.add_edge(u, v, weight=random_weight)
#             g.add_edge(v, u, weight=random_weight)
#             #print(u,v,random_weight)
#
#             weights = nx.get_edge_attributes(g, "weight")
#             #print(len(weights))
#             #print(weights)
#         node_list = [node for node in g.nodes]
#         node_sample = random.sample(node_list, 2)  # random
#         # node_sample = random.sample(range(node_sum ** 2), 2)  # grid
#
#         shortest_path = nx.shortest_path(g, node_sample[0], node_sample[1])
#         shortest_length = len(shortest_path)
#
#         SLD_total += shortest_length
#         SLD_max = max(SLD_max, shortest_length)
#         for stage in range(shortest_length-1):
#             g.edges[shortest_path[stage],shortest_path[stage+1]]['weight'] = random.randint(2, 20)
#         start_tic = time.perf_counter()
#         print(shortest_path)
#         result = PathEncoding(g, shortest_path).srv6_mapping()
#         end_tic = time.perf_counter()
#         SLD_mapping_total += len(result)
#         SLD_mapping_max = max(SLD_mapping_max, len(result))
#         total_time += (end_tic - start_tic)
#         total_compression += len(result) / shortest_length
#     ans_str = map(str, [node_sum**2,SLD_total/test_times, SLD_max, SLD_mapping_total/test_times, SLD_mapping_max, total_time/test_times, total_compression/test_times])
#     print(node_sum**2,SLD_total/test_times, SLD_max, SLD_mapping_total/test_times, SLD_mapping_max, total_time/test_times, total_compression/test_times)
#     desc_file.write(' '.join(ans_str))
#     desc_file.flush()
#         # nx.draw_networkx(g, with_labels=True)
#         # pos = nx.spring_layout(g)
#         # nx.draw_networkx_edge_labels(g,pos,edge_labels= weights)
#         # plt.show()
#
