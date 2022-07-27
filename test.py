#!/usr/bin/env python
# -*- coding: utf-8 -*-
'''
@Project ：AutoSRv6 
@File ：test.py
@Author ：Lucky
@Date ：2022/7/23 16:25 
'''
import os

from ISIS_synthesis import ISIS_Synthesizer, SIMPLE
from Policy import Policy
from SRv6_synthesis import SRv6_Synthesizer
from read_topo import Topo, interfaceByEdge
from keyword import *

from utils.keyword import ECMP, ORDER, SRv6_Dynamic

# list2 = ['0','1','2','3']
# print(list2[:-1])
# print(list2)
# print(list(reversed(list2)))

t = Topo('./topo/topology.json')
# Graph = t.getFromJson(json_topo) #网络拓扑
Graph = t.getFromJson()



class Test:
    def __init__(self,topo):
        self.topology = topo
        self.interface_names = []
        self.edge_node_to_inter = {}
        self.isis_policy = []

    def add_ISIS_Policy(self, policy):  # ['p_seq','seq',[H-D-B-A],[H-G-E-C-A],[A,B]]    ,['ecmp',[]],[........]
        '''
        添加policy给对应的ISIS_synthesis处理
        :param policy:
        :return:
        '''
        isis_policy = []
        if len(policy.paths) == 1:
            isis_policy.append((SIMPLE,policy.paths,None,policy.name))# tuple 第三个为针对拓扑的约束信息
        else:
            path_list = []
            # constraint(A,B,D,H > A,C,E,D,H = A,G,H)——> [(>,=),[A,B,D,H],[A,C,E,D,H],[A,G,H]]
            path_amount = len(policy.paths)-1
            operate_mark = policy.paths[0]
            policy_path = policy.paths[1::]
            balance_flsg = True
            for i in range(len(operate_mark)):
                if operate_mark[i] != '=':
                    balance_flsg = False
            if balance_flsg:
                isis_policy.append((ECMP, policy_path, None, policy.name))
                return True
            for i in range(len(operate_mark)):#(> = )
                if operate_mark[i] == '=':
                    isis_policy.append((ECMP,policy_path[i:i+2],None,policy.name))
                elif operate_mark[i] == '>':
                    isis_policy.append(isis_policy.append((ORDER, path_list[i:i+2], None, policy.name)))
                elif operate_mark[i] == '<':
                    isis_policy.append(isis_policy.append((ORDER, list(reversed(path_list[i:i+2])), None, policy.name)))

        self.isis_policy.extend(isis_policy)
        return True

    def get_necessary_info(self):
        '''

        :return:
        '''
        self.node_names = [node for node in self.topology.nodes()]
        topo_edge = [edge for edge in self.topology.edges()]
        for e in topo_edge:
            self.interface_names.append(self.topology.edges[e[0],e[1]]['src_int'])
            self.interface_names.append(self.topology.edges[e[0], e[1]]['dst_int'])
        for e in topo_edge:
            self.edge_node_to_inter[e] = (interfaceByEdge(self.topology,e))
        edges = []
        for mode, path_list, exc, name in self.isis_policy:
            for path in path_list:
                for index, node in enumerate(path[:-1]):
                    edges.append(path[index],path[index + 1])
        #print(edges)
        self.req_edges = list(set(edges))


path = [('='),['A','B','D','H' ],['A','C','E','D','H']]
policy = Policy('p','b',path,{})
t = Test(Graph)
t.add_ISIS_Policy(policy)
t.get_necessary_info()

policy2 = Policy('p2','constraint',[('>','='),[['A','B','D','H'] ,['A','C','E','D','H'],['A','C','E','F','G','H']]],{'protocol':'ISIS'})
#sr_synthesis = SRv6_Synthesizer(Graph,policy2)
#policy_1 = sr_synthesis.add_ISIS_Policy(policy2)
policy_3 = ('order', [['A', 'B', 'D', 'H'], ['A', 'C', 'E', 'D', 'H']], None, 'p2')
policy_4 = ('ecmp',[['A','C','E','D','H'],['A','C','E','F','G','H']],None, 'p2')
isis_p = (ECMP, [['A','B','D','H'] ,['A','C','E','D','H']], None, policy.name)
#print(isis_p)
# isis_p2 = (ORDER,[['H','D','B','A'],['H','G','E','C','A']], None, policy.name)
# isis_p3 = (ECMP,[['A','B','D'],['A','C','E','D']], None, policy.name)
# list_p = []
# list_p.append(isis_p)
# list_p.append(isis_p2)
# print([isis_p])
# print(policy_1)
# print(policy_1[0])
# print([policy_1[0]])

#
# isis_synthesis = ISIS_Synthesizer(Graph,[policy_3,policy_4])
# isis_synthesis.synthesize()

policy1 = Policy('p1','constraint',[('='),[['A','B','D','H'] ,['A','C','E','D','H']]],{'protocol':'ISIS'})

p4_dict = {}
p4_dict['protocol'] = SRv6_Dynamic
p4 = Policy('p1','avoid_node',[['A','H'],['B']],p4_dict)

policy = []
policy.append(policy1)
policy.append(p4)


out_dir = os.path.dirname('ConfigurationFiles')

srv6 = SRv6_Synthesizer(Graph,policy,out_dir)
srv6.policy_Synthesis()