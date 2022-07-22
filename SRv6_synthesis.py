#!/usr/bin/env python
# -*- coding: utf-8 -*-
'''
显示路径对应的是explicit_path文件夹对应的内容——>Segment List——>SRv6 policy
剩下的采用动态路径+灵活算法——>SRv6生成
链路避免、链路亲和	+ 低延时路径
@Project ：SRv6CS 
@File ：SRv6_synthesis.py
@Date ：2022/7/19 15:00 
'''
import SRv6_encoding
from Policy import Policy
from SRv6_Policy import SRv6_Policy
from read_topo import Topo
from utils.keyword import *

t = Topo('./topo/topology.json')
# Graph = t.getFromJson(json_topo) #网络拓扑
Graph = t.getFromJson()


class SRv6_Synthesizer(object):
    def __init__(self, topology, policy): #, out_dir
        self.Topology = topology
        self.policy = policy
       #self.out_dir = out_dir
        #self.mid_out_dir = out_dir

        self.Middle_Policy = []
        self.ISISDomain = []
        self.BGPDomain = []
        self.ISIS_Policy = []  # (mode, paths_list, exc_edges_or_nodes)
        self.BGP_Policy = []  # (node, color, ip_list)
        self.SRv6_Policy = []
        self.isis_costs = {}

        # self.policy_Synthesis()
        # self.init_Segment_object()
        # self.try_Solve_With_ISIS(self, policy)

    def classify_policy(self,policy):
        '''
        根据policy的classify属性分类
        :param policy: policy 对象
        :return:
        '''


    def init_Segment_object(self):
            # 32位颜色意图范围 0-4294967296
            self.Policy_Color = iter([i for i in range(0, 10000)])
            self.Link_Color = iter([i for i in range(0, 32)])
            self.BSID = iter([i for i in range(50000, 60000)])  # 需要进一步改为ipv6地址
            self.Felx_Algo_SID = iter([i for i in range(128, 255)])
            for node in self.Topology.nodes:  # 给节点添加灵活算法的属性
                node['flex_algo'] = []

    def try_Solve_With_ISIS(self, policy):  # [A-B-D-H = A-C-E-D-H]
            # IGP 不处理否定路径、航路点路径、TYPE标识非IGP、包含区域节点的策略
            pro_list = [SRv6_explicit, BGP, SRv6_ODN, AS, SRv6_LAT]
            if 'protocol' in policy.pro_dict.keys():
                if policy.pro_dict['protocol'] in pro_list:
                    return False
            for path in policy.paths:
                if policy.classify != 'ISIS':
                    return False
                if self.get_Node_Set(path):
                    return False
            if not self.add_ISIS_Policy(policy):
                return False
            return True

    def is_ISIS_Policy_Repeat(self, policy):  # N
            # assert isinstance(policy_list, list)
            if SRv6_Synthesizer.is_isis_path_req_sat(self.ISIS_Policy, policy[0], policy[1]):
                return False
            else:
                return True

    @staticmethod
    def is_isis_path_req_sat(reqs, checked_mode, checked_path_list):
            """
            判断需求合理性
            :param reqs: 已经检查的需求集合
            :param checked_mode: 待检查需求类型
            :param checked_paths: 待检查需求路径
            :return:
            """
            assert len(checked_path_list) >= 1

            for mode, path_list, exc, name in reqs:
                for checked_path in checked_path_list:
                    for i, src in enumerate(checked_path.nodes_list):
                        for j, dst in enumerate(checked_path.nodes_list):
                            if i >= j:
                                continue
                            for path in path_list:
                                if src in path.nodes_list and dst in path.nodes_list:
                                    head = path.nodes_list.index(src)
                                    tail = path.nodes_list.index(dst)
                                    if head < tail:
                                        list = path.nodes_list[head:tail + 1]
                                        if list != checked_path.nodes_list[i:j + 1]:
                                            return False

            return True

        # def add_ISIS_Policy(self, mode, path, exc_nodes=None, exc_edges=None):
        #
        #     return True

    def add_ISIS_Policy(self, isis_data):  # ['p_seq','seq',[H-D-B-A],[H-G-E-C-A],[A,B]]    ,['ecmp',[]],[........]
            '''
            添加isis_policy的约束
            :param self:
            :param isis_data:
            :return:
            '''
            isis_policy = []
            paths = []
            for data in isis_data:
                length = len(data) - 2
                for i in range(length):
                    paths.append(data[2 + i])
                if data[0] == 'balance':
                    isis_policy.append((ECMP, paths, None, data[1]))
                if data[0] == 'seq':
                    isis_policy.append((ORDER, paths, None, data[1]))

            for policy in isis_policy:
                if self.is_ISIS_Policy_Repeat(policy):
                    return False

            self.ISIS_Policy.extend(isis_policy)
            return True

    def distribute_Flex_Algo_SID(self, Flex_Algo_SID, exc_nodes, anycast_nodes=[]):
            '''
            给避免节点的策略分配灵活算法对应的数值
            :param self:
            :param Flex_Algo_SID:
            :param exc_nodes:
            :param anycast_nodes:
            :return:
            '''
            assert isinstance(exc_nodes, list)
            if anycast_nodes:
                for nodes in anycast_nodes:
                    for node in nodes:
                        self.Topology.nodes[node]['flex_algo'].append((Flex_Algo_SID, True))  # 放的是元组
            for node in self.Topology.nodes(data=True):
                assert isinstance(node, tuple)
                data = node[1]
                if node[0] not in exc_nodes and node[0] not in anycast_nodes:
                    data['flex_algo'].append(
                        (Flex_Algo_SID, False))  # (Flex_Algo_SID)

    def distribute_color_to_link(self, color_name, link_color, exc_edges):
            '''

            :param self:
            :param color_name: 链路着色名称
            :param link_color: 链路着色数字
            :param exc_edges: 避免的链路
            :return:
            '''
            for edge in exc_edges:
                src_node = edge[0]
                dst_node = edge[1]
                # dst_inter = self.Links[(src_node, dst_node)][0]
                # dst = edge[1]
                self.Topology.edges[(src_node,dst_node)][LINK_COLOR] = (color_name, link_color)

    def solve_negtive_paths(self, policy):
        assert isinstance(policy,Policy)
        # policy  (name, classify , paths, pro_dict) ['A','D',[('A','B')]]
        # [[A,D,[(A,B)], [A,H],[C,D]]
        exc_nodes = []
        exc_edges = []
        print(policy.classify)
        if(policy.classify != 'avoid_node'  and policy.classify != 'avoid_link'):
            return False
        path = policy.paths
        #print(path)
        #链路着色处理
        link = path[-1] # ['A','B']
        if isinstance(link[0], tuple):
            print('sssss')
            length = len(link)
            for i in range(length):
                exc_edges.append(link[i])
            #节点避免用灵活算法进行处理
        else:
            node_list = link
            node_length = len(link)
            for i in range(node_length):
                exc_nodes.append(node_list[i])
        return exc_nodes, exc_edges
#
# policy = Policy('p1','avoid_node',['A','D',['A','B']],{})
# s = SRv6_Synthesizer(Graph,policy)
# print(s.solve_negtive_paths(policy)[0])

    def solve_With_Dynamic_SRv6_Policy(self, policy):
        #Policy('pol', 'classify':'avoid_node','path':['C','*','D','*','G'],'pro_dict':{'exc':('A','B')} }
        if policy.pro_dict['protocol'] == 'ISIS':
            return False

        name = policy.name
        color = next(self.Policy_Color)
        bsid = next(self.BSID)
        head = policy.paths[0]
        end = policy.paths[-1]

        info = {}
        cons = {}

        if 'protocol' in policy.pro_dict.keys() and SRv6_ODN == policy.pro_dict['protocol']:
            info[SRv6_ODN] = True
        if 'protocol' in policy.pro_dict.keys() and SRv6_LAT == policy.pro_dict['protocol']:
            info[Mertric_Type] = 1
        if EXC in policy.pro_dict.keys():
            cons[EXC] = policy.pro_dict[EXC]
        if ANN in policy.pro_dict.keys():
            self.BGP_Policy.append((end, color, policy.pro_dict[ANN]))

        # get constraints
        exc_nodes, exc_edges = self.solve_negtive_paths(policy)

        if len(exc_nodes) != 0:    #避免节点的采用灵活算法
            info[Flex_Algo] = next(self.Felx_Algo_SID)
            self.distribute_Flex_Algo_SID(info[Flex_Algo], exc_nodes)

        if len(exc_edges) != 0: #避免链路
            link_color = next(self.Link_Color)
            color_name = 'color' + str(link_color)
            cons[Exclude_Any] = (color_name, link_color)
            self.distribute_color_to_link(color_name, link_color, exc_edges)
        info[CONS] = cons

        self.SRv6_Policy.append(SRv6_Policy(name, head, color, end, bsid, **info))

        return True

    def get_Segment_List(self):
        '''

        :return:
        '''

    def solve_With_Explicit_SRv6_Policy(self, policy):
        '''
        SRv6_Policy 显示路径生成
        :param policy:Policy('policy_name','weight_balance',[[1,2,3],[A,D,H],[A,E,D,H],[A,G,H]],proc{type:explicit})
        :return:
        '''
        explicit_type = ['waypoint','bandwidth','weight_balance']
        if policy.classify not in explicit_type:
            return False
        name = policy.name
        color = next(self.Policy_Color)
        bsid = next(self.BSID)
        if(policy.classify == 'waypoint' or policy.classify == 'bandwidth'):
            head = policy.paths[0]
            end = policy.paths[-1]
        else:
            head = policy.paths[0][0]
            end = policy.paths[0][-1]
        info = {}
        cons = {}
        info[Policy_Type] = SRv6_explicit
        candidate_path = []
        #得到segment_list
        info[Can_Paths] = []
        if (policy.classify == 'waypoint' or policy.classify == 'bandwidth'):
            path = SRv6_encoding(self.Topology,policy.paths)
            candidate_path.append(Can_Paths(Priority = 128, Seg_List = path, Weight = 1))
        else:
            weight_paths = []
            path_length = len(policy.paths)-1
            for i in range(1,path_length):
                path_i = policy.paths[i]
                weight_i = policy.paths[0][i-1]
                candidate_path.append(Can_Paths(Priority = 128, Seg_List = path_i, Weight = weight_i))
        info[Can_Paths].append(candidate_path)
        self.SRv6_Policy.append(SRv6_Policy(name,head,color,end,bsid,**info))


    def output(self, text):
       # if self.log_signal is None:
       print(text)
       # else:
          #  t = str(text)
           # self.log_signal.emit(t)


    def policy_Synthesis(self):
        self.output('Begin sythesize policy')
        for policy in self.policy:
            # try  solve with isis
            if self.try_Solve_With_ISIS(policy):
                continue
            # solve with dynamic SRv6 Policy
            if self.solve_With_Dynamic_SRv6_Policy(policy):
                continue
            # solve with explicit SRv6 Policy
            try:
                self.solve_With_Explicit_SRv6_Policy(policy)
            except Exception as e:
                self.output(e)
                self.output("Can't solve policy:" + policy.name)
                exit(-1)
        # self.output('*' * 3 + 'Out distributed Prefix SIDs' + '*' * 3)
        #
        # for node in self.Topology.nodes(data=True):
        #     data = node[1]
        #     if data[TYPE] == NODE:
        #         self.output(node[0])
        #         for sid in data[PREFIX_SID]:
        #             self.output(sid)


