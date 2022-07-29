#!/usr/bin/env python
# -*- coding: utf-8 -*-
'''
显示路径对应的是explicit_path文件夹对应的内容——>Segment List——>SRv6 policy
剩下的采用动态路径+灵活算法——>SRv6生成
链路避免、链路亲和	+ 低延时路径
@Project ：AutoSRv6
@File ：SRv6_synthesis.py
@Date ：2022/7/19 15:00 
'''
import json
import os
import shutil
import time
import explicit_path.bandwidth_path
import SRv6_encoding
from ISIS_synthesis import ISIS_Synthesizer
from Policy import Policy
from SRv6_Policy import SRv6_Policy
from explicit_path.bandwidth import BandWidth
from explicit_path.waypoint import WayPoint
from read_topo import Topo
from utils.keyword import *
from explicit_path import waypoint
import read_policy

t = Topo('./topo/topology.json')
# Graph = t.getFromJson(json_topo) #网络拓扑
Graph = t.getFromJson()


class SRv6_Synthesizer(object):
    def __init__(self, topology, policy,out_dir):  # , out_dir
        self.Topology = topology
        self.policy = policy
        # self.out_dir = out_dir
        # self.mid_out_dir = out_dir
        self.out_dir = out_dir
        self.mid_out_dir = out_dir
        self.bandwidth = []
        self.Middle_Policy = []
        self.ISISDomain = []
        self.BGPDomain = []
        self.ISIS_Policy = []
        self.conflict_Policy = []
        self.BGP_Policy = []  # (node, color, ip_list)
        self.SRv6_Policy = []  # (mode, paths_list, exc_edges_or_nodes)
        self.isis_costs = {}
#        self.bandwidth_cons_list = read_policy.bandwidth_info()[1]#需要传递data！！！！！！！！！！！！！！解析文件还需要改

        # self.policy_Synthesis()
        # self.init_Segment_object()
        # self.try_Solve_With_ISIS(self, policy)
        self.init_Segment_object()

    def classify_policy(self, policy):
        '''
        根据policy的classify属性分类
        :param policy: policy 对象
        :return:
        '''

    def init_Segment_object(self):
        # 32位颜色意图范围 0-4294967296
        self.Policy_Color = iter([i for i in range(10, 10000)])
        self.Link_Color = iter([i for i in range(0, 32)])
        self.BSID = iter([i for i in range(50000, 60000)])  # 需要进一步改为ipv6地址
        self.Felx_Algo_SID = iter([i for i in range(128, 255)])
        for node in self.Topology.nodes:  # 给节点添加灵活算法的属性
            self.Topology.nodes[node]['flex_algo'] = []

    def has_waypoint(self, path):
        if '*' in path:
            return True
        else:
            return False

    def get_anycastNode_Set(self, path):
        '''
        得到路径的节点集，对于节点集路径的策略需求
        :param path:
        :return:
        '''
        assert isinstance(path, list)
        anycast_nodes = []
        for node in path:
            if isinstance(node, tuple):
                anycast_nodes.append(node)
        return anycast_nodes

    def try_Solve_With_ISIS(self, policy):  # [A-B-D-H = A-C-E-D-H]
        # IGP 不处理否定路径、航路点路径、TYPE标识非IGP、包含区域节点的策略
        pro_list = [SRv6_explicit, BGP, SRv6_ODN, AS, SRv6_LAT]
        if 'protocol' in policy.pro_dict.keys():
            if policy.pro_dict['protocol'] in pro_list:
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

    def add_ISIS_Policy(self, policy):  # ['p_seq','seq',[H-D-B-A],[H-G-E-C-A],[A,B]]    ,['ecmp',[]],[........]
        '''
        添加policy给对应的ISIS_synthesis处理
        :param policy:
        :return:
        '''
        isis_policy = []
        if len(policy.paths) == 1:
            isis_policy.append((SIMPLE, policy.paths, None, policy.name))  # tuple 第三个为针对拓扑的约束信息
        else:
            path_list = []
            # constraint(A,B,D,H > A,C,E,D,H = A,G,H)——> [(>,=),[A,B,D,H],[A,C,E,D,H],[A,G,H]]
            path_amount = len(policy.paths) - 1
            operate_mark = policy.paths[0]
            policy_path = policy.paths[1]
            balance_flag = True
            order_flag = True
            order_reverse_flag = True

            for i in range(len(operate_mark)):
                if operate_mark[i] != '=':
                    balance_flag = False
            if balance_flag:  # 里面的路劲是等价路径
                isis_policy.append((ECMP, policy_path, None, policy.name))
                self.ISIS_Policy.extend(isis_policy)
                return self.ISIS_Policy

            for i in range(len(operate_mark)):
                if operate_mark[i] != '>':
                    order_flag = False
            if order_flag:  # 里面的路劲是等价路径
                isis_policy.append((ORDER, policy_path, None, policy.name))
                self.ISIS_Policy.extend(isis_policy)
                return self.ISIS_Policy
            for i in range(len(operate_mark)):
                if operate_mark[i] != '<':
                    order_reverse_flag = False
            if order_reverse_flag:  # 里面的路劲是等价路径
                isis_policy.append((ORDER, policy_path[::-1], None, policy.name))
                self.ISIS_Policy.extend(isis_policy)
                return self.ISIS_Policy

            for index, policy_oprate in enumerate(operate_mark):  # (> = )
                if operate_mark[index] == '=':
                    isis_policy.append((ECMP, policy_path[index:index + 2], None, policy.name))
                elif operate_mark[index] == '>':
                    isis_policy.append((ORDER, policy_path[index:index + 2], None, policy.name))
                elif operate_mark[index] == '<':
                    isis_policy.append((ORDER, list(reversed(policy_path[index:index + 2])), None, policy.name))

        self.ISIS_Policy.extend(isis_policy)
        return self.ISIS_Policy

    def distribute_Flex_Algo_SID(self, Flex_Algo_SID, exc_nodes, anycast_nodes=[]):
        '''
            给避免节点的策略分配灵活算法对应的数值(Not)
            :param self:
            :param Flex_Algo_SID:
            :param exc_nodes:
            :param anycast_nodes:[(A,B),(C,D)]
            :return:
            '''
        assert isinstance(exc_nodes, list)
        if anycast_nodes:
            for nodes in anycast_nodes:
                for node in nodes:
                    self.Topology.nodes[node]['flex_algo'].append((Flex_Algo_SID, True))  # 放的是元组
        for node in self.Topology.nodes():

            if node not in exc_nodes and node not in anycast_nodes:
                self.Topology.nodes[node]['flex_algo'].append((Flex_Algo_SID, False))  # (Flex_Algo_SID)

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
            self.Topology.edges[(src_node, dst_node)][LINK_COLOR] = (color_name, link_color)

    def solve_negtive_paths(self, policy):
        assert isinstance(policy, Policy)
        # policy  (name, classify , paths, pro_dict) [[A,D],[(A,B),(C,D)]]
        # []
        exc_nodes = []
        exc_edges = []
        print(policy.classify)
        if policy.classify != 'avoid_node' and policy.classify != 'avoid_link':
            return False
        path = policy.paths
        # print(path)
        if policy.classify == 'avoid_node':
            # 获取避免的节点
            for avoid_node in path[1]:  # [A,(B,C),D]
                if not isinstance(avoid_node, tuple):
                    exc_nodes.append(avoid_node)
                else:
                    exc_nodes.extend(list(avoid_node))
        else:
            # 获取避免的路径[(A,B),(C,D)]
            for edge in path[1]:
                exc_edges.append(edge)

        return exc_nodes, exc_edges

    #
    # policy = Policy('p1','avoid_node',['A','D',['A','B']],{})
    # s = SRv6_Synthesizer(Graph,policy)
    # print(s.solve_negtive_paths(policy)[0])

    def solve_With_Dynamic_SRv6_Policy(self, policy):
        # 处理避免路径和避免节点以及低延迟路径的策略
        # Policy('pol', 'classify':'avoid_node','path':[['C','*','D','*','G'],[(A,B)],'pro_dict':{'exc':('A','B')} }
        if policy.pro_dict['protocol'] == ISIS:
            return False
        if policy.pro_dict['protocol'] == SRv6_explicit:
            return False
        name = policy.name
        color = next(self.Policy_Color)
        bsid = next(self.BSID)
        head = policy.paths[0][0]
        end = policy.paths[0][-1]

        info = {}
        cons = {}

        if 'type' in policy.pro_dict.keys() and SRv6_ODN == policy.pro_dict['type']:
            info[SRv6_ODN] = True
        if 'type' in policy.pro_dict.keys() and SRv6_LAT == policy.pro_dict['type']:
            info[Mertric_Type] = 1

        if EXC in policy.pro_dict.keys():
            cons[EXC] = policy.pro_dict[EXC]
        if ANN in policy.pro_dict.keys():
            info[IP] = policy.pro_dict[ANN]
            self.BGP_Policy.append(SRv6_Policy(policy.name, head, bsid, color, end, info))

        # get constraints
        exc_nodes, exc_edges = self.solve_negtive_paths(policy)  #exc_node = 'B'

        if len(exc_nodes) != 0:  # 避免节点的采用灵活算法,给节点分配灵活算法的值
            info[Flex_Algo] = next(self.Felx_Algo_SID)
            self.distribute_Flex_Algo_SID(info[Flex_Algo], exc_nodes)

        if len(exc_edges) != 0:  # 避免链路
            link_color = next(self.Link_Color)  # 给链路染色
            color_name = 'color' + str(link_color)
            cons[Exclude_Any] = (color_name, link_color)
            self.distribute_color_to_link(color_name, link_color, exc_edges)
        info[CONS] = cons
        #name, head, bsid, color, end_p`oint, info
        pol = SRv6_Policy(name, head, bsid, color, end, info)
        self.SRv6_Policy.append(pol)

        return True

    def get_peer_path(self, srcNode, dstNode):
        '''
        根据两个节点获取对应的path路径
        :return:
        '''
        for path in self.bandwidth_cons_list:
            src = path[0]
            dst = path[-1]
            if src == srcNode and dst == dstNode:
                return path

    def solve_With_Explicit_SRv6_Policy(self, policy):
        '''
        SRv6_Policy 显示路径生成
        Policy('policy_name','waypoint',[srcNode,dstNode,[waypoint]],{'protocol':SRv6_explicit})
        Policy('policy_name','bandwidth',[srcNode,dstNode,100],{'protocol':SRv6_explicit})
        :param policy:Policy('policy_name','weight_balance',[[1,2,3],[A,D,H],[A,E,D,H],[A,G,H]],{'protocol':SRv6_explicit})
        :return:
        '''
        explicit_type = ['waypoint', 'bandwidth', 'weight_balance']
        if policy.classify not in explicit_type:
            return False
        name = policy.name
        color = next(self.Policy_Color)
        bsid = next(self.BSID)

        if policy.classify == 'waypoint' or policy.classify == 'bandwidth':
            head = policy.paths[0]
            end = policy.paths[1]
        else:
            head = policy.paths[1][0]
            end = policy.paths[1][-1]

        info = {}
        cons = {}

        info[Policy_Type] = SRv6_explicit
        if EXC in policy.pro_dict.keys():
            cons[EXC] = policy.pro_dict[EXC]
        if ANN in policy.pro_dict.keys():
            info[ANN] = policy.pro_dict[ANN]
            self.BGP_Policy.append(SRv6_Policy(name, head, bsid, color, end, info))

        # 构建显示路径：
        priority = 128
        info[Can_Paths] = []
        flex_algo = 0
        if Flex_Algo in info.keys():
            flex_algo = info[Flex_Algo]
        weight = 1

        if policy.classify == 'waypoint':
            policy_path = policy.paths  # 传递给waypoint的列表是[S,T,[A,B]]
            waypoint_path = WayPoint(self.Topology, policy_path).explicit_path()
            segment_list = SRv6_encoding.PathEncoding(self.Topology, waypoint_path)
            info[Can_Paths].append(Can_Paths(priority, segment_list, weight))
            self.SRv6_Policy.append(SRv6_Policy(name, head, color, end, bsid, **info))
        elif policy.classify == 'bandwidth':#!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!  根据read_policy返回的结果
           # 解析之后的结果policy(name,classify,[A,B,100],proc_dict)
           # Can_Path = namedtuple("Can_Path", [Priority, Seg_List, Weight])
            srcNode = policy.paths[0]
            dstNode = policy.paths[1]
            if len(self.bandwidth_path) == 0:
                bandWidth = BandWidth(self.Topology,self.bandwidth_cons_list)
                bandWidth.creat_z3_var()
                bandWidth.path_link_con()
                bandWidth.edge_bandwidth_con()
                bandWidth.solver.check()
                ppp = bandWidth.solver.model()
                for i in bandWidth.edge_key_var.values():
                    print(ppp.get_interp(i))
                    print(bool(ppp.get_interp(i)))
               # print(ppp)
               # print(ppp.get_interp(bandWidth.edge_key_var[('c', 'd', 'a', 'd')]))
                self.bandwidth_cons_list.extend(bandWidth.set_paths())
            bandwidth_path = self.get_peer_path(srcNode,dstNode)
            segment_list = SRv6_encoding.PathEncoding(self.Topology, bandwidth_path)
            info[Can_Paths].append(Can_Paths(priority, segment_list, weight))
            self.SRv6_Policy.append(SRv6_Policy(name, head, color, end, bsid, **info))
        elif policy.classify == 'weight_balance':
            policy_fraction = policy.paths[0]
            policy_path = policy.paths[1:]
            segment_list = []
            for index, path in enumerate(policy_path):
                segment_list.append(path)
                info[Can_Paths].append(Can_Paths(priority, segment_list, policy_fraction[index]))
        else:
            conflict_policy = self.conflict_Policy
            # (ECMP, [['A','B','D','H'] ,['A','C','E','D','H']], None, policy.name)
            # policy_3 = ('order', [['A', 'B', 'D', 'H'], ['A', 'C', 'E', 'D', 'H']], None, 'p2')
            # policy_4 = ('ecmp',[['A','C','E','D','H'],['A','C','E','F','G','H']],None, 'p2')
            segment_list = []
            for pol in conflict_policy:
                for mode, path_list, exc, pol.name in pol:
                    if mode == 'ecmp':
                        for path in path_list:
                            segment_list.append(path)
                            info[Can_Paths].append(Can_Paths(priority, segment_list, 1))
                    if mode == 'order':
                        for index, path in enumerate(path_list):
                            segment_list = path
                            priority -= 1
                            info[Can_Paths].append(Can_Paths(priority, segment_list, 1))
        self.SRv6_Policy.append(SRv6_Policy(name,head,color,end,bsid,**info))

    def output(self, text):#override
        print(text)


    def policy_Synthesis(self):

        self.output('Begin sythesize policy')
        for policy in self.policy:
            # try  solve with isis
            if policy.classify =='constraint' and self.try_Solve_With_ISIS(policy):
                out_dir = os.path.join(self.mid_out_dir, "mid")
                shutil.rmtree(out_dir, True)
                if not os.path.exists(out_dir):
                    os.mkdir(out_dir)

                with open(os.path.join(out_dir, "sr_policy.json"), 'w', encoding='utf-8') as f:
                    f.write(json.dumps(self.SRv6_Policy, indent=4, default=lambda obj: obj.__dict__))

                self.output('*' * 3 + 'Out ISIS Policy' + '*' * 3)

                with open(os.path.join(out_dir, "ospf_policy.json"), 'w', encoding='utf-8') as f:
                    f.write(json.dumps(self.ISIS_Policy, indent=4, default=lambda obj: obj.__dict__))

                for mode, path_list, exc, name in self.ISIS_Policy:
                    self.output('*' * 20)
                    self.output('mode: ' + mode)
                    self.output('path_list: ')
                    for path in path_list:
                        self.output(path)
                    self.output('exc_edges_or_nodes: ' + str(exc))
                    self.output('*' * 20)

                # solve isis policy
                t1 = time.time()
                self.output('*' * 3 + 'Begin synthesize ISIS Policy' + '*' * 3)
                if self.ISIS_Policy:
                    isis = ISIS_Synthesizer(self.Topology, self.ISIS_Policy,
                                            out_dir=out_dir)
                    self.isis_costs = isis.synthesize()
                t2 = time.time()
                self.output("ISIS synthesize time is " + str(t2 - t1) + "s")
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

        self.output('*' * 3 + 'Out SRv6 Policy' + '*' * 3)
        print(self.SRv6_Policy)
        for pol in self.SRv6_Policy:
            print(pol)
        # for po in self.SRv6_Policy:
        #     print(po)

        out_dir = os.path.join(self.mid_out_dir, "mid")
        shutil.rmtree(out_dir, True)
        if not os.path.exists(out_dir):
            os.mkdir(out_dir)

        with open(os.path.join(out_dir, "sr_policy.json"), 'w', encoding='utf-8') as f:
            f.write(json.dumps(self.SRv6_Policy, indent=4, default=lambda obj: obj.__dict__))



        t2 = time.time()
        self.output("ISIS synthesize time is " + str(t2 - t1) + "s")