#!/usr/bin/env python

# -*- coding: utf-8 -*-

'''
读取策略文件并解析成Policy四元组
使用PLY编写的词法与语法
Input：策略文件*2
Output：
@Project ：AutoSRv6
@File ：read_policy.py
@Date ：2022/7/19 15:51
'''
import os
import shutil
import json
import time

from pyparsing import *
from Policy import *


class read_policy(object):

    def __init__(self,out_dir=None,log_signal=None):
        self.out_dir = out_dir
        self.log_signal = log_signal
        self.policy_list = []

        # 通用匹配模式
        self.integer = Word(nums)
        self.id = Word(srange("[a-zA-Z_]"), srange("[a-zA-Z0-9_-]"))
        self.element = Word(srange("[0-9a-fA-F]"))
        self.op = Word(srange("[>=-]:"))
        self.ip_subnet = Combine(self.element - (':' + self.element) * 7)("address") + "/" + self.integer("num")
        self.ip = ("ip" + self.ip_subnet("subnet"))

        # ip前缀匹配模式

        # prefix pre1 {AD80:0000:0000:0000:ABAA:0000:00C2:0002 / 128}

        self.def_ipprefix = Word("prefix") + self.id("name") + Suppress("{") + self.ip_subnet("ip") + Suppress("}")

        # 带宽约束

        # self.bandwidth = self.integer("bandwidth*")
        # self.p_bandwidth = Word("bandwidth") + Suppress("(") + self.id("bandwidth*") + (Suppress(",")
        #                                                                                 + self.id("bandwidth*"))[
        #     0, ...] + Suppress(",") + self.bandwidth + Suppress(")")
        self.p_bandwidth = Word("bandwidth") + Suppress("(") + self.id("src*") + Suppress(",") + self.id(
            "dst*") + Suppress(
            ",") + self.integer("bandwidth*") + Suppress(")")

        # waypoint (C,D)
        # self.p_bandwidth = Word("bandwidth") + Suppress("(") + self.id("src*") + Suppress(",") + self.id(
        #     "dst*") + Suppress(",") + self.id("bandwidth*") + Suppress(")")

        self.p_waypoint = Word("waypoint") + Suppress("(") + Suppress("[") + \
                          self.id("p_node*") + Suppress(",") + self.id("dst_node*")[0, ...] + Suppress("]") \
                          + Suppress("@") + Suppress("[") + self.id("waypoint*") + \
                          (Suppress(",") + self.id("waypoint*"))[0, ...] \
                          + Suppress("]") + Suppress(")")

        self.p_path = self.id("node*") + (Suppress("-") + self.id("node*"))[0, ...]

        self.p_constraint = Word("constraint") + Suppress("(") + \
                            self.id("constraint*") + (Suppress(",") + self.id("constraint*"))[0, ...] + \
                            (self.op("op*") + self.id("constraint*") + (Suppress(",") + self.id("constraint*"))[
                                0, ...])[0, ...] \
                            + Suppress(")")

        # weight_balance()
        self.p_weight_balance = Word("weight_balance") + Suppress("(") + \
                                self.id("weight_balance*") + (Suppress(",") + self.id("weight_balance*"))[0, ...] \
                                + (Suppress(":") + self.id("weight_balance*") +
                                   (Suppress(",") + self.id("weight_balance*"))[0, ...])[0, ...] \
                                + Suppress("=") + self.integer("weight*") + (Suppress(":") + self.integer("weight*"))[
                                    0, ...] + Suppress(")")

        # avoid_node()
        self.p_avoid_node = Word("avoid_node") + Suppress("(") + \
                            Suppress("[") + self.id("path_node*") + (Suppress(",") + self.id("path_node*"))[
                                0, ...] + Suppress("]") \
                            + Suppress("!") + Suppress("[") + self.id("avoid_node*") + \
                            (Suppress(",") + self.id("avoid_node*"))[0, ...] \
                            + Suppress("]") + \
                            (Suppress("&") + self.id("low_latency") + Suppress("=") + self.id("True"))[
                                0, ...] + Suppress(")")
        # avoid_link()
        self.p_avoid_link = Word("avoid_link") + Suppress("(") + \
                            Suppress("[") + self.id("path_link*") + (Suppress(",") + self.id("path_link*"))[
                                0, ...] + Suppress("]") \
                            + Suppress("!") + Suppress("[") + Suppress("(") + self.id("avoid_link*") + \
                            (Suppress(",") + self.id("avoid_link*"))[0, ...] \
                            + Suppress(")") + (Suppress(",") + Suppress("(") + self.id("avoid_link*") +
                                               (Suppress(",") + self.id("avoid_link*"))[0, ...] \
                                               + Suppress(")"))[0, ...] + Suppress("]") + \
                            (Suppress("&") + self.id("low_latency") + Suppress("=") + self.id("True"))[0, ...] + \
                            Suppress(")")
        # low_latency()
        self.p_simple = Word("simple") + Suppress("(") + Suppress("[") + self.id("simple*") + \
                        (Suppress(",") + self.id("simple*"))[0, ...] + Suppress("]") + \
                        (Suppress("&") + self.id("low_latency") + Suppress("=") + self.id("True"))[0, ...] \
                        + Suppress(")")

        # 总定义

        self.def_policy = self.id("policy_name") + Suppress(":") + \
                          ((self.p_bandwidth[..., 1]) & (self.p_avoid_link[..., 1]) & (self.p_constraint[..., 1]) & (
                              self.p_simple[..., 1]) &
                           (self.p_waypoint[..., 1]) & (self.p_avoid_node[..., 1]) & (
                               self.p_weight_balance[..., 1])) + Suppress(";")

        # & ( p_low_latency[..., 1])& ( p_disjoint[..., 1])) + \

        # 主函数匹配模式

        # A -> H apply traffic; # [['A'],['E'],['C','G']]

        # main_direction_schema = id("name1") + Suppress("->") + id("name2") + Suppress("apply") + id(
        #     "policy_name*") + Suppress(";")

        self.def_main = Suppress("main") + Suppress("{") + \
                        (Group(self.def_policy)[...]) + \
                        Suppress("}")
        # with open(r'./policy/new_policy', 'r') as file:
        #     self.data = file.read()
        with open(r'./policy/new_policy', 'r') as file:
            self.data = file.read()

    # 1. low_latancy path?
    # 2. 全改成类内函数
    # 3. avoid_node 、 avoid_link输入解析修改([C,@,D,H])
    def get_policy(self):
        '''
        # 所有定义的策略集
        # 返回一个记录所有定义的策略集的字典，键为策略集名字，值为策略集具体信息
        :param data:
        :return: policy_dict
        '''
        policy_dict = {}
        for po in self.def_policy.searchString(self.data):
            # print(po)
            policy_dict[po["policy_name"]] = po
        # print(policy_dict.keys())
        # print("\n")
        # print(policy_dict.values())
        # print("\n")
        # print("****************************************")
        return policy_dict

    # get_policy(user_policy)

    # 主函数调用策略

    def main_policy_called(self):
        global_plist = []  # 全局策略
        group_plist = []  # 多个用户组参与的策略
        direction_plist = []  # 方向性策略

        for i in sum(self.def_main.searchString(self.data)):
            if len(i) == 1:
                global_plist.append(i)
            else:
                # print("!!!!!!!!!!!!!!!!!!!!!!!!!!!!!")
                # print(i)
                # print("!!!!!!!!!!!!!!!!!!!!!!!!!!!!!")
                group_plist.append(i)
        return global_plist, group_plist, direction_plist

    # 返回一个二维list记录带宽约束信息

    # ['CE6', 'CE5', 2000]

    def constraint_info(self):

        policy = self.get_policy()
        # print(policy)
        constraint_policy = []
        for i in self.main_policy_called()[1]:
            pro_dict = {'protocol': 'ISIS'}
            length = int(len(i))
            # print(i)
            # print(i[length - 1])

            list1 = list(policy[i[0]])  # ['policy', 'traffic', 'waypoint', 'C', 'D']
            # print(list1)

            name = list1[0]  # extra:得到策略的name

            if 'constraint' in list1:
                ops = policy[i[0]]['op']
                # print(i[0])
                cs = policy[i[0]]['constraint']
                start = 0
                end = 0
                cs_tmp = []
                while end < len(cs):
                    if cs[end] == policy[i[0]]['constraint'][-1]:
                        cs_tmp.append(list(cs[start:end + 1]))
                        start = end + 1
                    end += 1
                # print(cs)
                result = []
                result.append(list(ops))
                result.append(cs_tmp)
                #           #policy = SRv6_Policy(list1[1],)

                constraint_policy.append(Policy(name, "constraint", result, pro_dict))

        return constraint_policy

    def bandwidth_info(self):
        '''
        :param data: bandwidth(A,H,100)
        :return: Policy('policy_name','bandwidth',[srcNode,dstNode,100],{'protocol':SRv6_explicit})
        '''

        policy = self.get_policy()
        # print(policy)
        bd_policy = []
        constraint_list = []
        for i in self.main_policy_called()[1]:
            pro_dict = {'protocol': 'SRv6_explicit'}
            length = int(len(i))
            # print(i[0])
            list1 = list(policy[i[0]])
            name = list1[0]
            if 'bandwidth' in list1:
                # constraint_list.append(list(policy[i[0]]["bandwidth"]))
                # bd_policy.append(Policy(name, "bandwidth", list(policy[i[0]]["bandwidth"]), pro_dict))
                bandwidth_guarentee = str(i['bandwidth'][0])
                src_node = str(policy[i[0]]['src'][0])
                dst_node = str(policy[i[0]]['dst'][0])
                # print(wp)
                #           #policy = SRv6_Policy(list1[1],)
                #
                print(src_node)
                constraint = []
                constraint.append(src_node)
                constraint.append(dst_node)
                constraint.append(bandwidth_guarentee)
                print(constraint)
                # wp_tmp.extend(list(pn))
                # wp_tmp.extend(list(dst_node))
                # wp_tmp.append(list(pn))
                # wp_tmp.append(list(dst_node))
                bd_policy.append(Policy(name, "bandwidth", constraint, pro_dict))
        return bd_policy

    # bd_list=bandwidth_info(user_policy)
    # #
    # print(bd_list[0].paths)

    def waypoint_info(self):
        '''
        :param data:  waypoint([A,H]@[B,C])
        :return: # Policy('policy_name','waypoint',[srcNode,dstNode,[waypoint]],{'protocol':SRv6_explicit})
        '''

        policy = self.get_policy()
        # print(policy)
        wp_policy = []
        for i in self.main_policy_called()[1]:
            pro_dict = {'protocol': 'SRv6_explicit'}
            length = int(len(i))

            list1 = list(policy[i[0]])  # ['policy', 'traffic', 'waypoint', 'C', 'D']
            # print(list1)
            name = list1[0]  # extra:得到策略的name

            if 'waypoint' in list1:
                wp = policy[i[0]]['waypoint']
                pn = policy[i[0]]['p_node']
                dst_node = policy[i[0]]['dst_node']
                # print(wp)

                #           #policy = SRv6_Policy(list1[1],)
                constraint = {}
                constraint["src"] = pn[0]
                constraint["dst"] = dst_node[0]
                wp_tmp = list(wp)
                # wp_tmp.extend(list(pn))
                # wp_tmp.extend(list(dst_node))
                # wp_tmp.append(list(pn))
                # wp_tmp.append(list(dst_node))
                constraint["waypoint"] = wp_tmp
                wp_policy.append(Policy(name, "waypoint", constraint, pro_dict))
                self.policy_list.append(Policy(name, "waypoint", constraint, pro_dict))
        #
        return wp_policy

    def weight_balance_info(self):
        '''
        :param data:weight_balance(A,D,H : A,E,D,H : A,G,H = 1 : 2 : 3)
        :return:Policy('policy_name','weight_balance',[[1,2,3],[A,D,H],[A,E,D,H],[A,G,H]],{'protocol':SRv6_explicit})
        '''

        policy = self.get_policy()
        # print(policy)
        wb_policy = []
        for i in self.main_policy_called()[1]:
            pro_dict = {'protocol': 'SRv6_explicit'}
            length = int(len(i))
            # print(i)
            list1 = list(policy[i[0]])  # ['policy', 'traffic', 'waypoint', 'C', 'D']
            # print(list1)
            name = list1[0]  # extra:得到策略的name

            if 'weight_balance' in list1:
                # print(policy)
                # print(i[length - 1])
                wb = policy[i[0]]['weight_balance']
                # print(policy[i[0]]['weight_balance'][-1])
                start = 0
                end = 0
                wb_tmp = []
                wb_tmp.append(list(policy[i[0]]['weight']))
                while end < len(wb):
                    if wb[end] == policy[i[0]]['weight_balance'][-1]:
                        wb_tmp.append(list(wb[start:end + 1]))
                        start = end + 1
                    end += 1

                # print(wb_tmp)
                #           #policy = SRv6_Policy(list1[1],)

                wb_policy.append(Policy(name, "weight_balance", wb_tmp, pro_dict))
                self.policy_list.append(Policy(name, "weight_balance", wb_tmp, pro_dict))
        return wb_policy

    # wb_policy= weight_balance_info(user_policy)
    #
    # print(wb_policy[0].paths)

    def avoid_node_info(self):
        '''
        :param avoid_node([A,@,D,@,H,G]！[A,B,C])
        :return:返回Policy对象('policy_name','avoid_node',[[A,@,D,@,H],[A,B,C]],proc{'protocol': Flex_Algo})  policy对象
        '''

        policy = self.get_policy()
        # print(policy)
        avoid_node_policy = []
        for i in self.main_policy_called()[1]:
            pro_dict = {'protocol': 'Flex_Algo'}
            length = int(len(i))
            # print(i)

            list1 = list(policy[i[0]])  # ['policy', 'traffic', 'waypoint', 'C', 'D']
            # print(list1)
            name = list1[1]  # extra:得到策略的name

            if 'avoid_node' in list1:
                if "True" in policy[i[0]]:
                    pro_dict = {'protocol': 'Flex_Algo', 'type': 'SRv6_LAT'}
                pn = policy[i[0]]['path_node']
                an = policy[i[0]]['avoid_node']
                result = []
                result.append(list(pn))
                result.append(list(an))
                #           #policy = SRv6_Policy(list1[1],)

                avoid_node_policy.append(Policy(name, "avoid_node", result, pro_dict))

        #
        return avoid_node_policy

    # avoid_node_policy=avoid_node_info(user_policy)
    #
    # print(avoid_node_policy[0].paths)

    def avoid_link_info(self):
        '''

        :param data:avoid_link([C,@,D,'H']![(A,B)])
        :return:返回Policy对象('policy_name','avoid_node',[[C,@,'D','H'],[(A,B)]],proc{'protocol':'SRv6_Dynamic'})  #列表第一个元素是路径，后面的是避免的链路

        '''

        policy = self.get_policy()
        # print(policy)
        avoid_link_policy = []
        for i in self.main_policy_called()[1]:
            pro_dict = {'protocol': 'SRv6_Dynamic'}
            length = int(len(i))
            # print(i)
            # print(i[length - 1])

            list1 = list(policy[i[0]])  # ['policy', 'traffic', 'waypoint', 'C', 'D']
            # print(list1)
            name = list1[0]  # extra:得到策略的name

            if 'avoid_link' in list1:
                if "True" in policy[i[0]]:
                    pro_dict = {'protocol': 'SRv6_Dynamic', 'type': 'SRv6_LAT'}
                pn = policy[i[0]]['path_link']
                an = policy[i[0]]['avoid_link']
                # print(an)
                result = []
                result.append(list(pn))
                result.append(list(an))
                #           #policy = SRv6_Policy(list1[1],)

                avoid_link_policy.append(Policy(name, "avoid_link", result, pro_dict))

        return avoid_link_policy

    # avoid_link_policy= avoid_link_info(user_policy)
    #
    # print(avoid_link_policy[0].paths)

    # constraint_policy= constraint_info(user_policy)
    #
    # print(constraint_policy[0].paths)

    def simple_info(self):
        '''
        当输入是：simple([A,B,D,E] & low_latency = True)  返回Policy对象('policy_name','simple',[A,B,D,E],proc{'protocol': ISIS,'type':SRv6_LAT})
        当输入是：simple([A,B,D,E])  返回Policy对象('policy_name','simple',[A,B,D,E],proc{'protocol': ISIS})
        :return:
        '''
        policy = self.get_policy()
        # print(policy)
        simple_policy = []
        for i in self.main_policy_called()[1]:
            pro_dict = {'protocol': 'ISIS'}
            length = int(len(i))
            # print(i)
            # print(i[length - 1])

            list1 = list(policy[i[0]])  # ['policy', 'traffic', 'waypoint', 'C', 'D']
            # print(list1)

            name = list1[0]  # extra:得到策略的name

            if 'simple' in list1:
                # print(policy[i[0]])
                if "True" in policy[i[0]]:
                    pro_dict = {'type': "SRv6_Dynamic",'Cons':"SRv6_LAT"}
                cs = policy[i[0]]['simple']

                # print(cs)
                result = []

                result.append(cs)
                #           #policy = SRv6_Policy(list1[1],)

                simple_policy.append(Policy(name, "constraint", cs, pro_dict))
                self.policy_list.append(Policy(name, "constraint", cs, pro_dict))

        return simple_policy

    def all_policy_info(self):
        all_policy_list = []
        all_policy_list.extend(self.simple_info()[0].pro_dict)
        all_policy_list.append(self.constraint_info())
        all_policy_list.append(self.avoid_link_info()[0].pro_dict)
        all_policy_list.append(self.avoid_node_info()[0].pro_dict)
        all_policy_list.append(self.waypoint_info())
        all_policy_list.append(self.bandwidth_info())
        all_policy_list.append(self.weight_balance_info())
        return all_policy_list

    def constraint_info_show(self):
        policy = self.get_policy()
        constraint_policy = []
        for i in self.main_policy_called()[1]:
            # list1 = list(policy[i[0]])  # ['policy', 'traffic', 'waypoint', 'C', 'D']
            # print(policy[i[0]])
            # i 指的是解析后的结果['p1', 'constraint', 'A', 'B', 'D', 'H', '>', 'A', 'C', 'E', 'D', 'H', '=', 'A', 'B', 'E', 'H']
            # print(i[0])  #i[0] 指的是策略名称 p1
            name = i[0]  # extra:得到策略的name

            if 'constraint' in i:
                ops = i['op']
                # print(policy[i[0]])
                cs = i['constraint']
                start = 0
                end = 0
                cs_tmp = []
                # print(i['constraint'][-1])
                while end < len(cs):
                    if cs[end] == i['constraint'][-1]:
                        cs_tmp.append(list(cs[start:end + 1]))
                        start = end + 1
                    end += 1
                # print(cs)
                result = []
                opslist = list(ops)
                result.append(list(ops))
                result.append(cs_tmp)
                #           #policy = SRv6_Policy(list1[1],)
                pro_dict = {'protocol': 'ISIS'}
                loop_ops = len(opslist)

                relations = {}
                # print(cs_tmp)  #[['A', 'B', 'D', 'H'], ['A', 'C', 'E', 'D', 'H'], ['A', 'B', 'E', 'H']]
                for i in range(loop_ops):

                    path = []
                    path2 = []
                    for j in range(len(cs_tmp[i])):
                        # print(cs_tmp[i][j])
                        path.extend(cs_tmp[i][j])
                    # print(path)
                    path = ''.join(path)
                    # print(path)
                    for z in range(len(cs_tmp[i + 1])):
                        path2.extend(cs_tmp[i + 1][z])
                    path2 = ''.join(path2)
                    relations['relation-' + str(i)] = path + ' ' + ops[i] + ' ' + path2

                # print(relations[i])

                constraint_policy.append(Policy(name, "constraint", relations, pro_dict))
                self.policy_list.append(Policy(name, "constraint", relations, pro_dict))

        return constraint_policy

    def bandwidth_info_show(self):
        '''
        :param data: bandwidth(A,H,100)
        :return: Policy('policy_name','bandwidth',[srcNode,dstNode,100],{'protocol':SRv6_explicit})
        '''

        policy = self.get_policy()
        # print(policy)
        bd_policy = []
        constraint_list = []
        for i in self.main_policy_called()[1]:
            pro_dict = {'protocol': 'SRv6_explicit'}
            length = int(len(i))
            # print(i[0])
            list1 = list(policy[i[0]])
            name = list1[0]
            if 'bandwidth' in list1:
                # constraint_list.append(list(policy[i[0]]["bandwidth"]))
                # bd_policy.append(Policy(name, "bandwidth", list(policy[i[0]]["bandwidth"]), pro_dict))
                bandwidth_guarentee = policy[i[0]]['bandwidth']
                src_node = policy[i[0]]['src']
                dst_node = policy[i[0]]['dst']
                # print(wp)

                #           #policy = SRv6_Policy(list1[1],)
                constraint = {"src": src_node[0], "dst": dst_node[0], "bandwidth_value": str(bandwidth_guarentee[0]),
                              "time": (0, 12)}
                # wp_tmp.extend(list(pn))
                # wp_tmp.extend(list(dst_node))
                # wp_tmp.append(list(pn))
                # wp_tmp.append(list(dst_node))
                bd_policy.append(Policy(name, "bandwidth", constraint, pro_dict))
                self.policy_list.append(Policy(name, "bandwidth", constraint, pro_dict))
        return bd_policy

    def avoid_node_info_show(self):
        '''
        :param avoid_node([A,@,D,@,H,G]！[A,B,C])
        :return:返回Policy对象('policy_name','avoid_node',[[A,@,D,@,H],[A,B,C]],proc{'protocol': Flex_Algo})  policy对象
        '''

        policy = self.get_policy()
        # print(policy)
        avoid_node_policy = []
        for i in self.main_policy_called()[1]:
            pro_dict = {'protocol': 'Flex_Algo'}
            length = int(len(i))
            # print(i)

            list1 = list(policy[i[0]])  # ['policy', 'traffic', 'waypoint', 'C', 'D']
            # print(list1)
            name = list1[0]  # extra:得到策略的name

            if 'avoid_node' in list1:
                if "True" in policy[i[0]]:
                    pro_dict = {'protocol': 'Flex_Algo', 'type': 'SRv6_LAT'}
                pn = policy[i[0]]['path_node']
                an = list(policy[i[0]]['avoid_node'])
                #print(an)
                constraint = { }
                constraint['src'] = pn[0]
                constraint['dst'] = pn[1]
                constraint['avoid_nodes'] = []
                if len(an) == 1:
                    constraint['avoid_nodes'] = an
                               #           #policy = SRv6_Policy(list1[1],)
                else:
                    for i in an:
                        constraint['avoid_nodes'].append(i)

                avoid_node_policy.append(Policy(name, "avoid_node",constraint , pro_dict))
                self.policy_list.append(Policy(name, "avoid_node",constraint , pro_dict))
        return avoid_node_policy


    def avoid_link_info_show(self):
        '''

        :param data:avoid_link([C,@,D,'H']![(A,B)])
        :return:返回Policy对象('policy_name','avoid_node',[[C,@,'D','H'],[(A,B)]],proc{'protocol':'SRv6_Dynamic'})  #列表第一个元素是路径，后面的是避免的链路

        '''

        policy = self.get_policy()
        # print(policy)
        avoid_link_policy = []
        for i in self.main_policy_called()[1]:
            pro_dict = {'protocol': 'SRv6_Dynamic'}
            length = int(len(i))
            # print(i)
            # print(i[length - 1])

            list1 = list(policy[i[0]])  # ['policy', 'traffic', 'waypoint', 'C', 'D']
            # print(list1)
            name = list1[0]  # extra:得到策略的name

            if 'avoid_link' in list1:
                if "True" in policy[i[0]]:
                    pro_dict = {'protocol': 'SRv6_Dynamic', 'type': 'SRv6_LAT'}
                pn = policy[i[0]]['path_link']
                an = policy[i[0]]['avoid_link']
                # print(an)
                # result = []
                # result.append(list(pn))
                # result.append(list(an))
                constraint = {}
                constraint['src'] = pn[0]
                constraint['dst'] = pn[1]
                constraint['avoid_links'] = []
                if len(an) == 1:
                    constraint['avoid_links'] = an
                    #           #policy = SRv6_Policy(list1[1],)
                else:
                    for i in range(int(len(an)/2)):
                    #    print(i)
                        link = []
                        link.append(an[2*i])
                        link.append(an[2*i+1])
                      #  print(link)
                        constraint['avoid_links'].append(link)
                    #print(an)
                       # link.append(i)
                    #constraint['avoid_links'].append(link)
                #           #policy = SRv6_Policy(list1[1],)
                avoid_link_policy.append(Policy(name, "avoid_link", constraint, pro_dict))
                self.policy_list.append(Policy(name, "avoid_link", constraint, pro_dict))
        return avoid_link_policy

    @property
    def analyze(self):
        t1 = time.time()
        t1 = int(round(t1 * 10000))
        self.constraint_info_show()
        t2 = time.time()
        t2 = int(round(t2 * 10000))
        print("intent analyze time is " + str(t2 - t1) + "ms")
        t3 = time.time()
        t3 = int(round(t3 * 10000))
        self.waypoint_info()
        t4 = time.time()
        t4 = int(round(t4 * 10000))
        print("intent analyze time is " + str(t4 - t3) + "ms")
        t5 = time.time()
        t5 = int(round(t5 * 10000))
        self.bandwidth_info_show()
        t6 = time.time()
        t6 = int(round(t6 * 10000))
        print("intent analyze time is " + str(t6 - t5) + "ms")
        t7 = time.time()
        t7 = int(round(t7 * 10000))
        self.avoid_node_info_show()
        t8 = time.time()
        t8 = int(round(t8 * 10000))
        print("intent analyze time is " + str(t8 - t7) + "ms")
        self.avoid_link_info_show()
        self.weight_balance_info()
        self.simple_info()


        # 将多行文本写入文件中
       # out_dir = os.path.dirname("policy/parse")
        list = self.policy_list
        with open('policy/parse', 'w') as f:
            for i in range(len(list)):
                f.write(str(list[i]) + '\n')

        return list

    def output(self, text):

        if self.log_signal is None:
            print(text)
        else:
            t = str(text)
            self.log_signal.emit(t)

result = read_policy()

list = result.analyze
print(len(list))
for i in range(len(list)):

    print(list[i])

