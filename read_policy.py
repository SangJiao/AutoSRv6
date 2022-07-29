#!/usr/bin/env python

# -*- coding: utf-8 -*-

'''
读取策略文件并解析成Policy五元组
使用PLY编写的词法与语法
Input：策略文件*2
Output：
@Project ：AutoSRv6
@File ：read_policy.py
@Date ：2022/7/19 15:51
'''

from pyparsing import *
from Policy import *


class read_policy(object):

    def __init__(self):

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

        self.bandwidth = self.integer("bandwidth*")
        self.p_bandwidth = Word("bandwidth") + Suppress("(") + self.id("bandwidth*") + (Suppress(",")
                                                                                        + self.id("bandwidth*"))[
            0, ...] + Suppress(",") + self.bandwidth + Suppress(")")

        # waypoint (C,D)

        self.p_waypoint = Word("waypoint") + Suppress("(") + Suppress("[") + \
                          self.id("p_node*") + (Suppress(",") + self.id("p_node*"))[0, ...] + Suppress("]") \
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
        # print(policy_dict.values())
        return policy_dict

    # get_policy(user_policy)

    # 主函数调用策略

    def main_policy_called(self):
        global_plist = []  # 全局策略
        group_plist = []  # 多个用户组参与的策略
        direction_plist = []  # 方向性策略
        # print(self.data)

        for i in sum(self.def_main.searchString(self.data)):
            if len(i) == 1:
                global_plist.append(i)
            else:
                group_plist.append(i)
        return global_plist, group_plist, direction_plist

    # 返回一个二维list记录带宽约束信息

    # ['CE6', 'CE5', 2000]

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
            name = list1[1]
            if 'bandwidth' in list1:
                constraint_list.append(list(policy[i[0]]["bandwidth"]))
                bd_policy.append(Policy(name, "bandwidth", list(policy[i[0]]["bandwidth"]), pro_dict))
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
            name = list1[1]  # extra:得到策略的name

            if 'waypoint' in list1:
                wp = policy[i[0]]['waypoint']
                pn = policy[i[0]]['p_node']
                # print(wp)

                #           #policy = SRv6_Policy(list1[1],)

                wp_tmp = []
                wp_tmp.append(list(pn))
                wp_tmp.append(list(wp))
                wp_policy.append(Policy(name, "waypoint", wp_tmp, pro_dict))

        #
        return wp_policy

    # wp_list = waypoint_info(user_policy)
    #
    # print(wp_list[0].paths)

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
            name = list1[1]  # extra:得到策略的name

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
            name = list1[1]  # extra:得到策略的name

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

            name = list1[1]  # extra:得到策略的name

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

            name = list1[1]  # extra:得到策略的name

            if 'simple' in list1:
                # print(policy[i[0]])
                if "True" in policy[i[0]]:
                    pro_dict = {'protocol': ISIS, 'type': SRv6_LAT}
                cs = policy[i[0]]['simple']

                # print(cs)
                result = []

                result.append(cs)
                #           #policy = SRv6_Policy(list1[1],)

                simple_policy.append(Policy(name, "constraint", result, pro_dict))

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


result = read_policy()
print(result.all_policy_info())
print(read_policy().avoid_node_info()[0])
# for i in result.all_policy_info():
#     assert isinstance(i,Policy)
#     print(i)