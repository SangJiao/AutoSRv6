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

# 通用匹配模式

integer = Word(nums)
id = Word(srange("[a-zA-Z_]"), srange("[a-zA-Z0-9_-]"))
element = Word(srange("[0-9a-fA-F]"))
op = Word(srange("[>=-]"))
ip_subnet = Combine(element - (':' + element) * 7)("address") + "/" + integer("num")
ip = ("ip" + ip_subnet("subnet"))

# ip前缀匹配模式

# prefix pre1 {AD80:0000:0000:0000:ABAA:0000:00C2:0002 / 128}

def_ipprefix = Word("prefix") + id("name") + Suppress("{") + ip_subnet("ip") + Suppress("}")

# 带宽约束

bandwidth = integer("bandwidth*")
p_bandwidth = Word("bandwidth") + Suppress("(") + id("bandwidth*") + (Suppress(",") \
                                                                      + id("bandwidth*"))[0, ...] + Suppress(
    ",") + bandwidth + Suppress(")")

# waypoint (C,D)

p_waypoint = Word("waypoint") + Suppress("(") + Suppress("[") + \
             id("p_node*") + (Suppress(",") + id("p_node*"))[0, ...] + Suppress("]") \
             + Suppress("@") + Suppress("[") + id("waypoint*") + (Suppress(",") + id("waypoint*"))[0, ...] \
             + Suppress("]") + Suppress(")")

p_path = id("node*") + (Suppress("-") + id("node*"))[0, ...]

p_constraint = Word("constraint") + Suppress("(") + \
               id("constraint*") + (Suppress(",") + id("constraint*"))[0, ...] + \
               (op("op*") + id("constraint*") + (Suppress(",") + id("constraint*"))[0, ...])[0, ...] \
               + Suppress(")")

# weight_balance()
p_weight_balance = Word("weight_balance") + Suppress("(") + \
                   id("weight_balance*") + (Suppress(",") + id("weight_balance*"))[0, ...] \
                   + (Suppress(":") + id("weight_balance*") + (Suppress(",") + id("weight_balance*"))[0, ...])[0, ...] \
                   + Suppress("=") + integer("weight*") + (Suppress(":") + integer("weight*"))[0, ...] + Suppress(")")

# avoid_node()
p_avoid_node = Word("avoid_node") + Suppress("(") + \
               Suppress("[") + id("path_node*") + (Suppress(",") + id("path_node*"))[0, ...] + Suppress("]") \
               + Suppress("!") + Suppress("[") + id("avoid_node*") + (Suppress(",") + id("avoid_node*"))[0, ...] \
               + Suppress("]") + Suppress(")")
# avoid_link()
p_avoid_link = Word("avoid_link") + Suppress("(") + \
               Suppress("[") + id("path_link*") + (Suppress(",") + id("path_link*"))[0, ...] + Suppress("]") \
               + Suppress("!") + Suppress("[") + id("avoid_link*") + (Suppress(",") + id("avoid_link*"))[0, ...] \
               + Suppress("]") + Suppress(")")
# low_latency()
p_low_latency = Word("sequence") + Suppress("(") + \
                Suppress(")")

# 总定义

def_policy = "policy" + id("policy_name") + Suppress("{") + \
             ((p_bandwidth[..., 1]) & (p_avoid_link[..., 1]) & (p_constraint[..., 1]) &
              (p_waypoint[..., 1]) & (p_avoid_node[..., 1]) & (p_weight_balance[..., 1])) + Suppress("}")

# & ( p_low_latency[..., 1])& ( p_disjoint[..., 1])) + \


# 主函数匹配模式

# A -> H apply traffic; # [['A'],['E'],['C','G']]

main_direction_schema = id("name1") + Suppress("->") + id("name2") + Suppress("apply") + id(
    "policy_name*") + Suppress(";")
def_main = Suppress("main") + Suppress("{") + \
           (Group(main_direction_schema)[...]) + \
           Suppress("}")


def get_policy(data):
    '''
    # 所有定义的策略集
    # 返回一个记录所有定义的策略集的字典，键为策略集名字，值为策略集具体信息
    :param data:
    :return: policy_dict
    '''
    policy_dict = {}
    for po in def_policy.searchString(data):
        # print(po)
        policy_dict[po["policy_name"]] = po
    # print(policy_dict.keys())
    # print(policy_dict.values())
    return policy_dict





# get_policy(user_policy)

# 主函数调用策略

def main_policy_called(data):
    global_plist = []  # 全局策略
    group_plist = []  # 多个用户组参与的策略
    direction_plist = []  # 方向性策略
    for i in sum(def_main.searchString(data)):
        if len(i) == 1:
            global_plist.append(i)
        else:
            group_plist.append(i)
    return global_plist, group_plist, direction_plist


# 返回一个二维list记录带宽约束信息

# ['CE6', 'CE5', 2000]

def bandwidth_info(data):
    '''
    :param data: bandwidth([A,H,100],[])
    :return: Policy('policy_name','bandwidth',[[srcNode,dstNode,100],[srcNode,dstNode,200],{'protocol':SRv6_explicit})
    '''
    bd_list = []
    policy = get_policy(data)
    # print(policy)
    for i in main_policy_called(data)[1]:
        pro_dict = {'type': 'SRv6'}
        length = int(len(i))
        list1 = list(policy[i[length - 1]])
        name = list1[1]
        bd_policy = []
        constraint_path = []
        if 'bandwidth' in list1:
            bd_list.append([i["name1"], i["name2"], list(policy[i[length - 1]]["bandwidth"])])

            constraint_path.append(list(policy[i[length - 1]]["bandwidth"]))
            bd_policy.append(Policy(name, "bandwidth", list(policy[i[length - 1]]["bandwidth"]), pro_dict))
    return bd_policy,


# bd_list=bandwidth_info(user_policy)

# print(bd_list[0].name)

def waypoint_info(data):
    '''
    :param data:  waypoint([A,H]@[B,C],)
    :return: # Policy('policy_name','waypoint',[srcNode,dstNode,[waypoint]],{'protocol':SRv6_explicit})
    '''
    wp_list = []
    policy = get_policy(data)
    # print(policy)
    for i in main_policy_called(data)[1]:
        pro_dict = {'type': 'SRv6'}
        length = int(len(i))

        list1 = list(policy[i[length - 1]])  # ['policy', 'traffic', 'waypoint', 'C', 'D']
        # print(list1)
        name = list1[1]  # extra:得到策略的name
        if 'waypoint' in list1:
            wp = policy[i[length - 1]]['waypoint']
            # print(wp)

            #           #policy = SRv6_Policy(list1[1],)

            wp_tmp = []
            wp_tmp.append(i["name1"])
            wp_tmp.append(i["name2"])
            wp_tmp.append(list(wp))
            wp_list.append([name, pro_dict, i["name1"], i["name2"], wp_tmp])
            wp_policy = []
            wp_policy.append(Policy(name, "waypoint", wp_tmp, pro_dict))
    print('-----------------')
    print(wp_list)

    #
    return wp_policy


# wp_list = waypoint_info(user_policy)

# print(wp_list[0].paths)
def lowlatency_info(data):
    '''
    :param data:lowlatency_info(A,H)
    :return:Policy('policy_name','weight_balance',[[1,2,3],[A,D,H],[A,E,D,H],[A,G,H]],{'protocol':SRv6_explicit})
    '''




def weight_balance_info(data):
    '''
    :param data:weight_balance(A,D,H : A,E,D,H : A,G,H = 1 : 2 : 3 )
    :return:Policy('policy_name','weight_balance',[[1,2,3],[A,D,H],[A,E,D,H],[A,G,H]],{'protocol':SRv6_explicit})
    '''
    wb_list = []
    policy = get_policy(data)
    # print(policy)
    for i in main_policy_called(data)[1]:
        pro_dict = {'type': 'SRv6'}
        length = int(len(i))
        # print(i)
        list1 = list(policy[i[length - 1]])  # ['policy', 'traffic', 'waypoint', 'C', 'D']
        # print(list1)
        name = list1[1]  # extra:得到策略的name
        if 'weight_balance' in list1:
            # print(policy)
            # print(i[length - 1])
            wb = policy[i[length - 1]]['weight_balance']
            print(wb)
            start = 0
            end = 0
            wb_tmp = []
            wb_tmp.append(list(policy[i[length - 1]]['weight']))
            while end < len(wb):
                if wb[end] == i["name2"]:
                    wb_tmp.append(list(wb[start:end + 1]))
                    start = end + 1
                end += 1

            # print(wb_tmp)
            #           #policy = SRv6_Policy(list1[1],)
            wb_list.append([name, pro_dict, i["name1"], i["name2"], wb_tmp])
            wb_policy = []
            wb_policy.append(Policy(name, "weight_balance", wb_tmp, pro_dict))
    print('-----------------')
    print(wb_list)
    return wb_policy


# wb_policy= weight_balance_info(user_policy)

# print(wb_policy[0].paths)


def avoid_node_info(data):
    '''
    :param avoid_node([A,@,D,@,H,G]！[A,B,C] & low_latency = True)
    :return:返回Policy对象('policy_name','avoid_node',[[A,@,D,@,H],[A,B,C]],proc{'protocol': Flex_Algo,'type':SRv6_LAT})  policy对象
    '''
    an_list = []
    policy = get_policy(data)
    # print(policy)
    for i in main_policy_called(data)[1]:
        pro_dict = {'type': 'SRv6'}
        length = int(len(i))
        # print(i)

        list1 = list(policy[i[length - 1]])  # ['policy', 'traffic', 'waypoint', 'C', 'D']
        # print(list1)
        name = list1[1]  # extra:得到策略的name
        if 'avoid_node' in list1:
            pn = policy[i[length - 1]]['path_node']
            an = policy[i[length - 1]]['avoid_node']
            result = []
            result.append(list(pn))
            result.append(list(an))
            #           #policy = SRv6_Policy(list1[1],)
            an_list.append([name, pro_dict, i["name1"], i["name2"], result])
            avoid_node_policy = []
            avoid_node_policy.append(Policy(name, "avoid_node", result, pro_dict))
    print('-----------------')
    print(an_list)

    #
    return avoid_node_policy


# avoid_node_policy=avoid_node_info(user_policy)

# print(avoid_node_policy[0].paths)

def avoid_link_info(data):
    '''

    :param data:avoid_link([C,@,D,'H']![(A,B)])
    :return:返回Policy对象('policy_name','avoid_node',[[C,@,'D','H'],[(A,B)]],proc{'protocol':'SRv6_Dynamic'})  #列表第一个元素是路径，后面的是避免的链路

    '''
    an_list = []
    policy = get_policy(data)
    # print(policy)
    for i in main_policy_called(data)[1]:
        pro_dict = {'type': 'SRv6'}
        length = int(len(i))
        # print(i)
        # print(i[length - 1])

        list1 = list(policy[i[length - 1]])  # ['policy', 'traffic', 'waypoint', 'C', 'D']
        # print(list1)
        name = list1[1]  # extra:得到策略的name
        if 'avoid_link' in list1:
            pn = policy[i[length - 1]]['path_link']
            an = policy[i[length - 1]]['avoid_link']
            # print(an)
            result = []
            result.append(list(pn))
            result.append(list(an))
            #           #policy = SRv6_Policy(list1[1],)
            an_list.append([name, pro_dict, i["name1"], i["name2"], result])
            avoid_link_policy = []
            avoid_link_policy.append(Policy(name, "avoid_link", result, pro_dict))
    print('-----------------')
    print(an_list)

    return avoid_link_policy


# avoid_link_policy= avoid_link_info(user_policy)

# print(avoid_link_policy[0].paths)

def constraint_info(data):
    cs_list = []
    policy = get_policy(data)
    # print(policy)
    for i in main_policy_called(data)[1]:
        pro_dict = {'type': 'SRv6'}
        length = int(len(i))
        # print(i)
        # print(i[length - 1])

        list1 = list(policy[i[length - 1]])  # ['policy', 'traffic', 'waypoint', 'C', 'D']
        # print(list1)

        name = list1[1]  # extra:得到策略的name
        if 'constraint' in list1:
            ops = policy[i[length - 1]]['op']
            cs = policy[i[length - 1]]['constraint']
            start = 0
            end = 0
            cs_tmp = []
            while end < len(cs):
                if cs[end] == i["name2"]:
                    cs_tmp.append(list(cs[start:end + 1]))
                    start = end + 1
                end += 1
            # print(cs)
            result = []
            result.append(list(ops))
            result.append(cs_tmp)
            #           #policy = SRv6_Policy(list1[1],)
            cs_list.append([name, pro_dict, i["name1"], i["name2"], result])
            constraint_policy = []
            constraint_policy.append(Policy(name, "constraint", result, pro_dict))
    print('-----------------')
    print(cs_list)

    return constraint_policy

# constraint_policy= constraint_info(user_policy)

# print(constraint_policy[0].paths)