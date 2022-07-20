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

# 通用匹配模式
integer = Word(nums)
id = Word(srange("[a-zA-Z_]"), srange("[a-zA-Z0-9_-]"))
element = Word(srange("[0-9a-fA-F]"))
ip_subnet = Combine(element - (':' + element) * 7)("address") + "/" + integer("num")
ip = ("ip" + ip_subnet("subnet"))

# ip前缀匹配模式
# prefix pre1 {AD80:0000:0000:0000:ABAA:0000:00C2:0002 / 128}
def_ipprefix = Word("prefix") + id("name") + Suppress("{") + ip_subnet("ip") + Suppress("}")

# 带宽约束
bandwidth = integer("bandwidth")
p_bandwidth = Word("bandwidth") + bandwidth + Suppress(";")

# 陆航点
# waypoint ()
p_waypoint = Word("waypoint") + Suppress("(") + \
             id("waypoint*") + (Suppress(",") + id("waypoint*"))[0, ...] + Suppress(")")

#等价路径
p_balance = Word("balance")+ Suppress("(") + \
            id("node*") + (Suppress("-") + id("node*") )[0, ...] + \
            (Suppress("=") + id("node*") + (Suppress("-") + id("node*") )[0, ...])[0, ...] + Suppress(")")


#weight_balance()

#sequence()

#avoid_node()

#avoid_link()

#low_latency()

# disjoint()

# 总定义
def_policy = "policy" + id("policy_name") + Suppress("{") + \
             ( (p_balance[..., 1]) & (p_bandwidth[..., 1]) & (
                 p_waypoint[..., 1])) + \
             Suppress("}")


# 主函数匹配模式
# A -> H apply traffic; # [['A'],['E'],['C','G']]

main_direction_schema = id("name1") + Suppress("->") + id("name2") + Suppress("apply") + id(
    "policy_name*") + Suppress(";")
def_main = Suppress("main") + Suppress("{") + \
           ( Group(main_direction_schema)[...]) + \
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
        policy_dict[po["policy_name"]] = po
    print(policy_dict.keys())
    print(policy_dict.values())
    return policy_dict
with open(r'./policy/test_policy', 'r') as file:
    user_policy = file.read()

get_policy(user_policy)

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
# [['CE6', 'CE5', 2000], ['CE8', 'CE9', 2000]]
def bandwidth_info(data):
    bd_list = []
    policy = get_policy(data)
    for i in main_policy_called(data)[1]:
        length = int(len(i))
        list1 = list(policy[i[length - 1]])
        if 'bandwidth' in list1:
            bd_list.append([i["name1"], i["name2"], int(policy[i[length - 1]]["bandwidth"])])
    return bd_list



def waypoint_info(data):
    '''
    :param data: policy traffic{waypoint (LSW11; prefix pre1,pre2;)}
    :return: # 返回一个一维list记录陆航信息 # ['A', 'H', ['C']]
    '''
    wp_list = []
    policy = get_policy(data)
    for i in main_policy_called(data)[1]:
        length = int(len(i))
        list1 = list(policy[i[length - 1]])
        if 'waypoint' in list1:
            wp = policy[i[length - 1]]["waypoint"]
                # print(ipprefix_dict[j].ip_address)
                # print(ipprefix_dict[j].prefix_len)
            wp_list.append([i["name1"], i["name2"], list(wp)])

    return wp_list

def balance_info(data):
    '''

    :param data: (A-B-D-H = A-C-E-D-H)
    dict_keys(['p1', 'traffic'])
    dict_values([ParseResults(['policy', 'p1', 'balance', 'A-B-D-H', 'A-C-E-D-H'], {'policy_name': 'p1', 'node': ['A-B-D-H', 'A-C-E-D-H']})
    :return: [[A,B,D,H],[A,C,E,D,H]]
    '''
    bal_list = []
    policy = get_policy(data)
    print(policy)
