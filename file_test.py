#!/usr/bin/env python
# -*- coding: utf-8 -*-
'''
@Project ：AutoSRv6 
@File ：file_test.py
@Author ：Lucky
@Date ：2023/4/1 17:08 
'''
from pyparsing import *
from Policy import *

integer = Word(nums)
id = Word(srange("[a-zA-Z_]"), srange("[a-zA-Z0-9_-]"))
element = Word(srange("[0-9a-fA-F]"))
op = Word(srange("[>=-]:"))
ip_subnet = Combine(element - (':' + element) * 7)("address") + "/" + integer("num")
ip = ("ip" + ip_subnet("subnet"))
p_waypoint = Word("waypoint") + Suppress("(") + Suppress("[") + \
             id("p_node*") + Suppress(",") + id("dst_node*")[0, ...] + Suppress("]") \
             + Suppress("@") + Suppress("[") + id("waypoint*") + \
             (Suppress(",") + id("waypoint*"))[0, ...] \
             + Suppress("]") + Suppress(")")

p_path = id("node*") + (Suppress("-") + id("node*"))[0, ...]

p_constraint = Word("constraint") + Suppress("(") + \
               id("constraint*") + (Suppress(",") + id("constraint*"))[0, ...] + \
               (op("op*") + id("constraint*") + (Suppress(",") + id("constraint*"))[
                   0, ...])[0, ...] \
               + Suppress(")")

# weight_balance()
p_weight_balance = Word("weight_balance") + Suppress("(") + \
                   id("weight_balance*") + (Suppress(",") + id("weight_balance*"))[0, ...] \
                   + (Suppress(":") + id("weight_balance*") +
                      (Suppress(",") + id("weight_balance*"))[0, ...])[0, ...] \
                   + Suppress("=") + integer("weight*") + (Suppress(":") + integer("weight*"))[
                       0, ...] + Suppress(")")

# avoid_node()
p_avoid_node = Word("avoid_node") + Suppress("(") + \
               Suppress("[") + id("path_node*") + (Suppress(",") + id("path_node*"))[
                   0, ...] + Suppress("]") \
               + Suppress("!") + Suppress("[") + id("avoid_node*") + \
               (Suppress(",") + id("avoid_node*"))[0, ...] \
               + Suppress("]") + \
               (Suppress("&") + id("low_latency") + Suppress("=") + id("True"))[
                   0, ...] + Suppress(")")
# avoid_link()
p_avoid_link = Word("avoid_link") + Suppress("(") + \
               Suppress("[") + id("path_link*") + (Suppress(",") + id("path_link*"))[
                   0, ...] + Suppress("]") \
               + Suppress("!") + Suppress("[") + Suppress("(") + id("avoid_link*") + \
               (Suppress(",") + id("avoid_link*"))[0, ...] \
               + Suppress(")") + (Suppress(",") + Suppress("(") + id("avoid_link*") +
                                  (Suppress(",") + id("avoid_link*"))[0, ...] \
                                  + Suppress(")"))[0, ...] + Suppress("]") + \
               (Suppress("&") + id("low_latency") + Suppress("=") + id("True"))[0, ...] + \
               Suppress(")")
# low_latency()
p_simple = Word("simple") + Suppress("(") + Suppress("[") + id("simple*") + \
           (Suppress(",") + id("simple*"))[0, ...] + Suppress("]") + \
           (Suppress("&") + id("low_latency") + Suppress("=") + id("True"))[0, ...] \
           + Suppress(")")
# bandwidth = integer("bandwidth*")
# p_bandwidth = Word("bandwidth") + Suppress("(") + id("bandwidth*") + (Suppress(",")
#                                                                                         + id("bandwidth*"))[
#             0, ...] + Suppress(",") + bandwidth + Suppress(")")
# p_bandwidth = Word("bandwidth") + Suppress("(") + \
#                    id("src*") + Suppress(",") + id("dst*") + Suppress(",") \
#                    + id("bandwidth*") + Suppress(")")
p_bandwidth = Word("bandwidth") + Suppress("(") + id("src*") + Suppress(",") + id("dst*") + Suppress(",") + integer(
    "bandwidth*") + Suppress(")")

def_policy = id("policy_name") + Suppress(":") + \
             ((p_bandwidth[..., 1]) & (p_avoid_link[..., 1]) & (p_constraint[..., 1]) & (
                 p_simple[..., 1]) &
              (p_waypoint[..., 1]) & (p_avoid_node[..., 1]) & (
                  p_weight_balance[..., 1])) + Suppress(";")

def_main = Suppress("main") + Suppress("{") + \
           (Group(def_policy)[...]) + \
           Suppress("}")
with open(r'./policy/new_policy', 'r') as file:
    data = file.read()


# print(data)
# print("~~~~~~~~~~~~~~~~~~~~~~~~~~~~~")
# print(def_policy.searchString(data))
# print('!!!!!!!!!!!!!!!!!!!!!!')
# print(def_main.searchString(data))
def get_policy():
    '''
    # 所有定义的策略集
    # 返回一个记录所有定义的策略集的字典，键为策略集名字，值为策略集具体信息
    :param data:
    :return: policy_dict
    '''
    policy_dict = {}
    for po in (def_policy.searchString(data)):
        policy_dict[po["policy_name"]] = po
    # print(policy_dict.keys())
    # print("\n")
    # print(policy_dict.values())
    # print("\n")
    # print("****************************************")
    return policy_dict


# get_policy(user_policy)

# 主函数调用策略
d = def_main.searchString(data)
print(def_main.searchString(data))
print()

global_list = []
for i in sum(d):
    global_list.append(i)
# print("1111111111111")
# print(def_main.searchString(data))

# def main_policy_called():
#     g = []  # 全局策略
#     for m in sum(d):
#         g.append(m)
#     return g


# 返回一个二维list记录带宽约束信息
def waypoint_info():
    '''
        :param data:  waypoint([A,H]@[B,C])
        :return: # Policy('policy_name','waypoint',[srcNode,dstNode,[waypoint]],{'protocol':SRv6_explicit})
        '''

    policy = get_policy()
    # print(policy)
    wp_policy = []
    for i in global_list:
        pro_dict = {'protocol': 'SRv6_explicit'}
        length = int(len(i))

        list1 = list(policy[i[0]])  # ['policy', 'traffic', 'waypoint', 'C', 'D']
        # print(list1)
        name = list1[0]  # extra:得到策略的name

        if 'waypoint' in list1:
            print("。。。。。。。。。。。。")
            print(i)
            print("。。。。。。。。。。。。")
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

    #
    return wp_policy


def bandwidth_info():
    '''
        :param data: bandwidth(A,H,100)
        :return: Policy('policy_name','bandwidth',[srcNode,dstNode,100],{'protocol':SRv6_explicit})
        '''

    policy = get_policy()
    # print(policy)
    bd_policy = []
    constraint_list = []
    for i in global_list:
        pro_dict = {'protocol': 'SRv6_explicit'}
        length = int(len(i))
        # print(i[0])
        list1 = list(policy[i[0]])
        name = list1[0]
        if 'bandwidth' in list1:
            # print("。。。。。。。。。。。。")
            # print(i)
            # print("。。。。。。。。。。。。")
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

            #print(Policy(name, "bandwidth", constraint, pro_dict))
    return bd_policy


# class BandWidth(object):
#     def __init__(self, src, dst, bandwidth_value):
#         self.src = src
#         self.dst = dst
#         self.bandwidth = bandwidth_value
#         # if time is None:
#         #     self.time = (0, 12)
#         # else:
#         #     self.time = time
#
#         self.time = "(0,12)"
#
#     def __str__(self):
#         s = 'src: ' + self.src + "\n" + \
#             'dst: ' + self.dst + "\n" + \
#             'dst: ' + self.dst + "\n" + \
#             'bandwidth_guarantee:' + str(self.bandwidth) + \
#             'time: ' + str((0, 12)) + "\n"
#
#         return s

#    'time:' + self.time


# class Constraint(object):
#     def __init__(self, name, classify, paths):
#         self.src = name
#         self.dst = classify
#         self.waypoints = paths
#
#     def __str__(self):
#         s = 'src: ' + self.src + "\n" + \
#             'dst: ' + self.dst + "\n" + \
#             'waypoints:' + str(self.waypoints) + "\n"
#
#         return s


print(waypoint_info()[0])
sum = 0
#print(bandwidth_info()[0])

#print(bandwidth_info()[1])
print(bandwidth_info()[0:])
for i in bandwidth_info():
    print(i)