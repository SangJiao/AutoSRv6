#!/usr/bin/env python
# -*- coding: utf-8 -*-
'''
合成接口IPv6地址+前缀长度
还有设备+ Loop(IPv6地址)
给每个节点和链路分配SID (节点End.SID,链路End.x SID)
更新网络拓扑信息
@Project ：AutoSRv6 
@File ：topo_complete.py
@Date ：2022/7/19 15:51 
'''
from IPy import IP
import networkx as nx
import utils

def set_interface_ipv6(topo):
    assert (isinstance(topo, nx.DiGraph))
    loop_sid_ipv6_change_state = 1
    for node in topo.nodes:
        node[utils.keyword.IP] = IP('2001:DD8:'+str(hex(loop_sid_ipv6_change_state)[2:]).upper()+'::1/128')
        node[utils.keyword.PREFIX_SID] = IP('2001:DA8:'+str(hex(loop_sid_ipv6_change_state)[2:]).upper()+'::1/128')
        loop_sid_ipv6_change_state += 1
    dir = {}
    inter_ipv6_change_state = 1
    xsid_ipv6_change_state = 1
    for edge in topo.edges:
        if edge not in dir.keys():
            edge[utils.keyword.INTERFACE] = IP('2001:DB8:'+str(hex(inter_ipv6_change_state)[2:]).upper()+'::1/64')
            tem1 = (edge[1], edge[0])
            dir[tem1] = IP('2001:DB8:'+str(hex(inter_ipv6_change_state)[2:]).upper()+'::2/64')
            inter_ipv6_change_state += 1
        else:
            edge[utils.keyword.INTERFACE] = dir[edge]
        edge[utils.keyword.ADJ_SID] = IP('2001:D08:'+str(hex(xsid_ipv6_change_state)[2:]).upper()+'::1/128')
        xsid_ipv6_change_state += 1