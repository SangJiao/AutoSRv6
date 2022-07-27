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
from utils import keyword

i = IP('2001:DB8:1::1/128')
def set_interface_ipv6(topo):
    assert (isinstance(topo, nx.DiGraph))
    loop_sid_ipv6_change_state = 1
    for node in topo.nodes:
        topo.nodes[node][keyword.IP] = IP("2001:DD8:"+hex(loop_sid_ipv6_change_state).upper()+"::1/128")
        topo.nodes[node][keyword.PREFIX_SID] = IP('2001:DA8:'+hex(loop_sid_ipv6_change_state)[2:].upper()+'::1/128')
        loop_sid_ipv6_change_state += 1
    dir = {}
    inter_ipv6_change_state = 1
    xsid_ipv6_change_state = 1
    for edge in topo.edges:#(A,B)
        if edge not in dir.keys():
            topo.edges[edge][keyword.INTERFACE] = IP('2001:DB8:'+hex(inter_ipv6_change_state)[2:].upper()+'::1')  #(A,B)    A_INTERFACE[]
            topo.edges[edge]['mask'] = 64
            tem1 = (edge[1], edge[0]) #(B,A)
            # topo.edges[edge][keyword.INTERFACE] = IP('2001:DB8:' + hex(inter_ipv6_change_state)[2:].upper() + '::2')
            dir[tem1] = IP('2001:DB8:'+hex(inter_ipv6_change_state)[2:].upper()+'::2')
            inter_ipv6_change_state += 1
        else:
            topo.edges[edge][keyword.INTERFACE] = dir[edge]
            topo.edges[edge]['mask'] = 64
        topo.edges[edge][keyword.ADJ_SID] = IP('2001:D08:'+str(hex(xsid_ipv6_change_state)[2:]).upper()+'::1/128')
        xsid_ipv6_change_state += 1