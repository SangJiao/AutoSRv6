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
from utils.keyword import ENDX_SID, ENDXOPCODE

i = IP('2001:DB8:1::1/128')
def set_interface_ipv6(topo):
    assert (isinstance(topo, nx.DiGraph))
    loop_sid_ipv6_change_state = 1
    for node in topo.nodes:
        topo.nodes[node][keyword.LOOPBACK1] = IP("2001:DD8:"+hex(loop_sid_ipv6_change_state).upper()+"::1/128")
        topo.nodes[node][keyword.ENDX_PREFIX] = IP("2001:D08:"+hex(loop_sid_ipv6_change_state).upper()+"::1/128")
        topo.nodes[node][keyword.PREFIX_SID] = IP('2001:DA8:'+hex(loop_sid_ipv6_change_state)[2:].upper()+'::1/128')
        topo.edges[node]['network-entity'] = "10.0000.0000."+int2str(loop_sid_ipv6_change_state)+".00"
        loop_sid_ipv6_change_state += 1
        #给节点添加End.x SID的前缀,边加上opcode，# to字符串需要改为IP地址
        i = 0
        for n in topo.neighbors(node):
                i += 1
                edge = (node,n)
                topo.edges[edge][ENDXOPCODE] = i
                topo.edges[edge][ENDX_SID] = IP(topo.nodes[node][keyword.ENDX_PREFIX].make_net(64)[0].strCompressed() + str(i) + "/128") # to字符串需要改为IP地址！！！！！！！！！！！！！！！！！！！！！！！！！！！！
    dir = {}
    xsid_dir = {}
    inter_xsid_ipv6_change_state = 1
    for edge in topo.edges:#(A,B)

        if edge not in dir.keys():
            topo.edges[edge][keyword.INTERFACE] = IP('2001:DB8:'+hex(inter_xsid_ipv6_change_state)[2:].upper()+'::1')  #(A,B)    A_INTERFACE[]
            topo.edges[edge]['mask'] = 64
            topo.edges[edge][keyword.ADJ_SID] = IP('2001:D08:'+hex(inter_xsid_ipv6_change_state)[2:].upper()+'::1/128')
            tem1 = (edge[1], edge[0]) #(B,A)
            # topo.edges[edge][keyword.INTERFACE] = IP('2001:DB8:' + hex(inter_ipv6_change_state)[2:].upper() + '::2')
            dir[tem1] = IP('2001:DB8:'+hex(inter_xsid_ipv6_change_state)[2:].upper()+'::2')
            xsid_dir[tem1] = IP('2001:D08:'+hex(inter_xsid_ipv6_change_state)[2:].upper()+'::2/128')
            inter_xsid_ipv6_change_state += 1
        else:
            topo.edges[edge][keyword.INTERFACE] = dir[edge]
            topo.edges[edge]['mask'] = 64
            topo.edges[edge][keyword.ADJ_SID] = xsid_dir[edge]
        # topo.edges[edge][keyword.ADJ_SID] = IP('2001:D08:'+str(hex(xsid_ipv6_change_state)[2:]).upper()+'::1/128')
        # xsid_ipv6_change_state += 1


def int2str(i):
    return "0"*(4-len(str(i)))+str(i)