#!/usr/bin/env python
# -*- coding: utf-8 -*-
'''
BGP域之间(指定设备)EBGP关系—peer参数[接口IP]+as-number
同一个域里PE设备之间建立MP-IBGP关系[设备IP]
BGP引入SRv6-TE Policy，SRv6 Policy发布给EBGP对等体
固定配置

Input: 生成的policy
Output:各个BGP domain之间互通需要的peer参数 分配的as-number

@Project ：SRv6CS 
@File ：BGP_synthesis.py
@Date ：2022/7/19 15:04 ISIS_synthesis.py
'''

def BGP_conf(topo, policy_list):
    opcode_change_state = 1
    for node in topo.nodes:
        if node['type'] == 'PE':
            for nbr in topo.neighbors(node):
                node['opcode'] = str(opcode_change_state)
                opcode_change_state += 1
    for policy in policy_list:
        topo.nodes[policy.Head]['color'] = policy.Color





