#!/usr/bin/env python
# -*- coding: utf-8 -*-
'''
配置模板
@Project ：AutoSRv6
@File ：template.py
@Date ：2022/7/19 15:06
'''
from read_topo import Topo
from topo_complete import set_interface_ipv6
from utils import keyword
from IPy import IP

def BGP_conf(topo):
    bgp_contain_nodes_dir = {}
    for node_name in topo.nodes:
        node = topo.nodes[node_name]
        if node['bgp_domain'] not in bgp_contain_nodes_dir:
            bgp_contain_nodes_dir[node['bgp_domain']] = []
        bgp_contain_nodes_dir[node['bgp_domain']].append(node)

    configs = {}
    for node_name in topo.nodes:
        node = topo.nodes[node_name]
        config = ''
        # todo peer 相邻节点的peer处理，
        if node['type'] == 'PE' or node['type'] == 'P':
            config += 'segment-routing ipv6\n'
            config += ' locator {0} ipv6-prefix {1} 64 static 32\n'.format(node_name, node[keyword.PREFIX_SID].make_net(64)[0].strCompressed())
            config += '  opcode 1 end-dt6\n'  # TODO topo_complete里prefix_sid分配的默认为1

            config += 'bgp {}\n'.format(node['bgp_domain'])
            for peer in bgp_contain_nodes_dir[node['bgp_domain']]:
                if peer != node:
                    config += ' peer {0} as-number {1}\n'.format(peer[keyword.PREFIX_SID].strCompressed(), peer['bgp_domain'])
                    if peer['type'] == 'PE':
                        config += ' peer {0} as-number connect-interface Loopback1]\n'  # TODO 现在先默认是loopback1，看后续是否需要修改
            config += ' #\n'

            config += ' address-family ipv6 unicast\n'
            config += '  segment-routing ipv6 locator {0}\n'.format(node_name)
            for peer in bgp_contain_nodes_dir[node['bgp_domain']]:
                if peer != node:
                    config += '  peer {0} enable\n'.format(peer[keyword.PREFIX_SID])
                    config += '  peer {0} prefix-sid\n'.format(peer[keyword.PREFIX_SID])
                    config += '  network 64\n'  # TODO 默认64
            config += '  segment-routing ipv6 locator {0}\n'.format(node_name)
            config += '  segment-routing ipv6 traffic-engineer\n'

            for peer in bgp_contain_nodes_dir[node['bgp_domain']]:
                if peer != node:
                    config += '  peer {0} route-policy color export\n'.format(peer[keyword.IP])
                    config += '  peer {0} advertise-ext-community\n'.format(peer[keyword.IP])
            config += 'unnicast -route recursive-loopup tunnel-v6 tunnel-selector s\n'  # todo 默认只有一个selector

            config += ' #\n'
            config += ' route-policy color permit node 10\n'  # todo 10这个数字是否正确
            if 'color' in node:
                config += '  apply extcommunity color {0}\n'.format(node['color'])

            config += ' #\n'
            config += '  tunnel-selector s permit node 10\n'  # todo selector的名称，node 10这个数字
            config += '   apply tunnel-policy p\n'  # todo policy名称

            config += ' tunnel-policy p\n'  # todo policy名称
            config += '  tunnel select-seq ipv6 srv6-te-policy load-balance-number 1\n'

        elif node['type'] == 'Device':
            network_list = []
            config += 'bgp {0}\n'.format(node['bgp_domain'])
            config += ' router-id {0}\n'.format(node[keyword.IP])
            for nbr_name in topo.neighbors(node_name):
                nbr = topo.nodes[nbr_name]
                if nbr['type'] == 'PE':
                    config += ' peer {0} as-number {1}\n'.format(nbr[keyword.PREFIX_SID].strCompressed(), nbr['bgp_domain'])
                    edge = topo[node_name][nbr_name]
                    network_list.append(edge[keyword.INTERFACE].make_net(edge['mask']))
            config += ' #\n'
            config += ' address-family ipv6 unicast\n'
            config += '  undo synchronization\n'
            for nbr_name in topo.neighbors(node_name):
                nbr = topo.nodes[nbr_name]
                if nbr['type'] == 'PE':
                    edge = topo[node_name][nbr_name]
                    # network_list.append(edge[keyword.INTERFACE].make_net(edge['mask']))
                    config += '  network {0}\n'.format(edge[keyword.INTERFACE].make_net(edge['mask']))
                    config += '  peer {0} enable\n'.format(nbr[keyword.IP].strCompressed())

        configs[node_name] = config






t = Topo('./topo/topology.json')
# Graph = t.getFromJson(json_topo) #网络拓扑
Graph = t.getFromJson()
set_interface_ipv6(Graph)
BGP_conf(Graph)