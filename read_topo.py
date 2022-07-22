#!/usr/bin/env python
# -*- coding: utf-8 -*-
'''
参数拓扑模块：
拓扑文件使用json格式
节点属性：名称，型号
边：双向，源节点，目的节点，接口
以networkx为基础构建有向图。为节点与边设置属性。属性参考PPT中的节点属性
属性读取

拓扑文件读取
设备性能文件读取及与topo对应
@Project ：AutoSRv6
@File ：topo.py
@Date ：2022/7/19 14:46
'''
import networkx as nx
import json

from utils.keyword import *


class Topo:
    """
    参数拓扑数据结构
    """
    def __init__(self, json_topo):
        self.topo = nx.DiGraph()
        self.json_topo = json_topo
        self.json_data = self.get_json_data()


    def get_json_data(self):
        '''
        :return: 读取json_topo文件返回json数据
        '''
        with open(self.json_topo, 'r', encoding='utf-8') as file:
            data = json.load(file)
        return data


    def getFromJson(self):
        """
        根据json_data，构建拓扑
        :param json_topo:
        :return: self.topo
        """

        for element in self.json_data:
            #print(element)
            if 'nodes' in element:
                for node in element['nodes']:
                    #print(node)
                    self.topo.add_node(node["name"],type = node['type'])

            if 'edges' in element:
                for edge in element['edges']:
                    self.topo.add_edge(edge['node_1'],edge['node_2'],src_int=edge['int_1'],dst_int=edge['int_2'],
                                           bandwidth=1000, wide = 1 ,**{TYPE: LINK_EDGE})#ISIS的权重值用wide属性标识。边的权重为接口的wide值，都设为1
                    self.topo.add_edge(edge['node_2'], edge['node_1'], src_int=edge['int_2'], dst_int=edge['int_1'],
                                           weight=1000, wide = 1, **{TYPE: LINK_EDGE})

                # print('--------------------')
                # print(self.topo.nodes['A']['type'])
            if 'BGP_Domain' in element:
                    for domain in element['BGP_Domain']:
                        if 'nodes' in domain:
                            for node in domain['nodes']:
                                self.topo.nodes[node]['bgp_domain'] = domain['as_number']

        return self.topo


    def if_bgp_domian_relation(self, srcAS, dstAS):
        '''
        判断两个bgp_domain是否相连
        :param srcAS: bgp_domain 1
        :param dstAS: bgp_domain 2
        :return: True or False
        '''
        flag = False
        for element in self.json_data:
            if 'bgp_domain_links' in element:
                for link in element['bgp_domain_links']:
                    if link['srcAS'] == srcAS and link['dstAS'] == dstAS:
                        flag = True
        return flag


    def get_domain_peers(self, srcAS, dstAS):
        '''
        根据as_number 得到两个相连bgp_domain之间连的网络设备
        :param srcAS: bgp_domain 1
        :param dstAS: bgp_domain 2
        :return:
        '''

        src_Node = 'not exist'
        dst_Node = 'not exist'
        for element in self.json_data:
            if 'bgp_domain_links' in element:
                for link in element['bgp_domain_links']:
                    if link['srcAS'] == srcAS and link['dstAS'] == dstAS:
                        src_Node = link['srcNode']
                        dst_Node = link['dstNode']

        return src_Node, dst_Node


    def get_domain_relation(self):
        '''

        :return: 返回的是一个列表，里面的元素是peer
        '''
        domain_rel = []
        bgp_link = ()
        for element in self.json_data:
            if 'bgp_domain_links' in element:
                for link in element['bgp_domain_links']:
                    bgp_link = (link['srcAS'],link['dstAS'])
                    domain_rel.append(bgp_link)
        return domain_rel