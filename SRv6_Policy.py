#!/usr/bin/env python
# -*- coding: utf-8 -*-
'''
@Project ：AutoSRv6 
@File ：SRv6_Policy.py
@Author ：Lucky
@Date ：2022/7/20 21:23 
'''
from collections import namedtuple

from utils.keyword import *

Can_Path = namedtuple("Can_Path", [Priority, Seg_List, Weight])


class SRv6_Policy(object):

    def __init__(self, name, head, bsid, color, end_point, info):
        self.Name = name
        self.Head = head
        self.Color = color
        self.End = end_point
        self.BSID = bsid
        self.Info = {
            Policy_Type: Dynamic,  # dynamic  explicit
            Priority: 128,
            Mertric_Type: 0,  # 0: IGP ,1 : lat
            CONS: {},
            Flex_Algo: 0,  # 128-255 default:0
            Can_Paths: None,  # list of Can_Paths
        }
        for key, value in info.items():
            if key == "Can_Paths" and value is not None:
                if self.Info["Can_Paths"] is None:
                    self.Info["Can_Paths"] = []
                for v in value:
                    self.Info["Can_Paths"].append(Can_Path(Priority=v[0], Seg_List=v[1], Weight=v[2]))

            elif key in self.Info.keys():
                self.Info[key] = value

    def __str__(self):
        s = '*' * 20 + "\n" + \
            'name: ' + self.Name + "\n" + \
            'head: ' + self.Head + "\n" + \
            'color: ' + str(self.Color) + "\n" + \
            'End: ' + str(self.End) + "\n" + \
            'BSID: ' + str(self.BSID) + "\n" + \
            str(self.Info) + "\n" + \
            '*' * 20 + "\n"
        return s

