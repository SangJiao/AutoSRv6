#!/usr/bin/env python
# -*- coding: utf-8 -*-
'''
@Project ：AutoSRv6 
@File ：Policy.py
@Author ：Lucky
@Date ：2022/7/22 14:06 
'''
import re
from utils.keyword import *

class Policy(object):
    def __init__(self, name, classify, paths, pro_dict):
        assert isinstance(pro_dict, dict)
        self.name = name
        self.classify = classify
        self.paths = paths
        self.pro_dict = pro_dict

    def __str__(self):
        s = '*' * 20 + "\n" + \
            'name: ' + self.name + "\n" + \
            'classify: ' + self.classify + "\n" + \
            'paths:' + str(self.paths) + "\n" + \
            'pro_dict' + str(self.pro_dict)+ "\n" + \
            '*' * 20 + "\n"
        return s
