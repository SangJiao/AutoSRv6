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
        self.classify = classify
        self.name = name
        self.paths = paths
        self.pro_dict = pro_dict