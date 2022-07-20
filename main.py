# This is a sample Python script.

# Press Shift+F10 to execute it or replace it with your code.
# Press Double Shift to search everywhere for classes, files, tool windows, actions, and settings.

from read_topo import *
# json_topo = input("请输入网络拓扑文件地址：")
t = Topo('./topo/topology.json')
# Graph = t.getFromJson(json_topo) #网络拓扑
Graph = t.getFromJson()

