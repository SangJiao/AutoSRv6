# This is a sample Python script.

# Press Shift+F10 to execute it or replace it with your code.
# Press Double Shift to search everywhere for classes, files, tool windows, actions, and settings.
from explicit_path import waypoint
from explicit_path.waypoint import WayPoint
from read_policy import *
from read_topo import *

# json_topo = input("请输入网络拓扑文件地址：")
t = Topo('./topo/topology.json')
# Graph = t.getFromJson(json_topo) #网络拓扑
Graph = t.getFromJson()
print(Graph.nodes['A'])
print(Graph.edges())
print(Graph.edges[('A','B')])
with open(r'./policy/new_test', 'r') as file:
    user_policy = file.read()
rp = read_policy(user_policy)
waypoint_list = rp.waypoint_info()  # 陆航信息
print(waypoint_list)
waypoint_path = WayPoint(Graph,waypoint_list)
#waypoint_path.explicit_path()
