#!/usr/bin/env python
# -*- coding: utf-8 -*-
'''
@Project ：AutoSRv6 
@File ：gen_clean_config.py
@Author ：Lucky
@Date ：2023/3/17 8:10
'''
#!/usr/bin/env python
# -*- encoding: utf-8 -*-
# import lib
import glob
import os
import random
import shutil

from timeit import default_timer as timer

from tekton.bgp import Community

from eval_scripts.new_ebgp_eval import gen_simple_abs, gen_simple
from synet.utils.common import *
from synet.utils.topo_gen import read_topology_zoo_netgraph
from synet.utils.smt_context import VALUENOTSET
from synet.synthesis.ospf_heuristic import OSPFSyn as OSPFCEGIS
from synet.synthesis.ospf import OSPFSyn as OSPFConcrete
from synet.synthesis.connected import ConnectedSyn

def main():

    # small = 'topos/small'
    mid = 'topos/large'
    for file in glob.glob(mid+'/*.graphml'):
        print (file)
        topo = read_topology_zoo_netgraph(file)

        conn = ConnectedSyn([], topo, full=True)
        conn.synthesize()
        ospf = OSPFCEGIS(topo, gen_paths=100)
        assert ospf.synthesize()

        # This random generator MUST be used everywhere!!!!

        from tekton.gns3 import GNS3Topo
        ospf.update_network_graph()
        gns3 = GNS3Topo(topo)
        basename = os.path.basename(file).strip('.graphml')
        out_name = "%s_%s_%s_%s" % (basename, 0, 0, 0)
        out_dir = 'out-configs/large/%s' % out_name
        print ("Writing configs to:", out_dir)
        gns3.write_configs(out_dir)


def gen_bgp():

    config_dir = 'out-configs/bgp-out-configs'
    topo_size = '/large'
    topo_dir = 'topos' + topo_size
    req_size = 2
    for file in glob.glob(topo_dir+'/*.py'):
        file_name = os.path.basename(file).strip('.py').split('_')[0]
        config_files = config_dir + topo_size + '/'+file_name+'_fixed_0_abs_simple_reqsize_' + str(req_size)
        ipdict = get_dict(config_files)
        with open(file, 'r') as file:
            exec (file.read())
        dir1 = config_dir + topo_size + '_bgp_simple'
        if not os.path.exists(dir1):
            os.makedirs(dir1)
        topo_file = topo_dir + '/' + file_name + '.graphml'

        for i in [2, 8, 16]:
            ospf_reqs = eval('reqs_simple_%d' % i)
            topo = read_topology_zoo_netgraph(topo_file)
            all_communities = [Community("100:%d" % ii) for ii in range(len(ospf_reqs))]
            all_reqs, syn_vals = gen_simple(topo, ospf_reqs, all_communities)
            all_reqs = gen_simple_abs(topo, ospf_reqs, all_communities, {}, {})
            all_reqs = ospf_reqs
            string = ""

            dir2 = dir1 + '/' + file_name + '_bgp_simple_%s' % str(i) + '/logs'
            dir3 = dir1 + '/' + file_name + '_bgp_simple_%s' % str(i) + '/configs/'
            copy_configs(config_files, dir3)
            if not os.path.exists(dir2):
                os.makedirs(dir2)
            out_file = dir2 + '/verified.txt'
            for req in all_reqs:
                src = req.path[0]
                dst = req.path[-1]
                string += "smt-reachability srcIps=[\"" + ipdict[src] + "\"], dstIps=[\"" + ipdict[
                    dst] + "\"], ingressNodeRegex=" + str(src) + ", finalNodeRegex=" + str(
                    dst) + "\n"
            open(out_file, 'w').write(string)

        dir_order = config_dir + topo_size + '_bgp_order'
        if not os.path.exists(dir_order):
            os.makedirs(dir_order)
        topo_file_order = topo_dir + '/' + file_name + '.graphml'

        for i in [2, 8, 16]:
            ospf_reqs = eval('reqs_order_%d_2' % i)
            # topo = read_topology_zoo_netgraph(topo_file)
            # all_communities = [Community("100:%d" % ii) for ii in range(len(ospf_reqs))]
            # all_reqs, syn_vals = gen_simple(topo, ospf_reqs, all_communities)
            # all_reqs = gen_simple_abs(topo, ospf_reqs, all_communities, {}, {})
            all_reqs = ospf_reqs
            string = ""

            dir2_order = dir_order + '/' + file_name + '_bgp_order_%s' % str(i) + '/logs'
            dir3_order = dir_order + '/' + file_name + '_bgp_order_%s' % str(i) + '/configs/'
            copy_configs(config_files, dir3_order)
            if not os.path.exists(dir2_order):
                os.makedirs(dir2_order)
            out_file = dir2_order + '/verified.txt'
            for req in all_reqs:
                # req = PathOrderReq()
                path_str = []
                for req in req.paths:
                    src = req.path[0]
                    dst = req.path[-1]
                    interval = "["
                    num = len(req.path)
                    index = 0
                    for node in req.path:
                        index += 1
                        node = node.replace(" ", "")
                        if index == num:
                            interval += "'" + node + "']"
                        else:
                            interval += "'" + node + "',"
                    path_str.append(interval)

                string += "smt-path-preference srcIps=[\"" + ipdict[src] + "\"], dstIps=[\"" + ipdict[
                    dst] + "\"], ingressNodeRegex=" + str(src) + ", finalNodeRegex=" + str(
                    dst) + ", prefs=[" + path_str[0] + "," + path_str[1] + "]\n"
            open(out_file, 'w').write(string)


def parse_req():
    os.chdir(r'D:\Users\Lucky\NEU\AutoSRv6')  # 加入自己项目根目录路径
    mid = 'topos/large'
    gen_dir = 'out-configs/large'
    for file in glob.glob(mid + '/*.py'):
        print (file)
        file_name = os.path.basename(file).strip('.py').split('_')[0]
        allfile = file_name + '_0_0_0'
        config_file = gen_dir + '/'+allfile
        ipdict = get_dict(config_file)
        with open(file, 'r') as file:
            exec (file.read())
        dir1 = gen_dir + '_simple'
        if not os.path.exists(dir1):
            os.makedirs(dir1)
        for i in [2,8,16]:
            reqs = eval('reqs_simple_%d' % i)
            string = ""

            dir2 = dir1 + '/' + file_name + '_simple_%s' % str(i) + '/logs'
            dir3 = dir1 + '/' + file_name + '_simple_%s' % str(i) + '/configs/'
            copy_configs(config_file, dir3)
            if not os.path.exists(dir2):
                os.makedirs(dir2)
            out_file = dir2 + '/verified.txt'
            for req in reqs:
                # req = PathReq().
                src = req.path[0]
                dst = req.path[-1]
                path_str = str(req.path)
                # string += "smt-reachability srcIps=[\"" + ipdict[src] + "\"], dstIps=[\"" + ipdict[
                #     dst] + "\"], ingressNodeRegex=" + str(src) + ", finalNodeRegex=" + str(
                #     dst) + ", waypoints=" + path_str + "\n"
                string += "smt-reachability srcIps=[\"" + ipdict[src] + "\"], dstIps=[\"" + ipdict[
                    dst] + "\"], ingressNodeRegex=" + str(src) + ", finalNodeRegex=" + str(
                    dst) + "\n"
            open(out_file, 'w').write(string)

        dir_order = gen_dir + '_order'
        if not os.path.exists(dir_order):
            os.makedirs(dir_order)
        for i in [2,8,16]:
            reqs = eval('reqs_order_%d_2' % i)
            string = ""

            dir_order_2 = dir_order + '/' + file_name + '_order_%s' % str(i) + '/logs'
            dir_order_3 = dir_order + '/' + file_name + '_order_%s' % str(i) + '/configs/'
            copy_configs(config_file, dir_order_3)
            if not os.path.exists(dir_order_2):
                os.makedirs(dir_order_2)
            out_file = dir_order_2 + '/verified.txt'
            for req in reqs:
                # req = PathOrderReq()
                path_str = []
                for req in req.paths:
                    src = req.path[0]
                    dst = req.path[-1]
                    interval = "["
                    num = len(req.path)
                    index = 0
                    for node in req.path:
                        index += 1
                        node = node.replace(" ","")
                        if index == num:
                            interval += "'" + node + "']"
                        else:
                            interval += "'"+node+"',"
                    path_str.append(interval)

                string += "smt-path-preference srcIps=[\"" + ipdict[src] + "\"], dstIps=[\"" + ipdict[
                    dst] + "\"], ingressNodeRegex=" + str(src) + ", finalNodeRegex=" + str(
                    dst) + ", prefs=[" + path_str[0] + "," + path_str[1] + "]\n"
            open(out_file, 'w').write(string)


def mycopyfile(srcfile, dstpath):
    # 复制函数
    if not os.path.isfile(srcfile):
        print ("%s not exist!"%(srcfile))
    else:
        fpath, fname=os.path.split(srcfile)             # 分离文件名和路径
        if not os.path.exists(dstpath):
            os.makedirs(dstpath)                       # 创建路径
        shutil.copy(srcfile, dstpath + fname)          # 复制文件
        # print "copy %s -> %s" % (srcfile, dstpath + fname)

def copy_configs(allfile, distpath):
    for file in glob.glob(allfile + '/configs/*.cfg'):
        mycopyfile(file, distpath)

def get_dict(allfile):
    ipdict = dict()
    # allfile = 'out-configs/small/Arnes_0_0_0'
    for dst in glob.glob(allfile + '/configs/*.cfg'):
        # dstfilename = dst
        # print dst
        if not (os.path.isfile(dst)):
            print ("file doesn't exist")
        else:
            dstfile = "" + dst
            # dstfile = open(str(dstfilename), "r")
            with open(dstfile, 'r') as searchfile:
                for line in searchfile:
                    if 'ip address' in line:
                        if 'ip address prefix-list' in line:
                            continue
                        array = dst.split("\\")
                        name = array[len(array) - 1][:-4]
                        temp = line.split(" ")
                        ipdict[name] = line.split(" ")[3]
    return ipdict


if __name__ == '__main__':
    # main()
    os.chdir(r'D:\Users\Lucky\NEU\AutoSRv6')
    # parse_req()
    gen_bgp()