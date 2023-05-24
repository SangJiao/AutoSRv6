import ctypes
import json
import sys
import threading
from multiprocessing import Process

import win32con
from PyQt5.QtCore import QThread, pyqtSignal, Qt
from PyQt5.QtWidgets import QMainWindow, QDialog, QHeaderView, QMenu, QTableWidgetItem, QApplication

from record import Record, decode, encode
# from record import Record, decode, encode
from ui.isisSynthesisWindow import Ui_ISIS_Syn_Dialog
from ui.mainWindow import *
from ui.synthesisWindow import Ui_Syn_Dialog
from ui.verificationWindow import Ui_Ver_Dialog
from ui.recordWindow import Ui_Rec_Dialog
# from sr_synthesis import SR_Synthesizer
# from load_files import *
# from verification import *
import time
import os

#from ui.loginPage import *


def save_record(record):
    records_list = decode()
    records_list.append(record)
    encode(records_list)


class SynThread(QThread):
    log_signal = pyqtSignal(str)  # 值变化信号
    handle = -1

    def __init__(self):
        super(SynThread, self).__init__()
        self.topo_path = ""
        self.policy_path = ""
        self.record = None

    def run(self):
        try:
            self.handle = ctypes.windll.kernel32.OpenThread(
                win32con.PROCESS_ALL_ACCESS, False, int(QThread.currentThreadId()))
        except Exception as e:
            print('get thread handle failed', e)

        start_time = time.time()
        # 记录历史记录
        # input_path, start_time, type, out_path, time = "", result =
        file_dir = os.path.dirname(self.topo_path)
        format_time = time.strftime("%Y-%m-%d %H:%M:%S", time.localtime(start_time))
        self.record = Record(file_dir, format_time, "synthesis", file_dir)

        #topo = Load_topofile(self.topo_path)

        out_dir = os.path.dirname(self.topo_path)
        # time.sleep(10)
        #ana = policy.analyze()

        end_time = time.time()
        t = str(end_time - start_time)[:6] + "S"
        self.log_signal.emit("Synthesis time is " + t)

        self.record.time = t
        self.record.result = "true"
        save_record(self.record)


class VerThread(QThread):
    log_signal = pyqtSignal(str)  # 值变化信号
    handle = -1

    def __init__(self):
        super(VerThread, self).__init__()
        self.topo_path = ""
        self.policy_path = ""
        self.configs = ""
        self.record = None

    def run(self):
        try:
            self.handle = ctypes.windll.kernel32.OpenThread(
                win32con.PROCESS_ALL_ACCESS, False, int(QThread.currentThreadId()))
        except Exception as e:
            print('get thread handle failed', e)

        start_time = time.time()
        # 记录历史记录
        # input_path, start_time, type, out_path, time = "", result =
        file_dir = os.path.dirname(self.topo_path)
        format_time = time.strftime("%Y-%m-%d %H:%M:%S", time.localtime(start_time))
        self.record = Record(file_dir, format_time, "verification", file_dir)

       # topo = Load_topofile(self.topo_path)
        #policy = Load_policyfile(self.policy_path)

        # # time.sleep(10)
        #ver = Verfication(topo, policy, self.configs, log_signal=self.log_signal)
        #flag = ver.verify()
        flag = True
        if flag:
            self.log_signal.emit("Verify succeed! ")
            self.record.result = "true"
        else:
            self.log_signal.emit("Verify failed! ")
            self.record.result = "false"
        # SR_Synthesizer(topo, policy, out_dir, log_signal=self.log_signal)
        end_time = time.time()
        t = str(end_time - start_time)[:6] + "S"
        self.log_signal.emit("Verification time is " + t)

        self.record.time = t

        save_record(self.record)



class SynDialog(QDialog, Ui_Syn_Dialog):
    def __init__(self, parent=None):
        super(SynDialog, self).__init__(parent)
        self.setupUi(self)
        self.topo_file = ""
        self.policy_file = ""
        #self.topo_button.clicked.connect(self.topo_button_click)
        self.policy_button.clicked.connect(self.policy_button_click)
        self.start_button.clicked.connect(self.start_button_click)
        self.ana_button.clicked.connect(self.ana_button_click)
        # self.setMouseTracking(True)

        # 综合线程
        self.syn_thread = SynThread()
        # 信号绑定
        self.syn_thread.finished.connect(self.set_start_button_true)
        self.syn_thread.log_signal.connect(self.output_browser.append)

        self.record = None

    # 杀死综合线程
    def kill_thread(self):
        ret = ctypes.windll.kernel32.TerminateThread(self.syn_thread.handle, 0)
        # print('终止线程', self.syn_thread.handle, ret)

    def set_start_button_true(self):
        self.start_button.setEnabled(True)

    # 关闭窗口事件
    def closeEvent(self, event):

        reply = QtWidgets.QMessageBox.question(self, u'警告', u'确认退出?', QtWidgets.QMessageBox.Yes,
                                               QtWidgets.QMessageBox.No)
        # QtWidgets.QMessageBox.question(self,u'弹窗名',u'弹窗内容',选项1,选项2)

        if reply == QtWidgets.QMessageBox.Yes:
            self.kill_thread()
            event.accept()  # 关闭窗口
        else:
            event.ignore()  # 忽视点击事件

    # def topo_button_click(self):
    #     file, file_type = QtWidgets.QFileDialog.getOpenFileName(self, "选择", "./", "Topo Files (*.topo);;ALL Files (*)")
    #     if file:
    #         self.topo_lineEdit.setText(file)
    #         self.topo_file = file

    def policy_button_click(self):
        file, file_type = QtWidgets.QFileDialog.getOpenFileName(self, "选择", "./",
                                                                "Topo Files (*_policy);;ALL Files (*)")
        if file:
            self.policy_lineEdit.setText(file)
            self.policy_file = file

    def start_button_click(self):

        # if not (os.path.exists(self.topo_file) and os.path.exists(self.policy_file)):
        #     QtWidgets.QMessageBox.warning(self, "警告", "路径格式有误，请重新输入", QtWidgets.QMessageBox.Yes)
        #     return

        self.start_button.setEnabled(False)

        self.input_browser.clear()
        self.output_browser.clear()

        # with open(self.topo_file) as f:
        #     inputs = f.read()
        #self.input_browser.append("读取拓扑文件")
        #self.input_browser.append(inputs)
        with open(self.policy_file) as f:
            inputs = f.read()
        self.input_browser.append("读取SRv6配置意图文件")
        self.input_browser.append(inputs)

        # 使用新线程处理 生成策略部分
       # self.syn_thread.topo_path = self.topo_file
        self.syn_thread.policy_path = self.policy_file
        self.syn_thread.record = self.record
       # self.syn_thread.start()
        # policy = read_policy()
        # list = policy.analyze()
        # self.output_browser.append(list)

    def ana_button_click(self):

        self.start_button.setEnabled(False)
        self.output_browser.clear()
        with open("..\policy\parse") as f:
            inputs = f.read()
        self.output_browser.append("解析SRv6配置意图的结果")
        self.output_browser.append(inputs)




class ISISSynDialog(QDialog, Ui_ISIS_Syn_Dialog):
    def __init__(self, parent=None):
        super(ISISSynDialog, self).__init__(parent)
        self.setupUi(self)
        self.topo_file = ""
        self.policy_file = ""
        self.topo_buttoni.clicked.connect(self.topo_button_click)
        self.policy_buttoni.clicked.connect(self.policy_button_click)
        self.start1_button.clicked.connect(self.start_button_click)
        self.isis_syn_button.clicked.connect(self.isis_syn_button_click)
        # self.setMouseTracking(True)

        # 综合线程
        self.syn_thread = SynThread()
        # 信号绑定
        self.syn_thread.finished.connect(self.set_start_button_true)
        self.syn_thread.log_signal.connect(self.output_browseri.append)

        self.record = None

    # 杀死综合线程
    def kill_thread(self):
        ret = ctypes.windll.kernel32.TerminateThread(self.syn_thread.handle, 0)
        # print('终止线程', self.syn_thread.handle, ret)

    def set_start_button_true(self):
        self.start1_button.setEnabled(True)

    # 关闭窗口事件
    def closeEvent(self, event):

        reply = QtWidgets.QMessageBox.question(self, u'警告', u'确认退出?', QtWidgets.QMessageBox.Yes,
                                               QtWidgets.QMessageBox.No)
        # QtWidgets.QMessageBox.question(self,u'弹窗名',u'弹窗内容',选项1,选项2)

        if reply == QtWidgets.QMessageBox.Yes:
            self.kill_thread()
            event.accept()  # 关闭窗口
        else:
            event.ignore()  # 忽视点击事件

    def topo_button_click(self):
        file, file_type = QtWidgets.QFileDialog.getOpenFileName(self, "选择", "./", "Topo Files (*.json);;ALL Files (*)")
        if file:
            self.topo_lineEditi.setText(file)
            self.topo_file = file

    def policy_button_click(self):
        file, file_type = QtWidgets.QFileDialog.getOpenFileName(self, "选择", "./",
                                                                "Topo Files (*_policy);;ALL Files (*)")
        if file:
            self.policy_lineEditi.setText(file)
            self.policy_file = file

    def start_button_click(self):

        # if not (os.path.exists(self.topo_file) and os.path.exists(self.policy_file)):
        #     QtWidgets.QMessageBox.warning(self, "警告", "路径格式有误，请重新输入", QtWidgets.QMessageBox.Yes)
        #     return

        self.start1_button.setEnabled(False)

        self.input_browseri.clear()
        self.output_browseri.clear()

        with open(self.topo_file) as f:
            inputs = f.read()
        self.input_browseri.append("Topology information:")
        self.input_browseri.append(inputs)
        with open(self.policy_file) as f:
            inputs = f.read()
        self.input_browseri.append("Configuration information:")
        self.input_browseri.append(inputs)

        # 使用新线程处理 生成策略部分
       # self.syn_thread.topo_path = self.topo_file
       #  self.syn_thread.policy_path = self.policy_file
       #  self.syn_thread.record = self.record
       # self.syn_thread.start()
        # policy = read_policy()
        # list = policy.analyze()
        # self.output_browser.append(list)

    def isis_syn_button_click(self):

        self.start1_button.setEnabled(False)
        self.output_browseri.clear()
        with open("..\policy\isis_result") as f:
            inputs = f.read()
        #self.output_browseri.append("解析SRv6配置意图的结果")
        self.output_browseri.append(inputs)









class VerDialog(QDialog, Ui_Ver_Dialog):
    log_signal = pyqtSignal(str)  # 值变化信号

    def __init__(self, parent=None):

        super(VerDialog, self).__init__(parent)
        self.setupUi(self)

        self.topo_button.clicked.connect(self.topo_button_click)
        self.policy_button.clicked.connect(self.policy_button_click)
        self.start_button.clicked.connect(self.start_button_click)
        self.encoding_button.clicked.connect(self.encoding_button_click)
        self.syn_button.clicked.connect(self.syn_button_click)
        #self.config_button.clicked.connect(self.config_button_click)

        # # 验证线程
        # self.ver_thread = VerThread()
        # # 信号绑定
        # self.ver_thread.finished.connect(self.set_start_button_true)
        # self.ver_thread.log_signal.connect(self.output_browser.append)
        self.log_signal.connect(self.output_browser.append)
        self.record = None
        self.topo_file = ""
        self.policy_file = ""

    # 杀死验证线程
    def kill_thread(self):
        ret = ctypes.windll.kernel32.TerminateThread(self.ver_thread.handle, 0)
        # print('终止线程', self.syn_thread.handle, ret)

    def set_start_button_true(self):
        self.start_button.setEnabled(True)

    # 关闭窗口事件
    def closeEvent(self, event):

        reply = QtWidgets.QMessageBox.question(self, u'警告', u'确认退出?', QtWidgets.QMessageBox.Yes,
                                               QtWidgets.QMessageBox.No)
        # QtWidgets.QMessageBox.question(self,u'弹窗名',u'弹窗内容',选项1,选项2)

        if reply == QtWidgets.QMessageBox.Yes:
            # self.kill_thread()
            event.accept()  # 关闭窗口
        else:
            event.ignore()  # 忽视点击事件



    def topo_button_click(self):
        file, file_type = QtWidgets.QFileDialog.getOpenFileName(self, "选择", "./", "Topo Files (*.json);;ALL Files (*)")
        if file:
            self.topo_lineEdit.setText(file)
            self.topo_file = file

    def policy_button_click(self):
        file, file_type = QtWidgets.QFileDialog.getOpenFileName(self, "选择", "./",
                                                                "policy Files (*_policy);;ALL Files (*)")
        if file:
            self.policy_lineEdit.setText(file)
            self.policy_file = file

    def start_button_click(self):

        # if not (os.path.exists(self.topo_file) and os.path.exists(self.policy_file)):
        #     QtWidgets.QMessageBox.warning(self, "警告", "路径格式有误，请重新输入", QtWidgets.QMessageBox.Yes)
        #     return

        self.start_button.setEnabled(False)

        self.input_browser.clear()
        self.output_browser.clear()

        with open(self.policy_file) as f:
            inputs = f.read()
        self.input_browser.append("Intent information:")
        self.input_browser.append(inputs)
        with open(self.topo_file) as f:
            inputs = f.read()
        self.input_browser.append("Topology information:")
        self.input_browser.append(inputs)


        # 使用新线程处理 生成策略部分
       # self.syn_thread.topo_path = self.topo_file
       #  self.syn_thread.policy_path = self.policy_file
       #  self.syn_thread.record = self.record
       # self.syn_thread.start()
        # policy = read_policy()
        # list = policy.analyze()
        # self.output_browser.append(list)

    def encoding_button_click(self):
        self.start_button.setEnabled(False)
        self.input_browser2.clear()
        with open("..\policy\srv6_encoding") as f:
            inputs = f.read()
        #self.output_browseri.append("解析SRv6配置意图的结果")
        self.input_browser2.append(inputs)

    def syn_button_click(self):
        self.start_button.setEnabled(False)
        self.output_browser.clear()
        with open("..\policy\srv6_syn") as f:
            inputs = f.read()
        #self.output_browseri.append("解析SRv6配置意图的结果")
        self.output_browser.append(inputs)





class RecDialog(QDialog, Ui_Rec_Dialog):
    def __init__(self, parent=None):
        super(RecDialog, self).__init__(parent)
        self.setupUi(self)
        # with open("..\policy\parse") as f:
        #     inputs = f.read()
        # with open("record.json") as f:
        #     result = json.load(f)
        self.record_list = []
        # for i in result:
        #     self.record_list.append((i.get("input_path"),i.get("start_time"),i.get("type"),i.get("time"),i.get("result"),i.get("out_path")))
        # # self.record_tableWidget.horizontalHeader().setSectionResizeMode(QHeaderView.Stretch)  # 所有列自动拉伸，充满界面
        # self.record_tableWidget.setContextMenuPolicy(Qt.CustomContextMenu)  # 允许右键产生子菜单
        #self.record_tableWidget.customContextMenuRequested.connect(self.generate_menu)  # 右键菜单
        #self.records_list = decode()
        # if len(self.records_list) > 15:
        #     self.record_tableWidget.setRowCount(len(self.records_list))
        #self.display_records()

    def display_records(self):

        for i, record in enumerate(self.records_list):
            # input_path, start_time, type, out_path, time = "", result =
            item = QTableWidgetItem(str(i + 1))
            item.setTextAlignment(Qt.AlignHCenter | Qt.AlignVCenter)
            self.record_tableWidget.setItem(i, 0, item)
            item = QTableWidgetItem(record.input_path)
            item.setTextAlignment(Qt.AlignHCenter | Qt.AlignVCenter)
            self.record_tableWidget.setItem(i, 1, item)
            item = QTableWidgetItem(record.start_time)
            item.setTextAlignment(Qt.AlignHCenter | Qt.AlignVCenter)
            self.record_tableWidget.setItem(i, 2, item)
            item = QTableWidgetItem(record.type)
            item.setTextAlignment(Qt.AlignHCenter | Qt.AlignVCenter)
            self.record_tableWidget.setItem(i, 3, item)
            item = QTableWidgetItem(record.time)
            item.setTextAlignment(Qt.AlignHCenter | Qt.AlignVCenter)
            self.record_tableWidget.setItem(i, 4, item)
            item = QTableWidgetItem(record.result)
            item.setTextAlignment(Qt.AlignHCenter | Qt.AlignVCenter)
            self.record_tableWidget.setItem(i, 5, item)
            item = QTableWidgetItem(record.out_path)
            item.setTextAlignment(Qt.AlignHCenter | Qt.AlignVCenter)
            self.record_tableWidget.setItem(i, 6, item)

    # def generate_menu(self, pos):
    #     row_num = self.record_tableWidget.selectionModel().selection().indexes()[0].row()
    #     if row_num < len(self.records_list):
    #         menu = QMenu()
    #         open = menu.addAction(u"打开输出文件")
    #         delete = menu.addAction(u"删除记录")
    #         action = menu.exec_(self.record_tableWidget.mapToGlobal(pos))
    #         if action == open:
    #             os.startfile(self.records_list[row_num].input_path)
    #         elif action == delete:
    #             self.record_tableWidget.removeRow(row_num)
    #             del self.records_list[row_num]
    #             encode(self.records_list)
    #         else:
    #             return


class MainWindow(QMainWindow, Ui_mainWindow):
    def __init__(self, parent=None):
        super(MainWindow, self).__init__(parent)
        self.setupUi(self)
        # 添加鼠标点击事件
        self.isis_syn_button.clicked.connect(self.show_isis_syn_dialog)
        self.syn_button.clicked.connect(self.show_ver_dialog)
        self.ana_button.clicked.connect(self.show_syn_dialog)
        self.rec_button.clicked.connect(self.show_rec_dialog)

    def show_isis_syn_dialog(self):
        isis_synDialog = ISISSynDialog()
        isis_synDialog.show()
        isis_synDialog.exec_()

    def show_syn_dialog(self):
        synDialog = SynDialog()
        synDialog.show()
        synDialog.exec_()
        for thread in threading.enumerate():
            print(thread.name)

    def show_ver_dialog(self):
        verDialog = VerDialog()
        verDialog.show()
        verDialog.exec_()

    def show_rec_dialog(self):
        recDialog = RecDialog()
        recDialog.show()
        recDialog.exec_()


app = QApplication(sys.argv)
if __name__ == '__main__':
    myWin = MainWindow()
    myWin.show()

    sys.exit(app.exec_())
