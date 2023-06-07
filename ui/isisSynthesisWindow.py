#!/usr/bin/env python
# -*- coding: utf-8 -*-
#
# Created by: PyQt5 UI code generator 5.15.4
#
# WARNING: Any manual changes made to this file will be lost when pyuic5 is
# run again.  Do not edit this file unless you know what you are doing.
import os

from PyQt5 import QtCore, QtGui, QtWidgets

url = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))  # 文件夹

'''
@Project ：AutoSRv6 
@File ：isisSynthesisWindow.py
@Author ：Lucky
@Date ：2023/4/29 14:55 
'''


class Ui_ISIS_Syn_Dialog(object):
    def setupUi(self, ISIS_Syn_Dialog):
        ISIS_Syn_Dialog.setObjectName("ISIS_Syn_Dialog")
        ISIS_Syn_Dialog.resize(916, 573)
        icon = QtGui.QIcon()
        icon.addPixmap(QtGui.QPixmap(os.path.join(url, "./resource/icons/neu.png")), QtGui.QIcon.Normal,
                       QtGui.QIcon.Off)
        ISIS_Syn_Dialog.setWindowIcon(icon)
        ISIS_Syn_Dialog.setStyleSheet("background-color: rgb(240, 240, 240);")

        self.start1_button = QtWidgets.QPushButton(ISIS_Syn_Dialog)
        self.start1_button.setGeometry(QtCore.QRect(600, 40, 100, 60))
        self.start1_button.setAutoFillBackground(False)
        self.start1_button.setStyleSheet("QPushButton#start1_button {"
                                         "background-color: rgb(63, 152, 220);"
                                         "color: white;"
                                         "font-size: 18px;"
                                         "font-weight: bold;"
                                         "border: 2px solid white;"
                                         "border-radius: 10px;"
                                         "}"
                                         "QPushButton#start_button:hover {"
                                         "background-color: white;"
                                         "color: #4CAF50;"
                                         "}")
        self.start1_button.setCheckable(False)
        self.start1_button.setObjectName("start1_button")

        self.isis_syn_button = QtWidgets.QPushButton(ISIS_Syn_Dialog)
        self.isis_syn_button.setGeometry(QtCore.QRect(730, 40, 130, 60))
        self.isis_syn_button.setAutoFillBackground(False)
        self.isis_syn_button.setStyleSheet("QPushButton#isis_syn_button {"
                                           "background-color:rgb(63, 152, 220);"
                                           "color: white;"
                                           "font-size: 18px;"
                                           "font-weight: bold;"
                                           "border: 2px solid white;"
                                           "border-radius: 10px;"
                                           "}"
                                           "QPushButton#ana_button:hover {"
                                           "background-color: white;"
                                           "color: #4CAF50;"
                                           "}")

        self.isis_syn_button.setCheckable(False)
        self.isis_syn_button.setObjectName("isis_syn_button")

        self.layoutWidgeti = QtWidgets.QWidget(ISIS_Syn_Dialog)
        self.layoutWidgeti.setGeometry(QtCore.QRect(450, 150, 451, 411))
        self.layoutWidgeti.setObjectName("layoutWidgeti")
        self.gridLayouti_4 = QtWidgets.QGridLayout(self.layoutWidgeti)
        self.gridLayouti_4.setContentsMargins(0, 0, 0, 0)
        self.gridLayouti_4.setObjectName("gridLayouti_4")  # 用于设置对象的名称以便在后续的代码中引用。
        # self.layoutWidget.setStyleSheet("background-color: red;")

        self.labeli_2 = QtWidgets.QLabel(self.layoutWidgeti)  # 对应输出结果的那个标签标题
        font = QtGui.QFont()
        font.setFamily("宋体")
        font.setPointSize(10)
        self.labeli_2.setFont(font)
        self.labeli_2.setObjectName("labeli_2")
        self.gridLayouti_4.addWidget(self.labeli_2, 0, 0, 1, 1)

        self.output_browseri = QtWidgets.QTextBrowser(self.layoutWidgeti)  # 输出结果的那个框
        font = QtGui.QFont()
        font.setFamily("Consolas")
        self.output_browseri.setFont(font)
        self.output_browseri.setAutoFillBackground(True)
        self.output_browseri.setStyleSheet("background-color: rgb(255, 255, 255);")
        self.output_browseri.setSizeAdjustPolicy(QtWidgets.QAbstractScrollArea.AdjustToContents)
        self.output_browseri.setLineWrapMode(QtWidgets.QTextEdit.NoWrap)
        self.output_browseri.setLineWrapColumnOrWidth(0)
        self.output_browseri.setObjectName("output_browseri")
        self.gridLayouti_4.addWidget(self.output_browseri, 1, 0, 1, 1)

        self.layoutWidgeti1 = QtWidgets.QWidget(ISIS_Syn_Dialog)
        self.layoutWidgeti1.setGeometry(QtCore.QRect(10, 30, 565, 85))
        self.layoutWidgeti1.setObjectName("layoutWidgeti1")
        self.gridLayouti_2 = QtWidgets.QGridLayout(self.layoutWidgeti1)
        self.gridLayouti_2.setContentsMargins(0, 0, 0, 0)
        self.gridLayouti_2.setObjectName("gridLayouti_2")

        self.gridLayouti = QtWidgets.QGridLayout(self.layoutWidgeti1)
        self.gridLayouti.setContentsMargins(0, 0, 0, 0)
        self.gridLayouti.setObjectName("gridLayouti")
        self.topo_lineEditi = QtWidgets.QLineEdit(self.layoutWidgeti1)
        #self.layoutWidgeti1.setStyleSheet("background-color: rgb(255, 255, 255);")
        font = QtGui.QFont()
        font.setFamily("Consolas")

        self.topo_lineEditi.setFont(font)
        self.topo_lineEditi.setLayoutDirection(QtCore.Qt.LeftToRight)
        self.topo_lineEditi.setAutoFillBackground(False)
        self.topo_lineEditi.setStyleSheet("background-color: rgb(255, 255, 255);")
        self.topo_lineEditi.setReadOnly(True)
        self.topo_lineEditi.setObjectName("topo_lineEditi")
        self.gridLayouti.addWidget(self.topo_lineEditi, 0, 0, 1, 1)

        self.topo_buttoni = QtWidgets.QPushButton(self.layoutWidgeti1)
        self.topo_buttoni.setAutoFillBackground(False)
        self.topo_buttoni.setStyleSheet("background-color: rgb(225, 225, 225);\n"
"selection-background-color: rgb(229, 241, 251);")
        self.topo_buttoni.setCheckable(False)
        self.topo_buttoni.setObjectName("topo_buttoni")
        self.gridLayouti.addWidget(self.topo_buttoni, 0, 1, 1, 1)

        self.policy_lineEditi = QtWidgets.QLineEdit(self.layoutWidgeti1)
        font = QtGui.QFont()
        font.setFamily("Consolas")
        self.policy_lineEditi.setFont(font)
        self.policy_lineEditi.setCursor(QtGui.QCursor(QtCore.Qt.SizeVerCursor))
        self.policy_lineEditi.setLayoutDirection(QtCore.Qt.LeftToRight)
        self.policy_lineEditi.setAutoFillBackground(False)
        self.policy_lineEditi.setStyleSheet("background-color: rgb(255, 255, 255);")
        self.policy_lineEditi.setReadOnly(True)
        self.policy_lineEditi.setObjectName("policy_lineEditi")
        self.gridLayouti.addWidget(self.policy_lineEditi, 1, 0, 1, 1)


        self.policy_buttoni = QtWidgets.QPushButton(self.layoutWidgeti1)
        self.policy_buttoni.setAutoFillBackground(False)
        self.policy_buttoni.setStyleSheet("background-color: rgb(225, 225, 225);\n"
"selection-background-color: rgb(229, 241, 251);")
        self.policy_buttoni.setCheckable(False)
        self.policy_buttoni.setChecked(False)
        self.policy_buttoni.setObjectName("policy_buttoni")
        self.gridLayouti.addWidget(self.policy_buttoni, 1, 1, 1, 1)

        self.gridLayouti_2.addLayout(self.gridLayouti, 0, 0, 1, 1)

        self.layoutWidgeti2 = QtWidgets.QWidget(ISIS_Syn_Dialog)
        self.layoutWidgeti2.setGeometry(QtCore.QRect(7, 150, 431, 411))
        self.layoutWidgeti2.setObjectName("layoutWidgeti2")
        self.gridLayouti_3 = QtWidgets.QGridLayout(self.layoutWidgeti2)
        self.gridLayouti_3.setContentsMargins(0, 0, 0, 0)
        self.gridLayouti_3.setObjectName("gridLayouti_3")
        self.labeli = QtWidgets.QLabel(self.layoutWidgeti2)
        font = QtGui.QFont()
        font.setFamily("宋体")
        font.setPointSize(10)
        self.labeli.setFont(font)
        self.labeli.setObjectName("labeli")
        self.gridLayouti_3.addWidget(self.labeli, 0, 0, 1, 1)

        self.input_browseri = QtWidgets.QTextBrowser(self.layoutWidgeti2)
        font = QtGui.QFont()
        font.setFamily("Consolas")
        self.input_browseri.setFont(font)
        self.input_browseri.setAutoFillBackground(True)
        self.input_browseri.setStyleSheet("background-color: rgb(255, 255, 255);")
        self.input_browseri.setSizeAdjustPolicy(QtWidgets.QAbstractScrollArea.AdjustToContents)
        self.input_browseri.setLineWrapMode(QtWidgets.QTextEdit.NoWrap)
        self.input_browseri.setObjectName("input_browseri")
        self.gridLayouti_3.addWidget(self.input_browseri, 1, 0, 1, 1)
        self.retranslateUi(ISIS_Syn_Dialog)
        QtCore.QMetaObject.connectSlotsByName(ISIS_Syn_Dialog)


    def retranslateUi(self, ISIS_Syn_Dialog):
        _translate = QtCore.QCoreApplication.translate
        ISIS_Syn_Dialog.setWindowTitle(_translate("ISIS_Syn_Dialog", "AutoSRv6 ISIS配置综合"))
        self.start1_button.setText(_translate("ISIS_Syn_Dialog", "读取"))
        self.isis_syn_button.setText(_translate("ISIS_Syn_Dialog", "ISIS参数求解"))
        self.labeli_2.setText(_translate("ISIS_Syn_Dialog", "ISIS 参数求解结果："))
        self.output_browseri.setDocumentTitle(_translate("ISIS_Syn_Dialog", "输入信息"))
        self.topo_lineEditi.setText(_translate("ISIS_Syn_Dialog", "请选择拓扑文件路径"))
        self.topo_buttoni.setText(_translate("ISIS_Syn_Dialog", "选择"))
        self.policy_lineEditi.setText(_translate("ISIS_Syn_Dialog", "请选择意图文件路径"))
        self.policy_buttoni.setText(_translate("ISIS_Syn_Dialog", "选择"))
        self.labeli.setText(_translate("ISIS_Syn_Dialog", "输入信息："))
        self.input_browseri.setDocumentTitle(_translate("ISIS_Syn_Dialog", "输入网络拓扑和意图信息"))