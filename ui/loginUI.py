#!/usr/bin/env python
# -*- coding: utf-8 -*-
'''
@Project ：AutoSRv6 
@File ：loginUI.py
@Author ：Lucky
@Date ：2023/4/27 13:18 
'''
from PyQt5.QtWidgets import QApplication, QWidget, QLabel, QLineEdit, QPushButton, QHBoxLayout, QVBoxLayout
from PyQt5.QtGui import QIcon, QPixmap, QFont
from PyQt5.QtCore import Qt

class LoginWindow(QWidget):
    def __init__(self):
        super().__init__()

        # 设置窗口标题和图标
        self.setWindowTitle('AutoSRv6')
        #self.setWindowIcon(QIcon('icon.png'))
        self.setFixedSize(800,600)
        # 创建用户名和密码标签、输入框和登录按钮

        # 设置标题标签
        title_label = QLabel('基于意图的SRv6配置综合系统')
        title_label.setAlignment(Qt.AlignCenter)
        title_label.setFont(QFont('Arial', -1, 200))
        title_label.setStyleSheet('''
            color: #000000; /* 设置文字颜色为亮蓝色 */
            font-weight: bold; /* 加粗文字 */
            font-family: "楷体";
            text-shadow: 2px 2px 4px #000000; /* 设置文字阴影 */
            font-size: 35px
        ''')

        user_label = QLabel('用户名：')
        self.user_edit = QLineEdit()
        pass_label = QLabel('密  码：')
        self.pass_edit = QLineEdit()
        self.pass_edit.setEchoMode(QLineEdit.Password)
        self.login_button = QPushButton('登 录')
        self._button = QPushButton('')
        # 设置样式
        style_sheet = """
                    QWidget {
                        background-color: #F2F2F2;
                    }
                    QLabel {
                        font-size: 16px;
                        font-weight: bold;
                        
                    }
                    
                    QLineEdit, QPushButton {
                        padding: 8px;
                        border: 2px solid #E5E5E5;

                        border-radius: 5px;
                        font-size: 20px;
                        font-weight: normal;
                    }
                    QPushButton {
                        background-color: #4CAF50;
                        color: white;
                        width:400px
                    }
                    QPushButton:hover {
                        background-color: #3E8E41;
                    }
                """
        self.setStyleSheet(style_sheet)

        # 将标签、输入框和按钮添加到水平布局中
        h_layout0 = QHBoxLayout()
        h_layout0.addWidget(title_label)

        h_layout1 = QHBoxLayout()
        h_layout1.addWidget(user_label)
        h_layout1.addWidget(self.user_edit)
        h_layout2 = QHBoxLayout()
        h_layout2.addWidget(pass_label)
        h_layout2.addWidget(self.pass_edit)
        h_layout3 = QHBoxLayout()
        h_layout3.addStretch(1)
        h_layout3.addWidget(self.login_button)
        h_layout3.addStretch(1)

        # 将水平布局添加到垂直布局中
        v_layout = QVBoxLayout()
        v_layout.addStretch(1)
        v_layout.addLayout(h_layout0)
        v_layout.addSpacing(50)
        v_layout.addLayout(h_layout1)
        v_layout.addSpacing(5)
        v_layout.addLayout(h_layout2)
        v_layout.addSpacing(20)
        v_layout.addLayout(h_layout3)
        v_layout.addSpacing(30)
        v_layout.addStretch(1)

        # 设置窗口的布局
        self.setLayout(v_layout)


if __name__ == '__main__':
    app = QApplication([])
    window = LoginWindow()
    window.show()
    app.exec_()
