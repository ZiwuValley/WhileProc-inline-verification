# SimpleWhile 语言中函数的语义定义与简单函数内联语法等价性的证明

## 						—— CS2205 - Programming Language 理论任务

### 一、小组信息

- 组长：王许诺
- 组员：范昊翀、刘家宁、吴雨翔、周航

### 二、编译与运行

在 Linux 环境下，在 `WhileProc-inline-verification` 文件夹下，输入

```
make depend
make
```

进行编译，得到的 `Syntax.v` `Semantics.v` `Semantics_Inline_func.v` 即为作业内容

### 三、项目内容

`Syntax.v` 中，基于课堂上提到的 SimpleWhile 语言的语法，加入了 Function Call 部分

语言整体的解析分为表达式和语句两种类型，表达式支持整数类型以及布尔类型

同时，函数调用的形式为按照调用函数名，从函数表中寻找对应函数

`Semantic.v` 中，我们定义了新语言的语义算子

和 SimpleWhile 语言不同，由于函数的存在会导致表达式也可能修改程序状态，这里我们将表达式的语义也定义为：

（执行前程序状态，返回值，执行后程序状态）

的三元组，并在此基础上定义了各个表达式和语句的语意

`Semantics_Inline_func.v` 中，我们假定函数全部不改变程序状态，只返回一个简单的表达式，在此基础上定义了函数的“内联”操作，即将函数调用直接展开，并证明了在函数返回值为常数，变量值，表达式等情况下，函数内联操作保持语义等价性

## Hint for Members （记得删）

新的代码放在 Assignment 文件夹下

在 Makefile 的第 41 行加入对应的文件名

如果要引用 Assignment/a.v，命令是

```
Require Import Assignment.a
```

编译命令

```
make clean
make depend
make -j4
```

记得修改 vscode 插件中的根文件夹！！！

记得把 CONFIGURE 文件复制过来