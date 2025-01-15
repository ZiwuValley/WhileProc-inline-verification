## Project

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