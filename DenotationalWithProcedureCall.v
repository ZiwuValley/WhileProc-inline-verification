Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Psatz.
Require Import Coq.Classes.Equivalence.
Require Import Coq.Classes.Morphisms.
Require Import SetsClass.SetsClass. Import SetsNotation.
Require Import PL.InductiveType.
Require Import PL.RecurProp.
Require Import PL.Syntax.
Local Open Scope string.
Local Open Scope Z.
Local Open Scope sets.

(** * 一个极简的指令式程序语言：SimpleWhile *)

(** 在Coq中，我们就用字符串表示变量名，*)

Definition var_name: Type := string.

Declare Custom Entry prog_lang_entry.

Module Lang_SimpleWhile.

(** 并且使用Coq归纳类型定义表达式和语句的语法树。*)

Inductive expr_int : Type :=
  | EConst (n: Z): expr_int
  | EVar (x: var_name): expr_int
  | EAdd (e1 e2: expr_int): expr_int
  | ESub (e1 e2: expr_int): expr_int
  | EMul (e1 e2: expr_int): expr_int.

Inductive expr_bool: Type :=
  | ETrue: expr_bool
  | EFalse: expr_bool
  | ELt (e1 e2: expr_int): expr_bool
  | EAnd (e1 e2: expr_bool): expr_bool
  | ENot (e: expr_bool): expr_bool.

Inductive com : Type :=
  | CSkip: com
  | CAsgn (x: var_name) (e: expr_int): com
  | CSeq (c1 c2: com): com
  | CIf (e: expr_bool) (c1 c2: com): com
  | CWhile (e: expr_bool) (c: com): com.
  | CProcCall (f: proc_name) (es: list expr): com.

(** 在Coq中，可以利用_[Notation]_使得这些表达式和程序语句更加易读。*)

Definition EVar': string -> expr_int := EVar.
Coercion EConst: Z >-> expr_int.
Coercion EVar: var_name >-> expr_int.
Coercion EVar': string >-> expr_int.
Notation "[[ e ]]" := e
  (at level 0, e custom prog_lang_entry at level 99).
Notation "( x )" := x
  (in custom prog_lang_entry, x custom prog_lang_entry at level 99).
Notation "x" := x
  (in custom prog_lang_entry at level 0, x constr at level 0).
Notation "f x" := (f x)
  (in custom prog_lang_entry at level 1, only parsing,
   f custom prog_lang_entry,
   x custom prog_lang_entry at level 0).
Notation "x * y" := (EMul x y)
  (in custom prog_lang_entry at level 11, left associativity).
Notation "x + y" := (EAdd x y)
  (in custom prog_lang_entry at level 12, left associativity).
Notation "x - y" := (ESub x y)
  (in custom prog_lang_entry at level 12, left associativity).
Notation "x < y" := (ELt x y)
  (in custom prog_lang_entry at level 13, no associativity).
Notation "x && y" := (EAnd x y)
  (in custom prog_lang_entry at level 14, left associativity).
Notation "! x" := (ENot x)
  (in custom prog_lang_entry at level 10).
Notation "x = e" := (CAsgn x e)
  (in custom prog_lang_entry at level 18, no associativity).
Notation "c1 ; c2" := (CSeq c1 c2)
  (in custom prog_lang_entry at level 20, right associativity).
Notation "'skip'" := (CSkip)
  (in custom prog_lang_entry at level 10).
Notation "'if' e 'then' '{' c1 '}' 'else' '{' c2 '}'" := (CIf e c1 c2)
  (in custom prog_lang_entry at level 19,
   e custom prog_lang_entry at level 5,
   c1 custom prog_lang_entry at level 99,
   c2 custom prog_lang_entry at level 99,
   format  "'if'  e  'then'  '{'  c1  '}'  'else'  '{'  c2  '}'").
Notation "'while' e 'do' '{' c1 '}'" := (CWhile e c1)
  (in custom prog_lang_entry at level 19,
   e custom prog_lang_entry at level 5,
   c1 custom prog_lang_entry at level 99).

(** 使用_[Notation]_的效果如下：*)

Check [[1 + "x"]].
Check [["x" * ("a" + "b" + 1)]].
Check [[1 + "x" < "x"]].
Check [["x" < 0 && 0 < "y"]].
Check [["x" = "x" + 1]].
Check [[while (0 < "x") do { "x" = "x" - 1}]].


End Lang_SimpleWhile.