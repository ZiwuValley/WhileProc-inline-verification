Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Psatz.
Require Import Coq.Classes.Equivalence.
Require Import Coq.Classes.Morphisms.
Require Import SetsClass.SetsClass. Import SetsNotation.
Require Import PL.InductiveType.
Require Import PL.RecurProp.
Require Import PL.Monad.
Require Import Assignment.Syntax.
Local Open Scope string.
Local Open Scope Z.
Local Open Scope sets.


(* 定义 SimplieWhile + 函数调用的语义算子*)

Module Semantics_SimpleWhileFunc.

Definition state: Type := var_name -> Z.
Definition expr_int_sem: Type := StateMonad.M state Z.
Definition expr_bool_sem: Type := StateMonad.M state bool.
Definition com_sem: Type := state -> state -> Prop.

Definition const_sem (n: Z): expr_int_sem:
  StateMonad.ret n.


End Semantics_SimpleWhileFunc.