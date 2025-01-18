Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Psatz.
Require Import Coq.Classes.Equivalence.
Require Import Coq.Classes.Morphisms.
Require Import SetsClass.SetsClass. Import SetsNotation.
Require Import PL.InductiveType.
Require Import PL.RecurProp.
Require Import PL.Monad2.
Require Import Assignment.Syntax.
Require Import Assignment.FuncEquiv.
Require Import Coq.Lists.List.
Local Open Scope string.
Local Open Scope Z.
Local Open Scope sets.


(* 定义 SimplieWhile + 函数调用的语义算子*)

Module Semantics_SimpleWhileFunc.
Import StateRelMonad.
Import Lang_SimpleWhileFunc.

Definition var_name: Type := string.
Definition func_name: Type := string.
Definition state: Type := var_name -> Z.


(* 定义语义算子的类型，为state -> Z -> state的三元关系，每个semantic可以理解为三元组的集合 *)
Definition expr_int_sem: Type := state -> Z -> state -> Prop.
Definition expr_bool_sem: Type := state -> bool -> state -> Prop.
Definition com_sem: Type := state -> state -> Prop.
Definition func_list: Type := func_name -> list Z -> (expr_int_sem).


(* 定义五个基本语义算子的语义，如果这个三元组属于这个语义，implies "=>" 的右侧条件 *)
Definition const_sem (n: Z): expr_int_sem :=
  fun (s1: state) (res: Z) (s2: state) => res = n /\ s1 = s2.

Definition var_sem (x: var_name): expr_int_sem :=
  fun (s1: state) (res: Z) (s2: state) => res = (s1 x) /\ s1 = s2.

Definition add_sem (D1 D2: expr_int_sem): expr_int_sem :=
  fun (s1: state) (res: Z) (s3: state) =>
    exists (a: Z) (s2: state),
      (s1, a, s2) ∈ D1 /\ (s2, res - a, s3) ∈ D2.

Definition sub_sem (D1 D2: expr_int_sem): expr_int_sem :=
  fun (s1: state) (res: Z) (s3: state) =>
    exists (a: Z) (s2: state),
      (s1, a, s2) ∈ D1 /\ (s2, a - res, s3) ∈ D2.

Definition mul_sem (D1 D2: expr_int_sem): expr_int_sem :=
  fun (s1: state) (res: Z) (s3: state) =>
    exists (a: Z) (s2: state) (b: Z),
      a * b = res /\ (s1, a, s2) ∈ D1 /\ (s2, b, s3) ∈ D2.
  

(* 定义append_arg和bind_args两个辅助语义算子，用于处理函数的参数列表计算 *)
(* append_arg的作用是将一个参数添加到参数列表的头部 *)
(* bind_args的作用是将参数列表中的参数依次添加到参数列表的头部，吃进去一个表达式列表，返回一个semantic
   即从s1进去，这一坨表达式算出来的结果为一个整数列表，状态为s2 *)
Definition append_arg (Dargs: state -> (list Z) -> state -> Prop) (D: expr_int_sem): state -> (list Z) -> state -> Prop :=
  fun (s1: state) (res: list Z) (s3: state) =>
    exists (s2: state) (args: list Z) (arg: Z),
      cons arg args = res /\ (s2, args, s3) ∈ Dargs /\ (s1, arg, s2) ∈ D.

Fixpoint bind_args (Dargs: list expr_int_sem): state -> (list Z) -> state -> Prop :=
  match Dargs with
  | nil => ret state (list Z) nil
  | cons a l' => append_arg (bind_args l') a
  end.


(* 定义函数调用的语义算子，(s1, args, s2)在算完参数列表的语义里，(s2, res, s3)在函数运算的语义里*)
Definition func_sem (f: (list Z) -> expr_int_sem) (Dargs: list expr_int_sem): expr_int_sem :=
  fun (s1: state) (res: Z) (s3: state) =>
    exists (s2: state) (args: list Z),
      (s1, args, s2) ∈ bind_args Dargs /\ (s2, res, s3) ∈ f args.


(* 定义布尔类型算子的语义，同上 *)
Definition true_sem: expr_bool_sem :=
  fun (s1: state) (res: bool) (s2: state) => res = true /\ s1 = s2.

Definition false_sem: expr_bool_sem :=
  fun (s1: state) (res: bool) (s2: state) => res = false /\ s1 = s2.

Definition lt_sem (D1 D2: expr_int_sem): expr_bool_sem :=
  fun (s1: state) (res: bool) (s3: state) =>
    exists (lhs rhs: Z) (s2: state),
      (s1, lhs, s2) ∈ D1 /\ (s2, rhs, s3) ∈ D2 /\ (res = if Z_lt_dec lhs rhs then true else false).

Definition and_sem (D1 D2: expr_bool_sem): expr_bool_sem :=
  fun (s1: state) (res: bool) (s3: state) =>
    ((s1, false, s3) ∈ D1 /\ res = false) \/
      exists (s2: state),
        (s1, true, s2) ∈ D1 /\ (s2, res, s3) ∈ D2.

Definition not_sem (D: expr_bool_sem): expr_bool_sem :=
  fun (s1: state) (res: bool) (s2: state) =>
    (s1, negb res, s2) ∈ D.


(* 定义过程语义算子，同上 *)
Definition skip_sem: com_sem :=
  Rels.id.

Definition seq_sem (D1 D2: com_sem): com_sem :=
  D1 ∘ D2.

Definition asgn_sem (X: var_name) (D: expr_int_sem): com_sem :=
  fun (s1 s3: state) =>
    exists (s2: state) (res: Z),
      (s1, res, s2) ∈ D /\ s3 X = res /\
        forall Y, X <> Y -> s2 Y = s3 Y.

Definition test_true (D: expr_bool_sem): com_sem :=
  fun (s1: state) (s2: state) => (s1, true, s2) ∈ D.

Definition test_false (D: expr_bool_sem): com_sem :=
  fun (s1: state) (s2: state) => (s1, false, s2) ∈ D.

Definition if_sem (D0: expr_bool_sem) (D1 D2: com_sem): com_sem :=
  (test_true D0 ∘ D1) ∪ (test_false D0 ∘ D2).

Fixpoint boundedLB (D0: expr_bool_sem) (D1: com_sem) (n: nat): com_sem :=
  match n with
  | O => ∅
  | S n0 =>
      (test_true D0 ∘ D1 ∘ boundedLB D0 D1 n0) ∪ (test_false D0)
  end.

Definition while_sem (D0: expr_bool_sem) (D1: com_sem): com_sem :=
  ⋃ (boundedLB D0 D1).


(* 定义表达式和命令的求值算子 *)
(* eval_expr_int可以展开为以下六种情况：*)
Fixpoint eval_expr_int (fs: func_list) (e: expr_int) {struct e}: expr_int_sem :=
  match e with
  | EConst n => const_sem n (* 常量求值 *)
  | EVar X => var_sem X (* 变量求值 *)
  | EAdd e1 e2 => add_sem (eval_expr_int fs e1) (eval_expr_int fs e2) (* 加法求值 *)
  | ESub e1 e2 => sub_sem (eval_expr_int fs e1) (eval_expr_int fs e2) (* 减法求值 *)
  | EMul e1 e2 => mul_sem (eval_expr_int fs e1) (eval_expr_int fs e2) (* 乘法求值 *)
  | EFunc f args => func_sem (fs f) (map (eval_expr_int fs) args)  (* 函数调用求值 *)
  end.

(* eval_expr_bool可以展开为以下五种情况：*)
Fixpoint eval_expr_bool (fs: func_list) (e: expr_bool): expr_bool_sem :=
  match e with
  | ETrue => true_sem (* 真值求值 *)
  | EFalse => false_sem (* 假值求值 *)
  | ELt e1 e2 => lt_sem (eval_expr_int fs e1) (eval_expr_int fs e2) (* 小于求值 *)
  | EAnd e1 e2 => and_sem (eval_expr_bool fs e1) (eval_expr_bool fs e2) (* 与求值 *)
  | ENot e1 => not_sem (eval_expr_bool fs e1) (* 非求值 *)
  end.

(* eval_com可以展开为以下五种情况：*)
Fixpoint eval_com (fs: func_list) (c: com): com_sem :=
  match c with
  | CSkip =>
    skip_sem  (* 空语句求值 *)
  | CAsgn X e =>
    asgn_sem X (eval_expr_int fs e) (* 赋值语句求值 *)
  | CSeq c1 c2 =>
    seq_sem (eval_com fs c1) (eval_com fs c2) (* 顺序语句求值 *)
  | CIf e c1 c2 =>
    if_sem (eval_expr_bool fs e) (eval_com fs c1) (eval_com fs c2)  (* 条件语句求值 *)
  | CWhile e c1 =>
    while_sem (eval_expr_bool fs e) (eval_com fs c1)  (* 循环语句求值 *)
  end.

(* 证明各个语义算子能够保持等价关系 *)
(* 若传入的常数相同，则语义等价，下同*)
#[export] Instance const_sem_congr:
  Proper (eq ==> Sets.equiv) const_sem.
Proof.
  unfold Proper, respectful.
  intros.
  unfold const_sem.
  rewrite H.
  reflexivity.
Qed.

#[export] Instance var_sem_congr:
  Proper (eq ==> Sets.equiv) var_sem.
Proof.
  unfold Proper, respectful.
  intros.
  unfold var_sem.
  rewrite H.
  reflexivity.
Qed.

#[export] Instance add_sem_congr:
  Proper (Sets.equiv ==>  Sets.equiv ==>  Sets.equiv) add_sem.
Proof.
  unfold Proper, respectful.
  intros D11 D12 H1 D21 D22 H2.
  unfold add_sem.
  intros s1 res s2.
  split.
  + intros. destruct H as [a H]. destruct H as [s3 H].
    exists a. exists s3.
    rewrite <- H1, <- H2.
    tauto.
  + intros. destruct H as [a H]. destruct H as [s3 H].
    exists a. exists s3.
    rewrite H1, H2.
    tauto.
Qed.

#[export] Instance sub_sem_congr:
  Proper (Sets.equiv ==>  Sets.equiv ==>  Sets.equiv) sub_sem.
Proof.
  unfold Proper, respectful.
  intros D11 D12 H1 D21 D22 H2.
  unfold sub_sem.
  intros s1 res s2.
  split.
  + intros. destruct H as [a H]. destruct H as [s3 H].
    exists a. exists s3.
    rewrite <- H1, <- H2.
    tauto.
  + intros. destruct H as [a H]. destruct H as [s3 H].
    exists a. exists s3.
    rewrite H1, H2.
    tauto.
Qed.

#[export] Instance mul_sem_congr:
  Proper (Sets.equiv ==>  Sets.equiv ==>  Sets.equiv) mul_sem.
Proof.
  unfold Proper, respectful.
  intros D11 D12 H1 D21 D22 H2.
  unfold mul_sem.
  intros s1 res s2.
  split.
  + intros. destruct H as [a H]. destruct H as [s3 H]. destruct H as [b H].
    exists a. exists s3. exists b.
    rewrite <- H1, <- H2.
    tauto.
  + intros. destruct H as [a H]. destruct H as [s3 H]. destruct H as [b H].
    exists a. exists s3. exists b.
    rewrite H1, H2.
    tauto.
Qed.

(* 证明append_arg和bind_args两个辅助语义算子能够保持等价/包含关系 *)
#[export] Instance append_arg_mono:
  Proper (Sets.included ==> Sets.equiv ==> Sets.included) append_arg.
Proof.
  unfold Proper, respectful.
  intros Dargs1 Dargs2 H1 D1 D2 H2.
  unfold append_arg.
  intros s1 res s2.
  intros. sets_unfold.
  intros.
  destruct H as [s3 H]. destruct H as [args H]. destruct H as [arg H].
  exists s3. exists args. exists arg.
  sets_unfold in H2. specialize (H2 s1 arg s3).
  destruct H as (H3 & H4 & H5).
  apply H2 in H5.
  sets_unfold in H1. specialize (H1 s3 args s2).
  apply H1 in H4.
  tauto.
Qed.

(* 定义了list expr_int_sem的等价关系 *)
Definition list_expr_int_sem_equiv:
  (list expr_int_sem) -> (list expr_int_sem) -> Prop :=
  list_relation Sets.equiv.

(* 证明list_expr_int_sem_equiv是等价关系 *)
#[export] Instance list_expr_int_sem_equiv_equiv:
  Equivalence list_expr_int_sem_equiv.
Proof.
  unfold list_expr_int_sem_equiv.
  apply list_equivalence.
  pose proof Sets_equiv_equiv.
  destruct H.
  split.
  + unfold Reflexive. reflexivity.
  + unfold Symmetric. symmetry. tauto.
  + unfold Transitive. intros. transitivity y. tauto. tauto.
Qed.

(* Lemma func_to_set_3types (A B C: Type):
  forall (f: A -> B -> C -> Prop) (x: A) (y: B) (z: C), (f x y z) = ((x, y, z) ∈ f).
Proof.
  intros. sets_unfold. tauto.
Qed. *)

#[export] Instance bind_args_congr:
  Proper (list_expr_int_sem_equiv ==> Sets.equiv) bind_args.
Proof.
  unfold Proper, respectful.
  intros Dargs1 Dargs2 H1.
  unfold bind_args.
  apply Sets_equiv_Sets_included. split.
  + intros. revert H1. revert Dargs2. induction Dargs1; intros Dargs2 H1; destruct Dargs2.
    - reflexivity.
    - unfold list_expr_int_sem_equiv, list_relation in H1. tauto.
    - unfold list_expr_int_sem_equiv, list_relation in H1. tauto.
    - unfold list_expr_int_sem_equiv, list_relation in H1. destruct H1 as [? ?].
      specialize (IHDargs1 Dargs2 H0).
      assert (list_expr_int_sem_equiv Dargs1 Dargs2). tauto. clear H0.
      fold bind_args in IHDargs1. fold bind_args.
      rewrite <- H. rewrite IHDargs1. reflexivity.
  + intros. revert H1. revert Dargs1. induction Dargs2; intros Dargs1 H1; destruct Dargs1.
    - reflexivity.
    - unfold list_expr_int_sem_equiv, list_relation in H1. tauto.
    - unfold list_expr_int_sem_equiv, list_relation in H1. tauto.
    - unfold list_expr_int_sem_equiv, list_relation in H1. destruct H1 as [? ?].
      specialize (IHDargs2 Dargs1 H0).
      assert (list_expr_int_sem_equiv Dargs1 Dargs2). tauto. clear H0.
      fold bind_args in IHDargs2. fold bind_args.
      rewrite <- H. rewrite IHDargs2. reflexivity.
Qed.

(* 证明函数调用的语义算子能够保持等价关系 *)
#[export] Instance func_sem_congr:
  Proper (func_equiv _ _ ==> list_expr_int_sem_equiv ==> Sets.equiv) func_sem.
Proof.
  unfold Proper, respectful.
  intros f g H1 args1 args2 H2.
  unfold func_sem.
  intros s1 res s2.
  split.
  + intros. destruct H as [a H]. destruct H as [s3 H]. destruct H as [b H].
    exists a. exists s3.
    rewrite <- H1, <- H2.
    tauto.
  + intros. destruct H as [a H]. destruct H as [s3 H]. destruct H as [b H].
    exists a. exists s3.
    rewrite H1, H2.
    tauto.
Qed.

#[export] Instance lt_sem_congr:
  Proper (Sets.equiv ==> Sets.equiv ==> Sets.equiv) lt_sem.
Proof.
  unfold Proper, respectful.
  intros.
  unfold lt_sem.
  intros s1 res s3.
  split; intros;
  destruct H1 as [lhs H1];
  destruct H1 as [rhs H1];
  destruct H1 as [s2 H1].
  + rewrite H, H0 in H1.
    exists lhs. exists rhs. exists s2.
    tauto.
  + rewrite <- H, <- H0 in H1.
    exists lhs. exists rhs. exists s2.
    tauto.
Qed.

#[export] Instance and_sem_congr:
  Proper (Sets.equiv ==> Sets.equiv ==> Sets.equiv) and_sem.
Proof.
  unfold Proper, respectful.
  intros.
  unfold and_sem.
  intros s1 res s3.
  split; intros.
  + destruct H1 as [? | ?].
    - rewrite H in H1.
      left. tauto.
    - destruct H1 as [s2 H1].
      rewrite H, H0 in H1.
      right. exists s2. tauto.
  + destruct H1 as [? | ?].
    - rewrite <- H in H1.
      left. tauto.
    - destruct H1 as [s2 H1].
      rewrite <- H, <- H0 in H1.
      right. exists s2. tauto.
Qed.

#[export] Instance not_sem_congr:
  Proper (Sets.equiv ==> Sets.equiv) not_sem.
Proof.
  unfold Proper, respectful.
  intros.
  unfold not_sem.
  intros s1 res s2.
  rewrite H.
  reflexivity.
Qed.

#[export] Instance seq_sem_congr:
  Proper (Sets.equiv ==> Sets.equiv ==> Sets.equiv) seq_sem.
Proof. apply Rels_concat_congr. Qed.

#[export] Instance asgn_sem_congr:
  Proper (eq ==> Sets.equiv ==> Sets.equiv) asgn_sem.
Proof.
  unfold Proper, respectful.
  intros.
  unfold asgn_sem.
  intros s1 s3.
  split; intros;
  destruct H1 as [s2 H1];
  destruct H1 as [res H1].
  + rewrite H, H0 in H1.
    exists s2. exists res.
    tauto.
  + exists s2. exists res.
    rewrite H, H0.
    tauto.
Qed.

#[export] Instance test_true_congr:
  Proper (Sets.equiv ==> Sets.equiv) test_true.
Proof.
  unfold Proper, respectful.
  intros.
  unfold test_true.
  intros s1 s2.
  rewrite H.
  reflexivity.
Qed.

#[export] Instance test_false_congr:
  Proper (Sets.equiv ==> Sets.equiv) test_false.
Proof.
  unfold Proper, respectful.
  intros.
  unfold test_false.
  intros s1 s2.
  rewrite H.
  reflexivity.
Qed.

#[export] Instance if_sem_congr:
  Proper (Sets.equiv ==> Sets.equiv ==> Sets.equiv ==> Sets.equiv) if_sem.
Proof.
  unfold Proper, respectful.
  intros.
  unfold if_sem.
  rewrite H, H0, H1.
  reflexivity.
Qed.

#[export] Instance while_sem_congr:
  Proper (Sets.equiv ==> Sets.equiv ==> Sets.equiv) while_sem.
Proof.
  unfold Proper, respectful.
  intros.
  unfold while_sem.
  apply Sets_indexed_union_congr.
  intros n.
  induction n; simpl.
  + reflexivity.
  + rewrite IHn, H, H0. reflexivity.
Qed.

(* 定义整数表达式的语义等价关系 *)
(* 语义等价关系是指，对于任意传入的函数列表，两个表达式的语义等价，即算出来的三元组集合相同 *)
Definition iequiv (e1 e2: expr_int): Prop :=
  forall fs, Sets.equiv (eval_expr_int fs e1) (eval_expr_int fs e2).

(* 证明iequiv是等价关系 *)
#[export] Instance iequiv_equiv: Equivalence iequiv.
Proof.
  unfold iequiv.
  split.
  + unfold Reflexive. reflexivity.
  + unfold Symmetric. symmetry. apply (H fs).
  + unfold Transitive. intros. transitivity (eval_expr_int fs y).
    - apply (H fs). - apply (H0 fs).
Qed.

(* 同上 *)
Definition bequiv (e1 e2: expr_bool): Prop :=
  forall fs, Sets.equiv (eval_expr_bool fs e1) (eval_expr_bool fs e2).

#[export] Instance bequiv_equiv: Equivalence bequiv.
Proof.
  unfold bequiv.
  split.
  + unfold Reflexive. reflexivity.
  + unfold Symmetric. symmetry. apply (H fs).
  + unfold Transitive. intros. transitivity (eval_expr_bool fs y).
    - apply (H fs). - apply (H0 fs).
Qed.

Definition cequiv (e1 e2: com): Prop :=
  forall fs, Sets.equiv (eval_com fs e1) (eval_com fs e2).

#[export] Instance cequiv_equiv: Equivalence cequiv.
Proof.
  unfold cequiv.
  split.
  + unfold Reflexive. reflexivity.
  + unfold Symmetric. symmetry. apply (H fs).
  + unfold Transitive. intros. transitivity (eval_com fs y).
    - apply (H fs). - apply (H0 fs).
Qed.

(* 证明各个语义算子能够保持等价关系 *)
(* 若传入的常数相同，则语义等价，下同 *)
#[export] Instance EConst_congr:
  Proper (eq ==> iequiv) EConst.
Proof.
  unfold Proper, respectful, iequiv.
  intros.
  apply const_sem_congr.
  tauto.
Qed.

#[export] Instance EVar_congr:
  Proper (eq ==> iequiv) EVar.
Proof.
  unfold Proper, respectful, iequiv.
  intros.
  apply var_sem_congr.
  tauto.
Qed.

#[export] Instance EAdd_congr:
  Proper (iequiv ==> iequiv ==> iequiv) EAdd.
Proof.
  unfold Proper, respectful, iequiv.
  intros; simpl.
  apply add_sem_congr.
  + apply (H fs). + apply (H0 fs).
Qed.

#[export] Instance ESub_congr:
  Proper (iequiv ==> iequiv ==> iequiv) ESub.
Proof.
  unfold Proper, respectful, iequiv.
  intros; simpl.
  apply sub_sem_congr.
  + apply (H fs). + apply (H0 fs).
Qed.

#[export] Instance EMul_congr:
  Proper (iequiv ==> iequiv ==> iequiv) EMul.
Proof.
  unfold Proper, respectful, iequiv.
  intros; simpl.
  apply mul_sem_congr.
  + apply (H fs). + apply (H0 fs).
Qed.

#[export] Instance ELt_congr:
  Proper (iequiv ==> iequiv ==> bequiv) ELt.
Proof.
  unfold Proper, respectful, iequiv, bequiv.
  intros; simpl.
  apply lt_sem_congr.
  + apply (H fs). + apply (H0 fs).
Qed.

#[export] Instance EAnd_congr:
  Proper (bequiv ==> bequiv ==> bequiv) EAnd.
Proof.
  unfold Proper, respectful, bequiv.
  intros; simpl.
  apply and_sem_congr.
  + apply (H fs). + apply (H0 fs).
Qed.

#[export] Instance ENot_congr:
  Proper (bequiv ==> bequiv) ENot.
Proof.
  unfold Proper, respectful, bequiv.
  intros; simpl.
  apply not_sem_congr.
  apply (H fs).
Qed.

#[export] Instance CAsgn_congr:
  Proper (eq ==> iequiv ==> cequiv) CAsgn.
Proof.
  unfold Proper, respectful, iequiv, cequiv.
  intros; simpl.
  apply asgn_sem_congr.
  + tauto. + apply (H0 fs).
Qed.

#[export] Instance CSeq_congr:
  Proper (cequiv ==> cequiv ==> cequiv) CSeq.
Proof.
  unfold Proper, respectful, cequiv.
  intros; simpl.
  apply seq_sem_congr.
  + apply (H fs). + apply (H0 fs).
Qed.

#[export] Instance CIf_congr:
  Proper (bequiv ==> cequiv ==> cequiv ==> cequiv) CIf.
Proof.
  unfold Proper, respectful, bequiv, cequiv.
  intros; simpl.
  apply if_sem_congr.
  + apply (H fs). + apply (H0 fs). + apply (H1 fs).
Qed.

#[export] Instance CWhile_congr:
  Proper (bequiv ==> cequiv ==> cequiv) CWhile.
Proof.
  unfold Proper, respectful, bequiv, cequiv.
  intros; simpl.
  apply while_sem_congr.
  + apply (H fs). + apply (H0 fs).
Qed.

(* 定义列表的等价关系 *)
Definition list_iequiv:
  (list expr_int) -> (list expr_int) -> Prop :=
  list_relation iequiv.

(* 证明list_iequiv是等价关系 *)
#[export] Instance list_iequiv_equiv:
  Equivalence list_iequiv.
Proof.
  unfold list_iequiv.
  apply list_equivalence.
  split.
  + unfold Reflexive. reflexivity.
  + unfold Symmetric. symmetry. tauto.
  + unfold Transitive. intros. transitivity y. tauto. tauto.
Qed.

(* 定义 func_iequiv_sequiv: 用于描述两个从 expr_int 到 expr_int_sem 的函数 f 和 g 的等价性。*)
Definition func_iequiv_sequiv:
  (expr_int -> expr_int_sem) -> (expr_int -> expr_int_sem) -> Prop :=
  fun f g =>
  exists (fs1 fs2: func_list),
  (* f 和 g 分别由列表 fs1 和 fs2 经 eval_expr_int 解释得到。 *)
  f = (eval_expr_int fs1) /\ g = (eval_expr_int fs2) /\
  (* 对于任意等价的表达式 a 和 b，f a 和 g b 的集合值是等价的。 *)
  forall a b: expr_int, iequiv a b -> Sets.equiv (f a) (g b).

(* 证明 func_iequiv_sequiv 是一个自反关系。 *)
Lemma func_iequiv_sequiv_reflexive:
  forall fs, func_iequiv_sequiv (eval_expr_int fs) (eval_expr_int fs).
Proof.
  intros.
  unfold func_iequiv_sequiv.
  (* 构造存在的 fs1 和 fs2，即两个相同的函数列表 fs。 *)
  exists fs. exists fs.
  split. reflexivity. (* f = eval_expr_int fs *)
  split. reflexivity. (* g = eval_expr_int fs *)
  (* 对于任意等价的表达式 a 和 b，直接从假设 iequiv a b 推出等价性。 *)
  unfold iequiv. intros.
  apply H.
Qed.

(* 证明如果函数和输入列表在等价性关系下等价，
   那么通过 map 映射, 把参数列表计算之后的结果列表也是等价的。 *)
#[export] Instance map_func_congr:
  Proper (func_iequiv_sequiv ==> list_iequiv ==> list_expr_int_sem_equiv)
    (@map expr_int expr_int_sem).
Proof.
  unfold Proper, respectful.
  intros.
  unfold list_expr_int_sem_equiv.
  unfold list_relation.
  (* 对两个列表 x0 和 y0 进行递归分析。 *)
  revert H0. revert y0.
  induction x0; destruct y0; intros.
  + (* 基本情况：两个空列表，直接成立。 *)
    unfold map. auto.
  + (* 矛盾情况：一个为空列表，一个非空，根据 list_iequiv 定义矛盾。 *)
    unfold list_iequiv in H0. unfold list_relation in H0. tauto.
  + (* 矛盾情况同上，另一个方向。 *)
    unfold list_iequiv in H0. unfold list_relation in H0. tauto.
  + (* 递归情况：两个非空列表，分解头部和尾部进行处理。 *)
    unfold list_iequiv in H0. unfold list_relation in H0. destruct H0 as [H1 H2].
    assert (list_iequiv x0 y0). tauto. clear H2.
    specialize (IHx0 y0 H0).
    unfold map. split.
    - (* 证明两头部元素经过 map 映射后的结果等价。 *)
      unfold func_iequiv_sequiv in H. destruct H as [fs1 H]. destruct H as [fs2 H].
      destruct H as (H2 & H3 & H4).
      (* 利用 func_iequiv_sequiv 的定义，结合头部等价性 H1，推出结果等价性。 *)
      specialize (H4 a e H1). tauto.
    - (* 递归调用，证明尾部等价。 *)
      apply IHx0.
Qed.

(* 证明如果参数等价，则由 EFunc 构造的表达式语义等价。 *)
#[export] Instance EFunc_congr:
  Proper (eq ==> list_iequiv ==> iequiv) EFunc.
Proof.
  unfold Proper, respectful, iequiv.
  intros; simpl.
  apply func_sem_congr.
  + (* 第一个参数是完全相等的（使用 eq 的等价性）。 *)
    rewrite H. reflexivity.
  + (* 对第二个参数使用 map_func_congr 来证明保形性。 *)
    apply map_func_congr.
    - (* 函数部分等价性使用 func_iequiv_sequiv_reflexive。 *)
      apply func_iequiv_sequiv_reflexive.
    - (* 列表部分直接使用假设 H0。 *)
      apply H0.
Qed.

End Semantics_SimpleWhileFunc.