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

Definition expr_int_sem: Type := state -> Z -> state -> Prop.
Definition expr_bool_sem: Type := state -> bool -> state -> Prop.
Definition com_sem: Type := state -> state -> Prop.
Definition func_list: Type := func_name -> list Z -> (expr_int_sem).

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

Definition append_arg (Dargs: state -> (list Z) -> state -> Prop) (D: expr_int_sem): state -> (list Z) -> state -> Prop :=
  fun (s1: state) (res: list Z) (s3: state) =>
    exists (s2: state) (args: list Z) (arg: Z),
      cons arg args = res /\ (s2, args, s3) ∈ Dargs /\ (s1, arg, s2) ∈ D.

Fixpoint bind_args (Dargs: list expr_int_sem): state -> (list Z) -> state -> Prop :=
  match Dargs with
  | nil => ret state (list Z) nil
  | cons a l' => append_arg (bind_args l') a
  end.

Definition func_sem (f: (list Z) -> expr_int_sem) (Dargs: list expr_int_sem): expr_int_sem :=
  fun (s1: state) (res: Z) (s3: state) =>
    exists (s2: state) (args: list Z) (res: Z),
      (s1, args, s2) ∈ bind_args Dargs /\ (s2, res, s3) ∈ f args.

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
  fun (s1: state) (s2: state) =>
    exists (s2: state), (s1, true, s2) ∈ D.

Definition test_false (D: expr_bool_sem): com_sem :=
  fun (s1: state) (s2: state) =>
    exists (s2: state), (s1, false, s2) ∈ D.  

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

(* Fixpoint eval_expr_args (fs: func_list) (es: list expr_int) {struct es}: list expr_int_sem :=
    match es with
    | nil => nil
    | cons e es' => cons (eval_expr_int fs e) (eval_expr_args fs es')
    end. *)


Fixpoint eval_expr_int (fs: func_list) (e: expr_int) {struct e}: expr_int_sem :=
  match e with
  | EConst n => const_sem n
  | EVar X => var_sem X
  | EAdd e1 e2 => add_sem (eval_expr_int fs e1) (eval_expr_int fs e2)
  | ESub e1 e2 => sub_sem (eval_expr_int fs e1) (eval_expr_int fs e2)
  | EMul e1 e2 => mul_sem (eval_expr_int fs e1) (eval_expr_int fs e2)
  | EFunc f args => func_sem (fs f) (map (eval_expr_int fs) args)
  (* end
with eval_expr_args (fs: func_list) (es: list expr_int) {struct es}: list expr_int_sem :=
  match es with
  | nil => nil
  | cons e es' => cons (eval_expr_int fs e) (eval_expr_args fs es') *)
  end.


Fixpoint eval_expr_bool (fs: func_list) (e: expr_bool): expr_bool_sem :=
  match e with
  | ETrue => true_sem
  | EFalse => false_sem
  | ELt e1 e2 => lt_sem (eval_expr_int fs e1) (eval_expr_int fs e2)
  | EAnd e1 e2 => and_sem (eval_expr_bool fs e1) (eval_expr_bool fs e2)
  | ENot e1 => not_sem (eval_expr_bool fs e1)
  end.

Fixpoint eval_com (fs: func_list) (c: com): com_sem :=
  match c with
  | CSkip =>
    skip_sem
  | CAsgn X e =>
    asgn_sem X (eval_expr_int fs e)
  | CSeq c1 c2 =>
    seq_sem (eval_com fs c1) (eval_com fs c2)
  | CIf e c1 c2 =>
    if_sem (eval_expr_bool fs e) (eval_com fs c1) (eval_com fs c2)
  | CWhile e c1 =>
    while_sem (eval_expr_bool fs e) (eval_com fs c1)
  end.

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

#[export] Instance append_arg_congr:
  Proper (Sets.equiv ==> Sets.equiv ==> Sets.equiv) append_arg.
Proof.
  unfold Proper, respectful.
  intros Dargs1 Dargs2 H1 D1 D2 H2.
  unfold append_arg.
  intros s1 res s2.
  split.
  + intros. destruct H as [s3 H]. destruct H as [args H]. destruct H as [arg H].
    exists s3. exists args. exists arg.
    rewrite <- H1, <- H2. tauto.
  + intros. destruct H as [s3 H]. destruct H as [args H]. destruct H as [arg H].
    exists s3. exists args. exists arg.
    rewrite H1, H2. tauto.
Qed.

#[export] Instance bind_args_congr:
  Proper (eq ==> Sets.equiv) bind_args.
Proof.
  unfold Proper, respectful.
  intros Dargs1 Dargs2 H1.
  unfold bind_args.
  split. revert a a0 a1.
  intros s1 l s2.
  + intros. revert H1. revert Dargs2. induction Dargs1.
    - intros Dargs2 H1. rewrite <- H1. tauto.
    - intros Dargs2 H1. rewrite <- H1. tauto.
  + intros. revert H1. revert Dargs1. induction Dargs2.
    - intros Dargs1 H1. rewrite H1. tauto.
    - intros Dargs1 H1. rewrite H1. tauto.
Qed.

#[export] Instance func_sem_congr:
  Proper (func_equiv _ _ ==> eq ==> Sets.equiv) func_sem.
Proof.
  unfold Proper, respectful.
  intros f g H1 args1 args2 H2.
  unfold func_sem.
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

Definition iequiv (e1 e2: expr_int): Prop :=
  forall fs, Sets.equiv (eval_expr_int fs e1) (eval_expr_int fs e2).

#[export] Instance iequiv_equiv: Equivalence iequiv.
Proof.
  unfold iequiv.
  split.
  + unfold Reflexive. reflexivity.
  + unfold Symmetric. symmetry. apply (H fs).
  + unfold Transitive. intros. transitivity (eval_expr_int fs y).
    - apply (H fs). - apply (H0 fs).
Qed.

(* Definition list_iequiv:
  (list expr_int) -> (list expr_int) -> Prop := 
  func_equiv iequiv. *)

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

(* #[export] Instance EFunc_congr:
  Proper (iequiv ==> iequiv ==> iequiv) Efunc.
Proof.
  unfold Proper, respectful, iequiv.
  intros; simpl.
  apply mul_sem_congr.
  + apply (H fs). + apply (H0 fs).
Qed. *)




End Semantics_SimpleWhileFunc.