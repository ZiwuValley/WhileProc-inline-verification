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
Require Import Assignment.Semantics.
Local Open Scope string.
Local Open Scope Z.
Local Open Scope sets.

Module Semantics_SimpleWhileFunc_Inline.
Import StateRelMonad.
Import Lang_SimpleWhileFunc.
Import Semantics_SimpleWhileFunc.

Fixpoint get_args (args: list Z) (i: Z): Z :=
  match args with
  | nil => 0
  | cons arg args' =>
    match i with
    | Z0 => arg
    | _ => get_args args' (i-1)
    end
  end.

Definition args_sem (args: list Z) (i: Z): expr_int_sem :=
  fun (s1: state) (res: Z) (s2: state) =>
  res = get_args args i /\ s1 = s2.

Fixpoint eval_expr_func (e: expr_func) (args: list Z) : expr_int_sem :=
  match e with
  | EFConst n => const_sem n
  | EFVar X => var_sem X
  | EFArgs i => args_sem args i
  | EFAdd e1 e2 => add_sem (eval_expr_func e1 args) (eval_expr_func e2 args)
  | EFSub e1 e2 => sub_sem (eval_expr_func e1 args) (eval_expr_func e2 args)
  | EFMul e1 e2 => mul_sem (eval_expr_func e1 args) (eval_expr_func e2 args)
  end.

#[export] Instance args_sem_congr:
  Proper (eq ==> eq ==> Sets.equiv) args_sem.
Proof.
  unfold Proper, respectful.
  intros.
  unfold args_sem.
  rewrite H. rewrite H0.
  reflexivity.
Qed.

Fixpoint get_args_inline (args: list expr_int) (i: Z): expr_int :=
  match args with
  | nil => EConst 0
  | cons arg args' =>
    match i with
    | Z0 => arg
    | _ => get_args_inline args' (i-1)
    end
  end.

Fixpoint translate_func_inline (e: expr_func) (args: list expr_int) : expr_int :=
  match e with
  | EFConst n => EConst n
  | EFVar X => EVar X
  | EFArgs i => get_args_inline args i
  | EFAdd e1 e2 => EAdd (translate_func_inline e1 args) (translate_func_inline e2 args)
  | EFSub e1 e2 => ESub (translate_func_inline e1 args) (translate_func_inline e2 args)
  | EFMul e1 e2 => EMul (translate_func_inline e1 args) (translate_func_inline e2 args)
  end.

Definition state_unchanged (fs: func_list) (e: expr_int): Prop :=
  forall s1 res s2, (s1, res, s2) ∈ (eval_expr_int fs e) -> s1 = s2.

Fixpoint list_state_unchanged (fs: func_list) (args: list expr_int): Prop :=
  match args with
  | nil => True
  | cons e args' => state_unchanged fs e /\ list_state_unchanged fs args'
  end.

Lemma bind_args_unchanged:
  forall fs args, (list_state_unchanged fs args ->
    (forall s1 Dargs s2,
      ((s1, Dargs, s2) ∈ bind_args (map (eval_expr_int fs) args) ->
        s1 = s2))).
Proof.
  intros.
  revert H0. revert s1 Dargs s2.
  induction args.
  + intros. unfold map, bind_args, ret in H0.
    sets_unfold in H0. tauto.
  + intros.
    unfold list_state_unchanged in H. destruct H as [? ?].
    fold list_state_unchanged in H1. specialize (IHargs H1).
    sets_unfold in H0. unfold bind_args, map in H0.
    fold bind_args in H0.
    change (((fix map (l : list expr_int) :
          list expr_int_sem :=
        match l with
        | nil => nil
        | a :: t => eval_expr_int fs a :: map t
        end) args)) with (map (eval_expr_int fs) args) in H0.
    unfold append_arg in H0. destruct H0 as [s3 ?].
    destruct H0 as [Dargs0 ?]. destruct H0 as [arg ?].
    destruct H0 as (H2 & H3 & H4).
    specialize (IHargs s3 Dargs0 s2 H3).
    apply H in H4.
    rewrite H4, <- IHargs.
    reflexivity.
Qed.

Definition state_halt (fs: func_list) (e: expr_int): Prop :=
  forall s1, exists res s2, (s1, res, s2) ∈ (eval_expr_int fs e).

Fixpoint list_state_halt (fs: func_list) (args: list expr_int): Prop :=
  match args with
  | nil => True
  | cons e args' => state_halt fs e /\ list_state_halt fs args'
  end.

Lemma bind_args_unchanged_halt:
  forall fs args s1 (p: Prop),
    (list_state_unchanged fs args) ->
    (list_state_halt fs args) ->
    p ->
    (exists args0, (bind_args (map (eval_expr_int fs) args) s1 args0 s1) /\ p).
Proof.
  intros.
  induction args.
  + unfold map, bind_args, ret.
    exists nil. tauto.
  + destruct H as [? ?]. destruct H0 as [? ?].
    specialize (IHargs H2 H3). destruct IHargs as [Dargs ?].
    destruct H4 as (? & ?). clear H5.
    unfold state_halt in H0.
    specialize (H0 s1). destruct H0 as [arg H0]. destruct H0 as [s3 H0].
    pose proof H0. apply H in H0.
    rewrite <- H0 in H5.
    exists (arg :: Dargs).
    unfold bind_args, map. fold bind_args.
    change (((fix map (l : list expr_int) :
        list expr_int_sem :=
      match l with
      | nil => nil
      | a :: t => eval_expr_int fs a :: map t
      end) args)) with (map (eval_expr_int fs) args).
    unfold append_arg.
    split.
    exists s1, Dargs, arg.
    tauto. tauto.
Qed.

Definition inline_sem (args: list expr_int) (e: expr_func) (sem: expr_int_sem): Prop :=
  forall fs,
    list_state_unchanged fs args ->
    list_state_halt fs args ->
    Sets.equiv
      (func_sem (eval_expr_func e)
      (map (eval_expr_int fs) args))
      sem.

Lemma inline_const_sem:
  forall args n, inline_sem args (EFConst n) (const_sem n).
Proof.
  unfold inline_sem.
  intros. unfold eval_expr_func, func_sem.
  intros. split; revert a a0 a1; intros s1 res s2; intros.
  + destruct H1 as [s3 H1]. destruct H1 as [args0 H1].
    destruct H1 as [? ?].
    apply bind_args_unchanged in H1.
    - rewrite <- H1 in H2.
      sets_unfold in H2.
      apply H2.
    - apply H.
  + sets_unfold. exists s1.
    apply bind_args_unchanged_halt; tauto.
Qed.

Lemma inline_var_sem:
  forall args x, inline_sem args (EFVar x) (var_sem x).
Proof.
  unfold inline_sem.
  intros. unfold eval_expr_func, func_sem.
  intros. split; revert a a0 a1; intros s1 res s2; intros.
  + destruct H1 as [s3 H1]. destruct H1 as [args0 H1].
    destruct H1 as [? ?].
    apply bind_args_unchanged in H1.
    - rewrite <- H1 in H2.
      sets_unfold in H2.
      apply H2.
    - apply H.
<<<<<<< HEAD
  + sets_unfold. exists s1.
    apply bind_args_unchanged_halt; tauto. 
=======
    + sets_unfold. exists s1.
    apply bind_args_unchanged_halt; tauto.
>>>>>>> 071e46bb0fd639586623380bc8bc3c3879cc5cf1
Qed.

Lemma inline_args_sem:
  forall i fs args,
  list_state_unchanged fs args ->
  list_state_halt fs args ->
  Sets.equiv
    (func_sem (eval_expr_func (EFArgs i))
    (map (eval_expr_int fs) args))
    (eval_expr_int fs
    (get_args_inline args i)).
Proof.
  intros. unfold eval_expr_func, func_sem.
  intros. split; revert a a0 a1; intros s1 res s2; intros.
  + destruct H1 as [s3 H1]. destruct H1 as [args0 H1].
    destruct H1 as [? ?].
    pose proof H1 as H10.
    apply bind_args_unchanged in H1.
    - rewrite <- H1 in H2. rewrite <- H1 in H10. clear H1.
      sets_unfold in H2.
      unfold args_sem in H2.
      induction args.
      * unfold get_args_inline, eval_expr_int.
        unfold map, bind_args, ret in H10.
        sets_unfold in H10. destruct H10 as [? _].
        destruct H2 as [? ?]. rewrite <- H3. clear H3.
        rewrite H1 in H2. clear H1.
        unfold get_args in H2. unfold const_sem.
        tauto.
      * unfold get_args_inline.
      unfold get_args_inline.
<<<<<<< HEAD
Admitted.
  
Lemma inline_add_sem:
  forall fs e1 e2 args,
  list_state_unchanged fs args ->
  list_state_halt fs args ->
  state_unchanged fs (translate_func_inline e1 args) ->
  state_unchanged fs (translate_func_inline e2 args) ->
  state_halt fs (translate_func_inline e1 args) ->
  state_halt fs (translate_func_inline e2 args) ->
  Sets.equiv
    (func_sem (eval_expr_func (EFAdd e1 e2))
    (map (eval_expr_int fs) args))
    (add_sem (eval_expr_int fs (translate_func_inline e1 args))
    (eval_expr_int fs (translate_func_inline e2 args))).
Proof.
  intros. unfold eval_expr_func, func_sem.
  intros. split.
  + fold eval_expr_func. 
    intros.
    destruct H5 as [s3 H5]. destruct H5 as [args0 H5].
    destruct H5 as [? ?].
    pose proof H5 as H7.
    apply bind_args_unchanged in H5.
    rewrite <- H5 in H7; rewrite <- H5 in H6. 
    clear H5.
    - sets_unfold in H6.
      unfold add_sem in H6.
      destruct H6 as [res H6]. destruct H6 as [s5 H6].
      destruct H6 as [? H6].
      unfold add_sem.
      exists res, s5.
      split.
      * 
Admitted.


=======
      apply H2.
    - apply H.
>>>>>>> 071e46bb0fd639586623380bc8bc3c3879cc5cf1


Lemma inline_equivalence:
  forall fs f e args,
    list_state_unchanged fs args ->
    list_state_halt fs args ->
    eq (fs f) (eval_expr_func e) ->
    Sets.equiv
    (eval_expr_int fs (EFunc f args))
    (eval_expr_int fs (translate_func_inline e args)).
Proof.
  intros.
  unfold eval_expr_int.
  fold eval_expr_int.
  induction e; unfold translate_func_inline, eval_expr_func;
  rewrite H1; unfold eval_expr_int; fold eval_expr_int.
  + apply inline_const_sem; tauto.
  + apply inline_var_sem; tauto.
<<<<<<< HEAD
  + apply inline_args_sem; tauto.
  + fold translate_func_inline.
    apply inline_add_sem.
    - tauto.
    - tauto.
    - 
  
=======
  + unfold get_args_inline.

>>>>>>> 071e46bb0fd639586623380bc8bc3c3879cc5cf1
  apply inline_args_sem; tauto.
  split.
  unfold translate_func_inline.







End Semantics_SimpleWhileFunc_Inline.