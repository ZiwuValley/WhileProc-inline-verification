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

Lemma inline_const_sem:
  forall fs n args, 
    list_state_unchanged fs args ->
    Sets.equiv
      (func_sem (eval_expr_func (EFConst n))
      (map (eval_expr_int fs) args))
      (const_sem n).
Proof.
  intros.
  unfold eval_expr_func.
  unfold func_sem.
  intros.
  split. revert a a0 a1. 
  + intros s1 res s2. intros.
    destruct H0 as [s3 H0]. destruct H0 as [args0 H0].
    destruct H0 as [? ?].
    apply bind_args_unchanged in H0.
    - rewrite <- H0 in H1.
      sets_unfold in H1.
      apply H1.
    - apply H.
  + intros.
    sets_unfold.
    exists a.
    induction args.
    - unfold map, ret.
      unfold bind_args, ret.
      exists nil.
      tauto.
    - unfold list_state_unchanged in H.
      destruct H as [? ?].
      change ((fix list_state_unchanged
            (fs : func_list) (args : list expr_int) {struct args} : Prop :=
            match args with
            | nil => True
            | e :: args' => state_unchanged fs e /\ list_state_unchanged fs args'
            end) fs args) with (list_state_unchanged fs args) in H1.
      specialize (IHargs H1).
      destruct IHargs as [? ?]; destruct H2 as (? & ?).
      Check map (eval_expr_int fs) (a2 :: args).
      Check bind_args (map (eval_expr_int fs) (a2 :: args)).

      unfold bind_args, map.
      fold bind_args.
      change (((fix map (l : list expr_int) :
          list expr_int_sem :=
        match l with
        | nil => nil
        | a3 :: t => eval_expr_int fs a3 :: map t
        end) args)) with (map (eval_expr_int fs) args) in H0.



Lemma inline_equivalence:
  forall fs f e args, 
    eq (fs f) (eval_expr_func e) ->
    Sets.equiv
    (eval_expr_int fs (translate_func_inline e args)) 
    (eval_expr_int fs (EFunc f args)).
Proof.
  intros.
  unfold eval_expr_int.
  fold eval_expr_int.
  rewrite H.
  induction e.
  + unfold translate_func_inline. eval_expr_func.
    change ((fun _ : list Z => const_sem n)
            (map (eval_expr_int fs) args))
            with (const_sem n).
  split.
  unfold translate_func_inline.







End Semantics_SimpleWhileFunc_Inline.