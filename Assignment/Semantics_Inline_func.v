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

Fixpoint test_nat (i: nat): nat :=
    match i with
    | O => 0
    | S n => S (test_nat n)
    end.

Fixpoint get_args (args: list Z) (i: nat): Z :=
  match args with
  | nil => 0
  | cons arg args' =>
    match i with
    | O => arg
    | S n => get_args args' n
    end
  end.

Definition args_sem (args: list Z) (i: nat): expr_int_sem :=
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

Fixpoint get_args_inline (args: list expr_int) (i: nat): expr_int :=
  match args with
  | nil => EConst 0
  | cons arg args' =>
    match i with
    | O => arg
    | S n => get_args_inline args' n
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

Definition state_unchanged_func (args: list Z) (e: expr_func): Prop :=
  forall s1 res s2, (s1, res, s2) ∈ (eval_expr_func e args) -> s1 = s2.

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

Definition result_unique (fs: func_list) (e: expr_int): Prop :=
  forall s1 s2 s3 res1 res2, 
    (s1, res1, s2) ∈ (eval_expr_int fs e) ->
    (s1, res2, s3) ∈ (eval_expr_int fs e) -> 
    res1 = res2.

Fixpoint list_result_unique (fs: func_list) (args: list expr_int): Prop :=
  match args with
  | nil => True
  | cons e args' => result_unique fs e /\ list_result_unique fs args'
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
  + sets_unfold. exists s1.
    apply bind_args_unchanged_halt; tauto. 
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
Admitted.

Lemma inline_exists_args:
  forall fs args s1,
    list_state_unchanged fs args ->
    list_state_halt fs args ->
    exists args0,
      (s1, args0, s1) ∈ bind_args (map (eval_expr_int fs) args).
Proof.
  intros.
  induction args.
  + unfold map, bind_args, ret.
    exists nil. sets_unfold. tauto.
  + destruct H as [? ?]. destruct H0 as [? ?]. 
    specialize (IHargs H1 H2).
    destruct IHargs as [Dargs ?].
    unfold bind_args, map.
    change (((fix map (l : list expr_int) :
        list expr_int_sem :=
      match l with
      | nil => nil
      | a :: t => eval_expr_int fs a :: map t
      end) args)) with (map (eval_expr_int fs) args).
      fold bind_args.
    unfold append_arg.
    assert (forall (s4: state), exists res s5, (s4, res, s5) ∈ eval_expr_int fs a).
    intros. apply H0.
    specialize (H4 s1). destruct H4 as [res H4]. destruct H4 as [s2 H4].
    pose proof H4. apply H in H4.
    rewrite <- H4 in H5.
    exists (res :: Dargs).
    sets_unfold.
    exists s1, Dargs, res.
    split. tauto. split. tauto. tauto.
Qed.
    
(* Lemma inline_state_unchanged_func:
  forall fs e args,
    list_state_unchanged fs args ->
    list_state_halt fs args ->
    exists args0, state_unchanged_func args0 e.
Proof.
  intros. unfold state_unchanged_func.
  pose proof (inline_exists_args fs args).
  specialize (H1 (fun v => 0) H H0). destruct H1 as [args0 H1].
  clear H1.
  exists args0. intros.
  revert H1. revert s1 res s2.
  induction e; intros s1 res s2; intros.
  + unfold eval_expr_func, const_sem in H1.
    sets_unfold in H1. tauto.
  + unfold eval_expr_func, var_sem in H1.
    sets_unfold in H1. tauto.
  + unfold eval_expr_func, args_sem in H1.
    sets_unfold in H1. tauto.
  + unfold eval_expr_func in H1. fold eval_expr_func in H1.
    unfold add_sem in H1. sets_unfold in H1.
    destruct H1 as [res1 H1]. destruct H1 as [s3 H1].
    destruct H1 as [? ?].
    specialize (IHe1 s1 res1 s3 H1).
    specialize (IHe2 s3 (res-res1) s2 H2).
    rewrite IHe1. rewrite <- IHe2.
    tauto.
  + unfold eval_expr_func in H1. fold eval_expr_func in H1.
    unfold sub_sem in H1. sets_unfold in H1.
    destruct H1 as [res1 H1]. destruct H1 as [s3 H1].
    destruct H1 as [? ?].
    specialize (IHe1 s1 res1 s3 H1).
    specialize (IHe2 s3 (res1-res) s2 H2).
    rewrite IHe1. rewrite <- IHe2.
    tauto.
  + unfold eval_expr_func in H1. fold eval_expr_func in H1.
    unfold mul_sem in H1. sets_unfold in H1.
    destruct H1 as [res1 H1]. destruct H1 as [s3 H1].
    destruct H1 as [b H1]. destruct H1 as (? & ? & ?).
    specialize (IHe1 s1 res1 s3 H2).
    specialize (IHe2 s3 b s2 H3).
    rewrite IHe1. rewrite <- IHe2.
    tauto.
Qed. *)

Lemma inline_state_unchanged_func:
  forall args0 e, state_unchanged_func args0 e.
Proof.
  intros. unfold state_unchanged_func.
  intros s1 res s2 H1.
  revert H1. revert s1 res s2.
  induction e; intros s1 res s2; intros.
  + unfold eval_expr_func, const_sem in H1.
    sets_unfold in H1. tauto.
  + unfold eval_expr_func, var_sem in H1.
    sets_unfold in H1. tauto.
  + unfold eval_expr_func, args_sem in H1.
    sets_unfold in H1. tauto.
  + unfold eval_expr_func in H1. fold eval_expr_func in H1.
    unfold add_sem in H1. sets_unfold in H1.
    destruct H1 as [res1 H1]. destruct H1 as [s3 H1].
    destruct H1 as [H1 H2].
    specialize (IHe1 s1 res1 s3 H1).
    specialize (IHe2 s3 (res-res1) s2 H2).
    rewrite IHe1. rewrite <- IHe2.
    tauto.
  + unfold eval_expr_func in H1. fold eval_expr_func in H1.
    unfold sub_sem in H1. sets_unfold in H1.
    destruct H1 as [res1 H1]. destruct H1 as [s3 H1].
    destruct H1 as [H1 H2].
    specialize (IHe1 s1 res1 s3 H1).
    specialize (IHe2 s3 (res1-res) s2 H2).
    rewrite IHe1. rewrite <- IHe2.
    tauto.
  + unfold eval_expr_func in H1. fold eval_expr_func in H1.
    unfold mul_sem in H1. sets_unfold in H1.
    destruct H1 as [res1 H1]. destruct H1 as [s3 H1].
    destruct H1 as [b H1]. destruct H1 as (? & ? & ?).
    specialize (IHe1 s1 res1 s3 H0).
    specialize (IHe2 s3 b s2 H1).
    rewrite IHe1. rewrite <- IHe2.
    tauto.
Qed.

Lemma inline_state_unchanged_int:
  forall fs args e s1 res s2, 
    list_state_unchanged fs args ->
    (s1, res, s2) ∈ eval_expr_int fs (translate_func_inline e args) ->
    s1 = s2.
Proof.
  intros.
  revert H0. revert s1 res s2.
  induction e; intros; simpl in *.
  + unfold const_sem in H0.
    sets_unfold in H0. tauto.
  + unfold var_sem in H0.
    sets_unfold in H0. tauto.
  + unfold args_sem in H0.
    sets_unfold in H0.
    revert H0. revert i.
    induction args; induction i; intros; simpl in *.  
    - unfold const_sem in H0. tauto.
    - unfold const_sem in H0. tauto.
    - destruct H. specialize (IHargs H1). clear H1.
      apply H in H0. tauto.
    - destruct H. specialize (IHargs H1 i H0). tauto.
  + unfold add_sem in H0.
    sets_unfold in H0.
    destruct H0 as [res1 H0]. destruct H0 as [s3 H0].
    destruct H0.
    apply IHe1 in H0. apply IHe2 in H1. 
    rewrite H0, H1. tauto.
  + unfold sub_sem in H0.
    sets_unfold in H0.
    destruct H0 as [res1 H0]. destruct H0 as [s3 H0].
    destruct H0.
    apply IHe1 in H0. apply IHe2 in H1. 
    rewrite H0, H1. tauto.
  + unfold mul_sem in H0.
    sets_unfold in H0.
    destruct H0 as [res1 H0]. destruct H0 as [s3 H0].
    destruct H0 as [b H0]. destruct H0 as (? & ? & ?).
    apply IHe1 in H1. apply IHe2 in H2. 
    rewrite H1, H2. tauto.
Qed.

(* Lemma eval_expr_int_unique:
  forall fs e s1 s2 s3 arg0 arg1,
    (s1, arg0, s2) ∈ eval_expr_int fs e ->
    (s1, arg1, s3) ∈ eval_expr_int fs e ->
    arg0 = arg1 /\ s2 = s3.
Proof.
  intros.
  revert H H0. revert arg0 arg1 s1 s2 s3.
  induction e; intros; simpl in *. 
  + unfold const_sem in *.
    sets_unfold in H. sets_unfold in H0.
    destruct H as [? ?]. destruct H0 as [? ?].
    rewrite H, H0, <- H1, <- H2. tauto.
  + unfold const_sem in *.
    sets_unfold in H. sets_unfold in H0.
    destruct H as [? ?]. destruct H0 as [? ?].
    rewrite H, H0, <- H1, <- H2. tauto.
  + unfold add_sem in *.
    sets_unfold in H. sets_unfold in H0.
    destruct H as [res1 H]. destruct H as [s4 H]. destruct H as [? ?].
    destruct H0 as [res2 H0]. destruct H0 as [s5 H0]. destruct H0 as [? ?].
    pose proof (IHe1 res1 res2 s1 s4 s5 H H0).
    destruct H3 as [? ?]. rewrite <- H3, <- H4 in *. clear H3 H4 res2 s5.
    pose proof (IHe2 (arg0-res1) (arg1-res1) s4 s2 s3 H1 H2).
    destruct H3 as [? ?]. assert (arg0 = arg1). lia. clear H3.
    tauto.
  + unfold sub_sem in *.
    sets_unfold in H. sets_unfold in H0.
    destruct H as [res1 H]. destruct H as [s4 H]. destruct H as [? ?].
    destruct H0 as [res2 H0]. destruct H0 as [s5 H0]. destruct H0 as [? ?].
    pose proof (IHe1 res1 res2 s1 s4 s5 H H0).
    destruct H3 as [? ?]. rewrite <- H3, <- H4 in *. clear H3 H4 res2 s5.
    pose proof (IHe2 (res1-arg0) (res1-arg1) s4 s2 s3 H1 H2).
    destruct H3 as [? ?]. assert (arg0 = arg1). lia. clear H3.
    tauto.
  + unfold mul_sem in *.
    sets_unfold in H. sets_unfold in H0.
    destruct H as [res1 H]. destruct H as [s4 H]. 
    destruct H as [b1 H]. destruct H as (? & ? & ?).
    destruct H0 as [res2 H0]. destruct H0 as [s5 H0]. 
    destruct H0 as [b2 H0]. destruct H0 as (? & ? & ?).
    pose proof (IHe1 res1 res2 s1 s4 s5 H1 H3).
    destruct H5 as [? ?]. rewrite <- H5, <- H6 in *. clear H5 H6 res2 s5.
    pose proof (IHe2 b1 b2 s4 s2 s3 H2 H4).
    destruct H5 as [? ?]. rewrite <- H5, <- H6 in *. clear H5.
    rewrite <- H, <- H0. tauto.
  + unfold func_sem in *.
    sets_unfold in H. sets_unfold in H0.
    destruct H as [res1 H]. destruct H as [s4 H]. destruct H as [? ?].
    destruct H0 as [res2 H0]. destruct H0 as [s5 H0]. destruct H0 as [? ?]. *)


Lemma bind_args_unique:
  forall fs args s1 s2 s3 args0 args1, 
    list_state_unchanged fs args ->
    list_result_unique fs args ->
    (s1, args0, s2) ∈ bind_args (map (eval_expr_int fs) args) ->
    (s1, args1, s3) ∈ bind_args (map (eval_expr_int fs) args) ->
    args0 = args1.
Proof.
  intros.
  revert H1 H2. revert args0 args1.
  induction args; intros.
  + simpl in H1. unfold ret in H1. sets_unfold in H1. destruct H1 as [? _].
    simpl in H2. unfold ret in H2. sets_unfold in H2. destruct H2 as [? _].
    rewrite H1, H2. tauto.
  + simpl in *. unfold append_arg in H1, H2. 
    sets_unfold in H1. sets_unfold in H2.
    destruct H1 as [s4 H1]. destruct H1 as [args2 H1]. destruct H1 as [arg0 H1].
    destruct H2 as [s5 H2]. destruct H2 as [args3 H2]. destruct H2 as [arg1 H2].
    
    destruct H as [? ?]. destruct H0 as [? ?].
    destruct H1 as (? & ? & ?). destruct H2 as (? & ? & ?).
    rewrite <- H1, <- H2 in *. simpl in *. clear H1 H2 args0 args1.
    specialize (IHargs H3 H4 args2 args3).
    
    pose proof H5. 
    apply bind_args_unchanged in H1. rewrite H1 in *. clear H1 s4.
    pose proof H7.
    apply bind_args_unchanged in H1. rewrite H1 in *. clear H1 s5.

    unfold state_unchanged in H.
    pose proof (H s1 arg0 s2 H6). rewrite <- H1 in *. clear H1 s2.
    pose proof (H s1 arg1 s3 H8). rewrite <- H1 in *. clear H1 s3.
    unfold result_unique in H0.
    specialize (H0 s1 s1 s1 arg0 arg1 H6 H8). rewrite <- H0 in *. clear H0 arg1.
    specialize (IHargs H5 H7). rewrite IHargs in *. tauto. tauto. tauto.
Qed.

Definition inline_sem_2 (Binop: expr_func -> expr_func -> expr_func): Prop :=
  forall fs e1 e2 args,
    list_state_unchanged fs args ->
    list_state_halt fs args ->
    list_result_unique fs args ->
    func_sem (eval_expr_func e1)
      (map (eval_expr_int fs) args) ==
    eval_expr_int fs (translate_func_inline e1 args) ->
    func_sem (eval_expr_func e2)
      (map (eval_expr_int fs) args) ==
    eval_expr_int fs (translate_func_inline e2 args) ->
    func_sem (eval_expr_func (Binop e1 e2))
      (map (eval_expr_int fs) args) ==
    eval_expr_int fs
      (translate_func_inline (Binop e1 e2) args).

Lemma inline_add_sem: 
  inline_sem_2 EFAdd.
Proof.
  unfold inline_sem_2. intros fs e1 e2 args H H0 H100 IHe1 IHe2.
  unfold func_sem. split; revert a a0 a1; intros s1 res s2; intros H1.

  + destruct H1 as [s3 H1]. destruct H1 as [args0 H1].
    destruct H1. unfold add_sem in H2. sets_unfold in H2.
    destruct H2 as [res1 H2]. destruct H2 as [s4 H2]. 
    destruct H2.

    pose proof (bind_args_unchanged fs args H s1 args0 s3 H1) as H10.
    rewrite <- H10 in *. clear H10. clear s3.
    pose proof (inline_state_unchanged_func args0 e2).
    unfold state_unchanged_func in H4. specialize (H4 s4 (res-res1) s2 H3).
    rewrite H4 in *. clear H4. clear s4.
    pose proof (inline_state_unchanged_func args0 e1).
    unfold state_unchanged_func in H4. specialize (H4 s1 res1 s2 H2).
    rewrite <- H4 in *. clear H4. clear s2.

    unfold func_sem in IHe1. sets_unfold in IHe1. 

    specialize (IHe1 s1 res1 s1).
    assert (exists s3 args0, 
      (s1, args0, s3) ∈ bind_args (map (eval_expr_int fs) args) /\
      eval_expr_func e1 args0 s3 res1 s1).
      {exists s1. exists args0. 
      split. apply H1.
      tauto. }
    destruct IHe1 as [IHe1 _].
    specialize (IHe1 H4). clear H4.

    specialize (IHe2 s1 (res-res1) s1).
    assert (exists s3 args0, 
      (s1, args0, s3) ∈ bind_args (map (eval_expr_int fs) args) /\
      eval_expr_func e2 args0 s3 (res-res1) s1).
      {exists s1. exists args0. 
      split. apply H1.
      tauto. }
    destruct IHe2 as [IHe2 _].
    specialize (IHe2 H4). clear H4.

    unfold add_sem. exists res1, s1.
    tauto.

  + simpl in H1. simpl.
    symmetry in IHe1, IHe2.
    unfold add_sem in H1. destruct H1 as [res1 H1]. destruct H1 as [s3 H1].
    destruct H1.

    unfold func_sem in IHe1. sets_unfold in IHe1.
    specialize (IHe1 s1 res1 s3). destruct IHe1 as [IHe1 _].
    specialize (IHe1 H1). destruct IHe1 as [s4 IHe1]. 
    destruct IHe1 as [args0 IHe1].
    destruct IHe1 as [H10 IHe1].
    pose proof H10 as H11.
    apply bind_args_unchanged in H10. rewrite <- H10 in *. clear H10 s4.

    unfold func_sem in IHe2. sets_unfold in IHe2.
    specialize (IHe2 s3 (res-res1) s2). destruct IHe2 as [IHe2 _].
    specialize (IHe2 H2). destruct IHe2 as [s4 IHe2]. 
    destruct IHe2 as [args1 IHe2].
    destruct IHe2 as [H10 IHe2].
    pose proof H10 as H12.
    apply bind_args_unchanged in H10. rewrite <- H10 in *. clear H10 s4.
    
    pose proof H1. apply inline_state_unchanged_int in H3. 
    rewrite <- H3 in *. clear H3.
    pose proof H2. apply inline_state_unchanged_int in H3. 
    rewrite <- H3 in *. clear H3.

    pose proof (bind_args_unique fs args s1 s1 s1 args0 args1 H H100 H11 H12).
    rewrite <- H3 in *. clear H3.

    exists s1, args0. split. tauto.
    unfold add_sem. sets_unfold.
    exists res1, s1. tauto.
    tauto. tauto. tauto. tauto.
Qed.
    
    

    

Lemma inline_equivalence:
  forall fs f e args,
    list_state_unchanged fs args ->
    list_state_halt fs args ->
    list_result_unique fs args ->
    eq (fs f) (eval_expr_func e) ->
    Sets.equiv
    (eval_expr_int fs (EFunc f args))
    (eval_expr_int fs (translate_func_inline e args)).
Proof.
  intros.
  unfold eval_expr_int.
  fold eval_expr_int.
  rewrite H2. clear H2.
  induction e; intros;
  (*unfold translate_func_inline, eval_expr_func;*)
  unfold eval_expr_int; fold eval_expr_int.
  + apply inline_const_sem; tauto.
  + apply inline_var_sem; tauto.
  + apply inline_args_sem; tauto.
  + apply inline_add_sem; tauto.
  + apply inline_sub_sem; tauto.
    
    
         


  
  apply inline_args_sem; tauto.
  split.
  unfold translate_func_inline.







End Semantics_SimpleWhileFunc_Inline.