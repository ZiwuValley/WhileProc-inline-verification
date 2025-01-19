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

(* [Forward from README.md]

Semantics_Inline_func.v 中，我们假定函数全部不改变程序状态，只返回一个简单的表达式，

在此基础上定义了函数的“内联”操作，即将函数调用直接展开，并证明了在函数返回值为常数，

变量值，表达式等情况下，函数内联操作保持语义等价性

我们在内联函数的语法中添加了一个新的表达式类型，即EFArgs i，表示计算函数列表中第 i 个参数*)



(* 以下是对第二部分一段简单的说明：*)

(* 这部分中，除了“函数调用只返回一个简单的表达式，不改变程序状态”之外，我们还做了若干必要的假设：

1. "list_state_unchanged fs args" 表示函数参数列表的调用不改变程序状态，因为在题设中，对函数列表内
    出现的东西是没有任何限制的。举个例子，原函数为 f(g(), h()), 其中g()会改变程序状态，而h()使用了g()改变
    的那个全局变量，而f = g() + h()。

    这里需要用到的知识是，函数参数列表的求值顺序是undefined的，因此总存在一种求值顺序，使得h()先被算，而
    g()后被算。但是当我们在inline的时候，是固定先算g()，再算h()。这就导致了inline前和inline后语义不等价了！

2. "list_state_halt fs args" 表示函数参数列表的调用总是会终止，同样地，考虑 f(g(), h())，f = h()，
    如果g()不停机，那么在不inline时，f也不会停机。但是在inline的时候，f = h(), 因此只会调用 EFArgs 2, 
    即第二个参数，而不会调用第一个参数，因此f会停机。这就导致了inline前和inline后语义不等价了！

3. "list_result_unique fs args" 表示函数参数列表的调用总是会返回唯一的结果，这个假设是为了保证inline后的
    语义等价性。因为如果一个函数调用返回多个结果，那么inline后的语义就不唯一了。考虑f(x) = x + x，而g()是
    一个返回随机数的函数，g() ~ Ber(1/2)，那么f(g())有1/2的几率为0，1/2的几率为2，但是inline后g()+g()有
    1/4的概率是1，这就导致了inline前和inline后语义不等价了！

如果一个函数调用满足以上的假设，那么它是可以被inline的，我们定义的inline操作为类似宏替换的操作。

基于以上的假设，我们最终可以证明，对于一个函数调用，如果其内部只有常数，变量，+，-，*等
简单的语句，且没有函数调用，那么inline后的语义是等价的。 *)

(* 这一部分用于定义inline函数在取第i个参数时的语义 *)

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

(* 这里证明了args_sem能保持等价关系，即对于相同的参数列表，取相同的第i个值，返回值和结束状态是相同的 *)
#[export] Instance args_sem_congr:
  Proper (eq ==> eq ==> Sets.equiv) args_sem.
Proof.
  unfold Proper, respectful.
  intros.
  unfold args_sem.
  rewrite H. rewrite H0.
  reflexivity.
Qed.

(* 这里是inline函数中，get_args的定义，区别在于这里的args是expr_int类型的，而不是Z类型的 
   这个函数对应了用参数列表中的表达式去使用类似宏替换的方法替换EFArgs语句 *)
Fixpoint get_args_inline (args: list expr_int) (i: nat): expr_int :=
  match args with
  | nil => EConst 0
  | cons arg args' =>
    match i with
    | O => arg
    | S n => get_args_inline args' n
    end
  end.

(* 这里递归定义了一个关键的函数，即一个函数如果能被expr_func的语言表达，那么只要fs和args满足对应的条件，就可inline
   这个函数将expr_func和args翻译成一个expr_int，即对应了函数inline的过程 *)
Fixpoint translate_func_inline (e: expr_func) (args: list expr_int) : expr_int :=
  match e with
  | EFConst n => EConst n
  | EFVar X => EVar X
  | EFArgs i => get_args_inline args i
  | EFAdd e1 e2 => EAdd (translate_func_inline e1 args) (translate_func_inline e2 args)
  | EFSub e1 e2 => ESub (translate_func_inline e1 args) (translate_func_inline e2 args)
  | EFMul e1 e2 => EMul (translate_func_inline e1 args) (translate_func_inline e2 args)
  end.

(* 对于单个整数表达式，定义其具有“不改变状态”的条件，即前后状态一致 *)
Definition state_unchanged (fs: func_list) (e: expr_int): Prop :=
  forall s1 res s2, (s1, res, s2) ∈ (eval_expr_int fs e) -> s1 = s2.

(* 对于可以放在函数内的表达式，同理定义其具有“不改变状态”的条件 *)
Definition state_unchanged_func (args: list Z) (e: expr_func): Prop :=
  forall s1 res s2, (s1, res, s2) ∈ (eval_expr_func e args) -> s1 = s2.

(* 对于整个参数列表，递归定义其具有“不改变状态”的条件，即其中每个整数表达式都不改变状态 *)
Fixpoint list_state_unchanged (fs: func_list) (args: list expr_int): Prop :=
  match args with
  | nil => True
  | cons e args' => state_unchanged fs e /\ list_state_unchanged fs args'
  end.

(* 证明：计算参数列表的过程不改变程序状态 *)
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
    sets_unfold in H0. simpl in H0. 
    unfold append_arg in H0. destruct H0 as [s3 ?].
    destruct H0 as [Dargs0 ?]. destruct H0 as [arg ?].
    destruct H0 as (H2 & H3 & H4).
    specialize (IHargs s3 Dargs0 s2 H3).
    apply H in H4.
    rewrite H4, <- IHargs.
    reflexivity.
Qed.

(* 对于单个整数表达式，定义其具有“停机”条件，即对于任何输入状态，都能找到一个输出状态 *)
Definition state_halt (fs: func_list) (e: expr_int): Prop :=
  forall s1, exists res s2, (s1, res, s2) ∈ (eval_expr_int fs e).

(* 对于整个整数表达式列表，递归定义其具有“停机”条件，即其中每个整数表达式都停机 *)
Fixpoint list_state_halt (fs: func_list) (args: list expr_int): Prop :=
  match args with
  | nil => True
  | cons e args' => state_halt fs e /\ list_state_halt fs args'
  end.

(* 对于单个整数表达式，定义其具有“唯一性”条件，即对于任何输入状态，其返回值唯一 *)
Definition result_unique (fs: func_list) (e: expr_int): Prop :=
  forall s1 s2 s3 res1 res2, 
    (s1, res1, s2) ∈ (eval_expr_int fs e) ->
    (s1, res2, s3) ∈ (eval_expr_int fs e) -> 
    res1 = res2.

(* 对于整个整数表达式列表，递归定义其具有“唯一性”条件，即其中每个整数表达式都有唯一返回值 *)
Fixpoint list_result_unique (fs: func_list) (args: list expr_int): Prop :=
  match args with
  | nil => True
  | cons e args' => result_unique fs e /\ list_result_unique fs args'
  end.

(* 证明：计算参数列表的过程不改变程序状态，且总是停机 *)
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
    exists (arg :: Dargs). simpl in *.
    unfold append_arg.
    split.
    exists s1, Dargs, arg.
    tauto. tauto.
Qed.

(* 这里为了证明的简洁性，定义了某函数语句 e 和某语义 sem 在内联前后的语义等价性 *)
Definition inline_sem (args: list expr_int) (e: expr_func) (sem: expr_int_sem): Prop :=
  forall fs,
    list_state_unchanged fs args ->
    list_state_halt fs args ->
    Sets.equiv
      (func_sem (eval_expr_func e)
      (map (eval_expr_int fs) args))
      sem.

(* 这里证明了常数表达式的内联操作保持语义等价性 *)
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

(* 这里证明了变量表达式的内联操作保持语义等价性 *)
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

(* 首先，inline语义中bind_args的状态集非空，在此基础上，我们证明了存在某 list Z 为计算出来的参数列表
    便于我们后续证明中直接找到那个args0*)
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
    simpl in *.
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

(* 一个引理，同样是方便后续进行特化，直接找到对应的与元素arg和列表args1*)
Lemma args_unempty:
  forall fs args s1 args0 s2, 
    (s1, args0, s2) ∈ bind_args (map (eval_expr_int fs) args) ->
    ~ (args = nil) ->
    exists arg args1, args0 = arg :: args1.
Proof.
  intros.
  destruct args. tauto.
  simpl in *. unfold append_arg in H. sets_unfold in H.
  destruct H as [s3 H]. destruct H as [args1 H]. destruct H as [arg H].
  destruct H. exists arg, args1. symmetry. tauto.
Qed.

(* 证明能一个函数如果能被expr_func表达，那么对应的函数不改变程序状态 *)
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

(* 证明如果有参数列表的计算不改变程序状态，那么expr_func翻译出来的
   expr_int在对应fs和args下的求值也不改变程序状态 *)
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

(* 证明如果有参数列表的计算不改成程序状态且每个表达式本身结果唯一，那么同一状态算出的
   list Z是唯一的 *)
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
  
(* 证明如果参数列表不改变程序状态，必定停机且求值唯一，那么EFArgs语句在inline前后保持语义等价 *)
Lemma inline_args_sem:
  forall i fs args,
  list_state_unchanged fs args ->
  list_state_halt fs args ->
  list_result_unique fs args ->
  Sets.equiv
    (func_sem (eval_expr_func (EFArgs i))
    (map (eval_expr_int fs) args))
    (eval_expr_int fs
    (get_args_inline args i)).
Proof.
  intros. unfold eval_expr_func, func_sem. revert H1. intro H100.
  intros. split; revert a a0 a1; intros s1 res s2; intros.
  + destruct H1 as [s3 H1]. destruct H1 as [args0 H1].
    destruct H1 as [? ?].
    pose proof H1. apply bind_args_unchanged in H3. rewrite <- H3 in *. clear H3 s3.

    revert H1 H2. revert i. revert H H0 H100. revert args args0. revert s1 res s2.
    induction args; destruct i; simpl in *; intros; 
    unfold args_sem in H2; sets_unfold in H2. 
    - destruct args0; simpl in *; unfold const_sem. tauto.
      unfold ret in H1. sets_unfold in H1. 
      destruct H1 as [? _].
      discriminate H1.
    - unfold ret in H1. sets_unfold in H1.
      destruct H1 as [? _]. rewrite H1 in *. clear H1 args0.
      simpl in *. unfold const_sem. tauto.
    - destruct H. destruct H0.
      destruct args0. unfold append_arg in H1. 
      sets_unfold in H1. destruct H1 as [s3 H1]. destruct H1 as [args0 H1].
      destruct H1 as [arg H1]. destruct H1. discriminate H1.
      unfold get_args in H2. unfold append_arg in H1.
      sets_unfold in H1. destruct H1 as [s3 H1]. destruct H1 as [args1 H1].
      destruct H1 as [arg H1]. destruct H1 as (? & ? & ?).
      inversion H1.
      rewrite <- H8, H9 in *. clear H1 H8 H9 z args1.
      destruct H2. rewrite H1, <- H2 in *. clear H1 H2 res s2.
      pose proof H6. apply H in H1. rewrite <- H1 in *. clear H1 s3.
      tauto.
    - destruct H. destruct H0. destruct H100 as [H100 H101]. destruct H2.
      rewrite <- H5 in *. clear H5 s2.
      destruct args0; simpl in *. 
      unfold append_arg in H1. sets_unfold in H1.
      destruct H1 as [s3 H1]. destruct H1 as [args1 H1].
      destruct H1 as [arg H1]. destruct H1. discriminate H1.
      specialize (IHargs args0 H3 H4 H101 i). clear H4.
      unfold append_arg in H1. sets_unfold in H1.
      destruct H1 as [s3 H1]. destruct H1 as [args1 H1].
      destruct H1 as [arg H1]. destruct H1 as (? & ? & ?).
      inversion H1. rewrite <- H7, H8 in *. clear H1 H7 H8 z args1.
      pose proof H4. apply bind_args_unchanged in H1.
      rewrite H1 in *. clear H1 s3.
      specialize (IHargs H4).
      unfold args_sem in IHargs. sets_unfold in IHargs.
      assert (res = get_args args0 i /\ s1 = s1). tauto.
      specialize (IHargs H1). tauto. tauto. 
    - tauto.
  + revert H1. revert i s1 res s2.
    induction args; destruct i; intros.
    - simpl in *. 
      exists s1, nil. unfold ret. sets_unfold. 
      unfold args_sem. unfold const_sem in H1. unfold get_args. tauto.
    - simpl in *. 
      exists s1, nil. unfold ret. sets_unfold.
      unfold args_sem. unfold const_sem in H1. unfold get_args. tauto.
    - simpl in *. 
      destruct H, H0.
      pose proof H1. apply H in H4.
      rewrite <- H4 in *. clear H4 s2.
      unfold append_arg. sets_unfold.
      pose proof (inline_exists_args fs args s1 H2 H3).
      destruct H4 as [args0 H4].
      exists s1, (res :: args0). split.
      exists s1, args0, res. tauto.
      unfold args_sem, get_args. tauto.
    - pose proof (inline_exists_args fs (a :: args) s1 H H0).
      destruct H2 as [args0 H2].
      destruct H, H0. destruct H100 as [H100 H101].
      unfold append_arg. sets_unfold.
      specialize (IHargs H3 H4 H101).
      exists s1, args0.
      
      simpl in *. split. tauto.
      unfold append_arg in H2. sets_unfold in H2.
      destruct H2 as [s3 H2]. destruct H2 as [args1 H2]. destruct H2 as [arg H2].
      specialize (IHargs i s1 res s2 H1).
      destruct IHargs as [s4 IHargs]. destruct IHargs as [args2 IHargs].
      destruct IHargs. destruct H2 as (? & ? & ?).

      pose proof H5. apply bind_args_unchanged in H9. 
      rewrite <- H9 in *. clear H9 s4.
      pose proof H7. apply bind_args_unchanged in H9.
      rewrite H9 in *. clear H9 s3.
      pose proof (inline_state_unchanged_func args2 (EFArgs i)).
      unfold state_unchanged_func, eval_expr_func in H9.
      specialize (H9 s1 res s2 H6).
      rewrite <- H9 in *. clear H9 s2.

      pose proof (bind_args_unique fs args s1 s1 s1 args1 args2 H3 H101 H7 H5).
      rewrite <- H9 in *. clear H9 args2.
      rewrite <- H2 in *. clear H2 args0.
      unfold args_sem. split; simpl in *.
      apply H6. tauto. tauto. tauto.
Qed.

(* 定义二元操作在参数列表的假设与归纳假设成立时满足inline前后行为等价 *)
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

(* 证明EFAdd在参数列表的假设与归纳假设成立时满足inline前后行为等价 *)
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

(* 证明EFSub在参数列表的假设与归纳假设成立时满足inline前后行为等价 *)
Lemma inline_sub_sem: 
  inline_sem_2 EFSub.
Proof.
  unfold inline_sem_2. intros fs e1 e2 args H H0 H100 IHe1 IHe2.
  unfold func_sem. split; revert a a0 a1; intros s1 res s2; intros H1.

  + destruct H1 as [s3 H1]. destruct H1 as [args0 H1].
    destruct H1. unfold sub_sem in H2. sets_unfold in H2.
    destruct H2 as [res1 H2]. destruct H2 as [s4 H2]. 
    destruct H2.

    pose proof (bind_args_unchanged fs args H s1 args0 s3 H1) as H10.
    rewrite <- H10 in *. clear H10. clear s3.
    pose proof (inline_state_unchanged_func args0 e2).
    unfold state_unchanged_func in H4. specialize (H4 s4 (res1-res) s2 H3).
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

    specialize (IHe2 s1 (res1-res) s1).
    assert (exists s3 args0, 
      (s1, args0, s3) ∈ bind_args (map (eval_expr_int fs) args) /\
      eval_expr_func e2 args0 s3 (res1-res) s1).
      {exists s1. exists args0. 
      split. apply H1.
      tauto. }
    destruct IHe2 as [IHe2 _].
    specialize (IHe2 H4). clear H4.

    unfold sub_sem. exists res1, s1.
    tauto.

  + simpl in H1. simpl.
    symmetry in IHe1, IHe2.
    unfold sub_sem in H1. destruct H1 as [res1 H1]. destruct H1 as [s3 H1].
    destruct H1.

    unfold func_sem in IHe1. sets_unfold in IHe1.
    specialize (IHe1 s1 res1 s3). destruct IHe1 as [IHe1 _].
    specialize (IHe1 H1). destruct IHe1 as [s4 IHe1]. 
    destruct IHe1 as [args0 IHe1].
    destruct IHe1 as [H10 IHe1].
    pose proof H10 as H11.
    apply bind_args_unchanged in H10. rewrite <- H10 in *. clear H10 s4.

    unfold func_sem in IHe2. sets_unfold in IHe2.
    specialize (IHe2 s3 (res1-res) s2). destruct IHe2 as [IHe2 _].
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
    unfold sub_sem. sets_unfold.
    exists res1, s1. tauto.
    tauto. tauto. tauto. tauto.
Qed. 

(* 证明EFMul在参数列表的假设与归纳假设成立时满足inline前后行为等价 *)
Lemma inline_mul_sem: 
  inline_sem_2 EFMul.
Proof.
  unfold inline_sem_2. intros fs e1 e2 args H H0 H100 IHe1 IHe2.
  unfold func_sem. split; revert a a0 a1; intros s1 res s2; intros H1.

  + destruct H1 as [s3 H1]. destruct H1 as [args0 H1].
    destruct H1. unfold mul_sem in H2. sets_unfold in H2.
    destruct H2 as [res1 H2]. destruct H2 as [s4 H2]. destruct H2 as [b H2]. 
    destruct H2 as (H1000 & ? & ?).

    pose proof (bind_args_unchanged fs args H s1 args0 s3 H1) as H10.
    rewrite <- H10 in *. clear H10. clear s3.
    pose proof (inline_state_unchanged_func args0 e2).
    unfold state_unchanged_func in H4. specialize (H4 s4 b s2 H3).
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

    specialize (IHe2 s1 b s1).
    assert (exists s3 args0, 
      (s1, args0, s3) ∈ bind_args (map (eval_expr_int fs) args) /\
      eval_expr_func e2 args0 s3 b s1).
      {exists s1. exists args0. 
      split. apply H1.
      tauto. }
    destruct IHe2 as [IHe2 _].
    specialize (IHe2 H4). clear H4.

    unfold mul_sem. exists res1, s1, b.
    tauto.

  + simpl in H1. simpl.
    symmetry in IHe1, IHe2.
    unfold mul_sem in H1. destruct H1 as [res1 H1]. 
    destruct H1 as [s3 H1]. destruct H1 as [b H1].
    destruct H1 as (H1000 & ? & ?).

    unfold func_sem in IHe1. sets_unfold in IHe1.
    specialize (IHe1 s1 res1 s3). destruct IHe1 as [IHe1 _].
    specialize (IHe1 H1). destruct IHe1 as [s4 IHe1]. 
    destruct IHe1 as [args0 IHe1].
    destruct IHe1 as [H10 IHe1].
    pose proof H10 as H11.
    apply bind_args_unchanged in H10. rewrite <- H10 in *. clear H10 s4.

    unfold func_sem in IHe2. sets_unfold in IHe2.
    specialize (IHe2 s3 b s2). destruct IHe2 as [IHe2 _].
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
    unfold mul_sem. sets_unfold.
    exists res1, s1, b. tauto.
    tauto. tauto. tauto. tauto.
Qed.

(* 证明如果参数列表满足不改变程序状态，必定停机且求值唯一，那么inline前后的语句满足行为等价 *)
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
  unfold eval_expr_int; fold eval_expr_int.
  + apply inline_const_sem; tauto.
  + apply inline_var_sem; tauto.
  + apply inline_args_sem; tauto.
  + apply inline_add_sem; tauto.
  + apply inline_sub_sem; tauto.
  + apply inline_mul_sem; tauto.
Qed.

End Semantics_SimpleWhileFunc_Inline.