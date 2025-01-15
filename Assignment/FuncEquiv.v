Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Psatz.
Require Import Coq.Classes.Equivalence.
Require Import Coq.Classes.Morphisms.
Require Import SetsClass.SetsClass. Import SetsNotation.
Local Open Scope string.
Local Open Scope Z.
Local Open Scope sets.

Definition pointwise_relation
             (A: Type) {B: Type}
             (R: B -> B -> Prop)
             (f g: A -> B): Prop :=
  forall a: A, R (f a) (g a).

#[export] Instance pointwise_reflexive:
  forall {A B: Type} {R: B -> B -> Prop},
    Reflexive R ->
    Reflexive (pointwise_relation A R).
Proof.
  intros.
  unfold Reflexive, pointwise_relation.
  (** 展开定义后需要证明
      - _[forall (x: A -> B) a, R (x a) (x a)]_。*)
  intros.
  reflexivity.
  (** 这一步是使用二元关系_[R]_的自反性完成证明。*)
Qed.

#[export] Instance pointwise_symmetric:
  forall {A B: Type} {R: B -> B -> Prop},
    Symmetric R ->
    Symmetric (pointwise_relation A R).
Proof.
  intros.
  unfold Symmetric, pointwise_relation.
  intros.
  (** 展开定义后需要证明的前提和结论是：
      - H0: forall a, R (x a) (y a)
      - 结论: R (y a) (x a) *)
  symmetry.
  (** 这里的_[symmetry]_指令表示使用对称性。*)
  apply H0.
Qed.

#[export] Instance pointwise_transitive:
  forall {A B: Type} {R: B -> B -> Prop},
    Transitive R ->
    Transitive (pointwise_relation A R).
Proof.
  intros.
  unfold Transitive, pointwise_relation.
  intros.
  (** 展开定义后需要证明的前提和结论是：
      - H0: forall a, R (x a) (y a)
      - H1: forall a, R (y a) (z a)
      - 结论: R (x a) (z a) *)
  transitivity (y a).
  (** 这里，_[transitivity (y a)]_表示用“传递性”证明并选_[y a]_作为中间元素。*)
  + apply H0.
  + apply H1.
Qed.

#[export] Instance pointwise_equivalence:
  forall {A B: Type} {R: B -> B -> Prop},
    Equivalence R ->
    Equivalence (pointwise_relation A R).
Proof.
  intros.
  split.
  + apply pointwise_reflexive.
    apply Equivalence_Reflexive.
  + apply pointwise_symmetric.
    apply Equivalence_Symmetric.
  + apply pointwise_transitive.
    apply Equivalence_Transitive.
Qed.

Definition func_equiv (A B: Type):
  (A -> B) -> (A -> B) -> Prop :=
  pointwise_relation A (@eq B).

#[export] Instance func_equiv_equiv:
  forall A B, Equivalence (func_equiv A B).
Proof.
  intros.
  apply pointwise_equivalence.
  apply eq_equivalence.
Qed.

(* Fixpoint list_relation 
  {A : Type}
  (R: A -> A -> Prop)
  (l1 l2: list A): Prop :=
  match l1 with 
  | nil => 
    match l2 with
    | nil => True
    | cons b l2' => False
    end
  | cons a l1' =>
    match l2 with
    | nil => False
    | cons b l2' => (R a b) /\ (list_relation R l1' l2')
    end
  end.

#[export] Instance list_reflexive:
  forall {A: Type} {R: A -> A -> Prop},
  Reflexive R ->
  Reflexive (list_relation R).
Proof.
  unfold Reflexive.
  intros.
  unfold list_relation.
  induction x.
  + tauto.
  + pose proof H a. split.
    - tauto.
    - tauto.
Qed.

#[export] Instance list_symmetric:
  forall {A: Type} {R: A -> A -> Prop},
  Symmetric R ->
  Symmetric (list_relation R).
Proof.
  unfold Symmetric, list_relation.
  intros. revert H0. revert y.
  induction x.
  + intros. destruct y.
    - tauto. - tauto.
  + intros. destruct y.
    - tauto.
    - destruct H0 as [H1 H2].
      split.
      ++ pose proof H a a0 H1. tauto.
      ++ pose proof IHx y H2. tauto.
Qed.

Fixpoint list_set_equiv (A : Type):
  (list (A -> Prop)) -> (list (A -> Prop)) -> Prop := 
   *)