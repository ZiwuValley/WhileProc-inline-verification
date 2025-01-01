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
Definition func_name: Type := string.
Definition args: Type := list Z.

Definition state: Type := var_name -> Z.
Definition func_state: Type := (func_name -> args -> state -> Z * state).


Inductive binop : Type :=
  | OOr | OAnd
  | OLt | OLe | OGt | OGe | OEq | ONe
  | OPlus | OMinus | OMul | ODiv | OMod.

Inductive unop : Type :=
  | ONot | ONeg.

Module Lang_While.

(** 然后再定义表达式的抽象语法树。*)

Inductive expr : Type :=
  | EConst (n: Z): expr
  | EVar (x: var_name): expr
  | EBinop (op: binop) (e1 e2: expr): expr
  | EUnop (op: unop) (e: expr): expr
  | EFunc (f: func_name) (es: list expr): expr.

Inductive com : Type :=
  | CSkip: com
  | CAsgn (x: var_name) (e: expr): com
  | CSeq (c1 c2: com): com
  | CIf (e: expr) (c1 c2: com): com
  | CWhile (e: expr) (c: com): com.

Definition add_sem (D1 D2: state -> Z * state) (s: state): Z * state :=
    let (z1, s1) := D1 s in
    let (z2, s2) := D2 s1 in
    (Z.add z1 z2, s2).

Definition sub_sem (D1 D2: state -> Z * state) (s: state): Z * state :=
    let (z1, s1) := D1 s in
    let (z2, s2) := D2 s1 in
    (Z.sub z1 z2, s2).

Definition mul_sem (D1 D2: state -> Z * state) (s: state): Z * state :=
    let (z1, s1) := D1 s in
    let (z2, s2) := D2 s1 in
    (Z.mul z1 z2, s2).

Definition div_sem (D1 D2: state -> Z * state) (s: state): Z * state :=
    let (z1, s1) := D1 s in
    let (z2, s2) := D2 s1 in
    (Z.div z1 z2, s2).

Definition mod_sem (D1 D2: state -> Z * state) (s: state): Z * state :=
    let (z1, s1) := D1 s in
    let (z2, s2) := D2 s1 in
    (Z.modulo z1 z2, s2).

Definition or_sem (D1 D2: state -> Z * state) (s: state): Z * state :=
    let (z1, s1) := D1 s in
    let (z2, s2) := D2 s1 in
    (if Z.eqb z1 0 then 
        if Z.eqb z2 0 then 0 else 1 
    else 1, s2).

Definition and_sem (D1 D2: state -> Z * state) (s: state): Z * state :=
    let (z1, s1) := D1 s in
    let (z2, s2) := D2 s1 in
    (if Z.eqb z1 0 then 0 
    else if Z.eqb z2 0 then 0 else 1, s2).

Definition lt_sem (D1 D2: state -> Z * state) (s: state): Z * state :=
    let (z1, s1) := D1 s in
    let (z2, s2) := D2 s1 in
    (if Z.ltb z1 z2 then 1 else 0, s2).

Definition le_sem (D1 D2: state -> Z * state) (s: state): Z * state :=
    let (z1, s1) := D1 s in
    let (z2, s2) := D2 s1 in
    (if Z.leb z1 z2 then 1 else 0, s2).

Definition gt_sem (D1 D2: state -> Z * state) (s: state): Z * state :=
    let (z1, s1) := D1 s in
    let (z2, s2) := D2 s1 in
    (if Z.gtb z1 z2 then 1 else 0, s2).

Definition ge_sem (D1 D2: state -> Z * state) (s: state): Z * state :=
    let (z1, s1) := D1 s in
    let (z2, s2) := D2 s1 in
    (if Z.geb z1 z2 then 1 else 0, s2).

Definition eq_sem (D1 D2: state -> Z * state) (s: state): Z * state :=
    let (z1, s1) := D1 s in
    let (z2, s2) := D2 s1 in
    (if Z.eqb z1 z2 then 1 else 0, s2).

Definition ne_sem (D1 D2: state -> Z * state) (s: state): Z * state :=
    let (z1, s1) := D1 s in
    let (z2, s2) := D2 s1 in
    (if Z.eqb z1 z2 then 0 else 1, s2).
    
Definition not_sem (D: state -> Z * state) (s: state): Z * state :=
    let (z1, s1) := D s in
    (if Z.eqb z1 0 then 1 else 0, s1).

Definition neg_sem (D: state -> Z * state) (s: state): Z * state :=
    let (z1, s1) := D s in
    (-z1, s1).

Fixpoint eval_exprs (D: expr -> state -> Z * state) (es: list expr) (s: state): 
    args * state :=
    match es with 
    | nil => (nil, s)
    | cons e es' => 
        let (z1, s1) := D e s in
        let (zs, s2) := (eval_exprs D es' s1) in
        (cons z1 zs, s2)
    end.


Definition func_sem (D: state -> Z * state) (s: state) : Z * state :=
    D s.
  
Fixpoint eval_expr (fs: func_state) (e: expr) (s: state) : Z * state :=
    match e with
    | EConst n => (n, s)
    | EVar X => (s X, s)
    | EBinop op e1 e2 =>
        match op with
        | OPlus => add_sem (eval_expr fs e1) (eval_expr fs e2) s
        | OMinus => sub_sem (eval_expr fs e1) (eval_expr fs e2) s
        | OMul => mul_sem (eval_expr fs e1) (eval_expr fs e2) s
        | ODiv => div_sem (eval_expr fs e1) (eval_expr fs e2) s
        | OMod => mod_sem (eval_expr fs e1) (eval_expr fs e2) s
        | OOr => or_sem (eval_expr fs e1) (eval_expr fs e2) s
        | OAnd => and_sem (eval_expr fs e1) (eval_expr fs e2) s
        | OLt => lt_sem (eval_expr fs e1) (eval_expr fs e2) s
        | OLe => le_sem (eval_expr fs e1) (eval_expr fs e2) s
        | OGt => gt_sem (eval_expr fs e1) (eval_expr fs e2) s
        | OGe => ge_sem (eval_expr fs e1) (eval_expr fs e2) s
        | OEq => eq_sem (eval_expr fs e1) (eval_expr fs e2) s
        | ONe => ne_sem (eval_expr fs e1) (eval_expr fs e2) s
        end
    | EUnop op e => 
        match op with
        | ONot => not_sem (eval_expr fs e) s
        | ONeg => neg_sem (eval_expr fs e) s
        end
    | EFunc F es => 
        let (zs, s1) := eval_exprs (eval_expr fs) es s in
        (fs F zs s1)
end.
  

  


End Lang_SimpleWhile.