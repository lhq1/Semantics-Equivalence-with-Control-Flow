(** (This following part of this file is copied from <<Software Foundation>>
volume 1. It should be only used for lecture notes and homework assignments for
course CS263 of Shanghai Jiao Tong University, 2019 spring. Any other usage are
not allowed. For the material of thses parts, please refer to the original
book.) *)

Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Relations.Relation_Definitions.
Require Export Coq.ZArith.ZArith.
Require Export Coq.Strings.String.
Require Export Coq.Logic.Classical.

Arguments clos_refl_trans {A} _ _ _.
Arguments clos_refl_trans_1n {A} _ _ _.
Arguments clos_refl_trans_n1 {A} _ _ _.

Open Scope Z.

Definition var: Type := nat.

Inductive aexp : Type :=
  | ANum (n : Z)
  | AId (X : var)
  | APlus (a1 a2 : aexp)
  | AMinus (a1 a2 : aexp)
  | AMult (a1 a2 : aexp).

Inductive bexp : Type :=
  | BTrue
  | BFalse
  | BEq (a1 a2 : aexp)
  | BLe (a1 a2 : aexp)
  | BNot (b : bexp)
  | BAnd (b1 b2 : bexp).

Coercion ANum : Z >-> aexp.

Definition bool_to_bexp (b : bool) : bexp :=
  if b then BTrue else BFalse.
Coercion bool_to_bexp : bool >-> bexp.

Bind Scope imp_scope with aexp.
Bind Scope imp_scope with bexp.
Delimit Scope imp_scope with imp.

Notation "x + y" := (APlus x y) (at level 50, left associativity) : imp_scope.
Notation "x - y" := (AMinus x y) (at level 50, left associativity) : imp_scope.
Notation "x * y" := (AMult x y) (at level 40, left associativity) : imp_scope.
Notation "x <= y" := (BLe x y) (at level 70, no associativity) : imp_scope.
Notation "x == y" := (BEq x y) (at level 70, no associativity) : imp_scope.
Notation "x && y" := (BAnd x y) (at level 40, left associativity) : imp_scope.
Notation "'!' b" := (BNot b) (at level 39, right associativity) : imp_scope.

Inductive com : Type :=
  | CSkip
  | CAss (X: var) (a : aexp)
  | CSeq (c1 c2 : com)
  | CIf (b : bexp) (c1 c2 : com)
  | CWhile (b : bexp) (c : com)
  | CBreak                       (* <--- new *)
  | CCont                        (* <--- new *)
  .

Inductive exit_kind: Type :=
  | EK_Normal
  | EK_Break
  | EK_Cont.

Bind Scope imp_scope with com.
Notation "'Skip'" :=
   CSkip : imp_scope.
Notation "c1 ;; c2" :=
  (CSeq c1 c2) (at level 80, right associativity) : imp_scope.
Notation "'While' b 'Do' c 'EndWhile'" :=
  (CWhile b c) (at level 80, right associativity) : imp_scope.
Notation "'If' c1 'Then' c2 'Else' c3 'EndIf'" :=
  (CIf c1 c2 c3) (at level 10, right associativity) : imp_scope.

Module Abstract_Pretty_Printing.
Coercion AId: var >-> aexp.
Notation "x '::=' a" :=
  (CAss x a) (at level 80) : imp_scope.
End Abstract_Pretty_Printing.

(*Remove Module Hoare_Triple.*)


Definition state: Type := nat -> Z.

Fixpoint aeval (a : aexp) (st : state) : Z :=
  match a with
  | ANum n => n
  | AId X => st X
  | APlus a1 a2 => (aeval a1 st) + (aeval a2 st)
  | AMinus a1 a2  => (aeval a1 st) - (aeval a2 st)
  | AMult a1 a2 => (aeval a1 st) * (aeval a2 st)
  end.

Definition aexp_dequiv (d1 d2: state -> Z): Prop :=
  forall st, d1 st = d2 st.

Definition aexp_equiv (a1 a2: aexp): Prop :=
  aexp_dequiv (aeval a1) (aeval a2).

Fixpoint beval (b : bexp) (st : state) : Prop :=
  match b with
  | BTrue       => True
  | BFalse      => False
  | BEq a1 a2   => (aeval a1 st) = (aeval a2 st)
  | BLe a1 a2   => (aeval a1 st) <= (aeval a2 st)
  | BNot b1     => ~ (beval b1 st)
  | BAnd b1 b2  => (beval b1 st) /\ (beval b2 st)
  end.

(** Program's denotation is defined as a ternary relation. Specifically,
[st1, ek, st2] belongs to the denotation of program [c] if and only if
executing [c] from [st1] may terminate at state [st2] with exit kind [ek]. *)

Definition skip_sem: state -> exit_kind -> state -> Prop :=
  fun st1 ek st2 =>
    st1 = st2 /\ ek = EK_Normal.

Definition asgn_sem (X: var) (E: aexp): state -> exit_kind -> state -> Prop :=
  fun st1 ek st2 =>    ek = EK_Normal/\
    st2 X = aeval E st1 /\    
    forall Y, X <> Y -> st1 Y = st2 Y.

(** Obviously, skip commands and assignment commands can only terminate normally. *)

Definition break_sem: state -> exit_kind -> state -> Prop :=
  fun st1 ek st2 =>
    st1 = st2 /\ ek = EK_Break.

Definition cont_sem: state -> exit_kind -> state -> Prop :=
  fun st1 ek st2 =>
    st1 = st2 /\ ek = EK_Cont.

(** In contrast, [CBreak] and [CCont] will never terminate will normal exit. *)

Definition seq_sem (d1 d2: state -> exit_kind -> state -> Prop)
  : state -> exit_kind -> state -> Prop
:=
  fun st1 ek st3 =>
    (exists st2, d1 st1 EK_Normal st2 /\ d2 st2 ek st3) \/
    (d1 st1 ek st3 /\ ek <> EK_Normal).

(** For sequential composition, the second command will be executed if and only
if the first one terminates normally. *)

Definition if_sem (b: bexp) (d1 d2: state -> exit_kind -> state -> Prop)
  : state -> exit_kind -> state -> Prop
:=
  fun st1 ek st2 =>
    (d1 st1 ek st2 /\ beval b st1) \/
    (d2 st1 ek st2 /\ ~beval b st1).

(** The semantics of [if] commands is trivial. Next, we define the semantics of
loops. Remember, a loop itself will never terminate by [break] or [continue]
although a loop body may break and terminates whole loop's execution. *)

Fixpoint iter_loop_body
  (b: bexp)
  (loop_body: state -> exit_kind -> state -> Prop)
  (n: nat)
  : state -> state -> Prop
:=
  match n with
  | O =>
     fun st1 st2 =>
       st1 = st2 /\ ~beval b st1
  | S n' =>
     fun st1 st3 =>
      ((exists st2,
         (loop_body) st1 EK_Normal st2 /\
         (iter_loop_body b loop_body n') st2 st3) \/
       (loop_body) st1 EK_Break st3 \/
       (exists st2,
         (loop_body) st1 EK_Cont st2 /\
         (iter_loop_body b loop_body n') st2 st3)) /\
       beval b st1
  end.

Definition loop_sem (b: bexp) (loop_body: state -> exit_kind -> state -> Prop)
  : state -> exit_kind -> state -> Prop
:=
  fun st1 ek st2 =>
    exists n, (iter_loop_body b loop_body n) st1 st2 /\ ek = EK_Normal.


Fixpoint ceval (c: com): state -> exit_kind -> state -> Prop :=
  match c with
  | CSkip => skip_sem
  | CAss X E => asgn_sem X E
  | CSeq c1 c2 => seq_sem (ceval c1) (ceval c2)
  | CIf b c1 c2 => if_sem b (ceval c1) (ceval c2)
  | CWhile b c => loop_sem b (ceval c)
  | CBreak => break_sem
  | CCont => cont_sem
  end.




Inductive aexp_halt: aexp -> Prop :=
  | AH_num : forall n, aexp_halt (ANum n).

Inductive astep : state -> aexp -> aexp -> Prop :=
  | AS_Id : forall st X,
      astep st
        (AId X) (ANum (st X))

  | AS_Plus1 : forall st a1 a1' a2,
      astep st
        a1 a1' ->
      astep st
        (APlus a1 a2) (APlus a1' a2)
  | AS_Plus2 : forall st a1 a2 a2',
      aexp_halt a1 ->
      astep st
        a2 a2' ->
      astep st
        (APlus a1 a2) (APlus a1 a2')
  | AS_Plus : forall st n1 n2,
      astep st
        (APlus (ANum n1) (ANum n2)) (ANum (n1 + n2))

  | AS_Minus1 : forall st a1 a1' a2,
      astep st
        a1 a1' ->
      astep st
        (AMinus a1 a2) (AMinus a1' a2)
  | AS_Minus2 : forall st a1 a2 a2',
      aexp_halt a1 ->
      astep st
        a2 a2' ->
      astep st
        (AMinus a1 a2) (AMinus a1 a2')
  | AS_Minus : forall st n1 n2,
      astep st
        (AMinus (ANum n1) (ANum n2)) (ANum (n1 - n2))

  | AS_Mult1 : forall st a1 a1' a2,
      astep st
        a1 a1' ->
      astep st
        (AMult a1 a2) (AMult a1' a2)
  | AS_Mult2 : forall st a1 a2 a2',
      aexp_halt a1 ->
      astep st
        a2 a2' ->
      astep st
        (AMult a1 a2) (AMult a1 a2')
  | AS_Mult : forall st n1 n2,
      astep st
        (AMult (ANum n1) (ANum n2)) (ANum (n1 * n2)).

Inductive bexp_halt: bexp -> Prop :=
  | BH_True : bexp_halt BTrue
  | BH_False : bexp_halt BFalse.

Inductive bstep : state -> bexp -> bexp -> Prop :=

  | BS_Eq1 : forall st a1 a1' a2,
      astep st
        a1 a1' ->
      bstep st
        (BEq a1 a2) (BEq a1' a2)
  | BS_Eq2 : forall st a1 a2 a2',
      aexp_halt a1 ->
      astep st
        a2 a2' ->
      bstep st
        (BEq a1 a2) (BEq a1 a2')
  | BS_Eq_True : forall st n1 n2,
      n1 = n2 ->
      bstep st
        (BEq (ANum n1) (ANum n2)) BTrue
  | BS_Eq_False : forall st n1 n2,
      n1 <> n2 ->
      bstep st
        (BEq (ANum n1) (ANum n2)) BFalse

  | BS_Le1 : forall st a1 a1' a2,
      astep st
        a1 a1' ->
      bstep st
        (BLe a1 a2) (BLe a1' a2)
  | BS_Le2 : forall st a1 a2 a2',
      aexp_halt a1 ->
      astep st
        a2 a2' ->
      bstep st
        (BLe a1 a2) (BLe a1 a2')
  | BS_Le_True : forall st n1 n2,
      n1 <= n2 ->
      bstep st
        (BLe (ANum n1) (ANum n2)) BTrue
  | BS_Le_False : forall st n1 n2,
      n1 > n2 ->
      bstep st
        (BLe (ANum n1) (ANum n2)) BFalse

  | BS_NotStep : forall st b1 b1',
      bstep st
        b1 b1' ->
      bstep st
        (BNot b1) (BNot b1')
  | BS_NotTrue : forall st,
      bstep st
        (BNot BTrue) BFalse
  | BS_NotFalse : forall st,
      bstep st
        (BNot BFalse) BTrue

  | BS_AndStep : forall st b1 b1' b2,
      bstep st
        b1 b1' ->
      bstep st
       (BAnd b1 b2) (BAnd b1' b2)
  | BS_AndTrue : forall st b,
      bstep st
       (BAnd BTrue b) b
  | BS_AndFalse : forall st b,
      bstep st
       (BAnd BFalse b) BFalse.


Section Small_Step_Semantics.

(** The small step semantics for [break] and [continue] is based on control
stack. Specifically, every element in control stack describe a loop (loop
condition and loop body) and a command after loop. *)

Definition cstack: Type := list (bexp * com * com).


(** In order to define a small step for control flow, it is useful to define
the following properties:

    - a command [c] starts with [break]: [start_with_break c];

    - a command [c] starts with [continue]: [start_with_break c];

    - a command [c] is equivalent with a sequential composition of loop
      [CWhile b c1] and another command [c2]: [start_with_loop c b c1 c2].
*)

Inductive start_with_break: com -> Prop :=
| SWB_Break: start_with_break CBreak
| SWB_Seq: forall c1 c2,
             start_with_break c1 ->
             start_with_break (CSeq c1 c2).

Inductive start_with_cont: com -> Prop :=
| SWC_Cont: start_with_cont CCont
| SWC_Seq: forall c1 c2,
             start_with_cont c1 ->
             start_with_cont (CSeq c1 c2).

Inductive start_with_loop: com -> bexp -> com -> com -> Prop :=
| SWL_While: forall b c, start_with_loop (CWhile b c) b c CSkip
| SWL_Seq: forall c1 b c11 c12 c2,
             start_with_loop c1 b c11 c12 ->
             start_with_loop (CSeq c1 c2) b c11 (CSeq c12 c2).

(** Now, we are ready to define a small step semantics with control stack. *)

Inductive com': Type :=
| CNormal (s: cstack) (c: com): com'
|CLoopCond (s: cstack) (b: bexp): com'.

  


Inductive cstep : (com' * state) -> (com' * state) -> Prop :=
  | CS_AssStep : forall st s X a a',
      astep st a a' ->
      cstep
        (CNormal s (CAss X a), st)
        (CNormal s (CAss X a'), st)
  | CS_Ass : forall st1 st2 s X n,
      st2 X = n ->
      (forall Y, X <> Y -> st1 Y = st2 Y) ->
      cstep
        (CNormal s (CAss X (ANum n)), st1)
        (CNormal s CSkip, st2)
  | CS_SeqStep : forall st s c1 c1' st' c2,
      cstep
        (CNormal s c1, st)
        (CNormal s c1', st') ->
      cstep
        (CNormal s (CSeq c1 c2), st)
        (CNormal s (CSeq c1' c2), st')
  | CS_Seq : forall st s c2,
      cstep
        (CNormal s (CSeq CSkip c2), st)
        (CNormal s c2, st)
  | CS_IfStep : forall st s b b' c1 c2,
      bstep st b b' ->
      cstep
        (CNormal s (CIf b c1 c2), st)
        (CNormal s (CIf b' c1 c2), st)
  | CS_IfTrue : forall st s c1 c2,
      cstep
        (CNormal s (CIf BTrue c1 c2), st)
        (CNormal s c1, st)
  | CS_IfFalse : forall st s c1 c2,
      cstep
        (CNormal s (CIf BFalse c1 c2), st)
        (CNormal s c2, st)
  | CS_While : forall st s c b c1 c2,                 (* <-- new *)
      start_with_loop c b c1 c2 ->
      cstep
        (CNormal s c, st)
        (CLoopCond (cons (b, c1, c2) s) b, st)
  | CS_WhileStep : forall st s b b' b'' c1 c2,        (* <-- new *)
      bstep st b' b'' ->
      cstep
        (CLoopCond (cons (b, c1, c2) s) b', st)
        (CLoopCond (cons (b, c1, c2) s) b'', st)
  | CS_WhileTrue : forall st s b c1 c2,               (* <-- new *)
      cstep
        (CLoopCond (cons (b, c1, c2) s) BTrue, st)
        (CNormal (cons (b, c1, c2) s) c1, st)
  | CS_WhileFalse : forall st s b c1 c2,              (* <-- new *)
      cstep
        (CLoopCond (cons (b, c1, c2) s) BFalse, st)
        (CNormal s c2, st)
  | CS_Skip : forall st s b c1 c2,                    (* <-- new *)
      cstep
        (CNormal (cons (b, c1, c2) s) CSkip, st)
        (CLoopCond (cons (b, c1, c2) s) b, st)
  | CS_Break : forall st s b c1 c2 c,                 (* <-- new *)
      start_with_break c ->
      cstep
        (CNormal (cons (b, c1, c2) s) c, st)
        (CNormal s c2, st)
  | CS_Cont : forall st s b c1 c2 c,                  (* <-- new *)
      start_with_cont c ->
      cstep
        (CNormal (cons (b, c1, c2) s) c, st)
        (CLoopCond (cons (b, c1, c2) s) b, st)
.

End Small_Step_Semantics.

Definition multi_astep (st: state): aexp -> aexp -> Prop := clos_refl_trans (astep st).

Definition multi_bstep (st: state): bexp -> bexp -> Prop := clos_refl_trans (bstep st).

Definition multi_cstep: com' * state -> com' * state -> Prop := clos_refl_trans cstep.


Module Assertion_D.
Import Abstract_Pretty_Printing.

Definition logical_var: Type := nat.

Inductive aexp' : Type :=
  | ANum' (t : term)
  | AId' (X: var)
  | APlus' (a1 a2 : aexp')
  | AMinus' (a1 a2 : aexp')
  | AMult' (a1 a2 : aexp')
with term : Type :=
  | TNum (n : Z)
  | TId (x: logical_var)
  | TDenote (a : aexp')
  | TPlus (t1 t2 : term)
  | TMinus (t1 t2 : term)
  | TMult (t1 t2 : term).

Inductive bexp' : Type :=
  | BTrue'
  | BFalse'
  | BEq' (a1 a2 : aexp')
  | BLe' (a1 a2 : aexp')
  | BNot' (b : bexp')
  | BAnd' (b1 b2 : bexp').

Coercion ANum' : term >-> aexp'.
Coercion AId' : var >-> aexp'.
Bind Scope vimp_scope with aexp'.
Bind Scope vimp_scope with bexp'.
Delimit Scope vimp_scope with vimp.

Notation "x + y" := (APlus' x y) (at level 50, left associativity) : vimp_scope.
Notation "x - y" := (AMinus' x y) (at level 50, left associativity) : vimp_scope.
Notation "x * y" := (AMult' x y) (at level 40, left associativity) : vimp_scope.
Notation "x <= y" := (BLe' x y) (at level 70, no associativity) : vimp_scope.
Notation "x == y" := (BEq' x y) (at level 70, no associativity) : vimp_scope.
Notation "x && y" := (BAnd' x y) (at level 40, left associativity) : vimp_scope.
Notation "'!' b" := (BNot' b) (at level 39, right associativity) : vimp_scope.

Coercion TNum : Z >-> term.
Coercion TId: logical_var >-> term.
Bind Scope term_scope with term.
Delimit Scope term_scope with term.

Notation "x + y" := (TPlus x y) (at level 50, left associativity) : term_scope.
Notation "x - y" := (TMinus x y) (at level 50, left associativity) : term_scope.
Notation "x * y" := (TMult x y) (at level 40, left associativity) : term_scope.
Notation "{[ a ]}" := (TDenote ((a)%vimp)) (at level 30, no associativity) : term_scope.

(** Of course, every normal expression is a variable expression. *)

Fixpoint ainj (a: aexp): aexp' :=
  match a with
  | ANum n        => ANum' (TNum n)
  | AId X         => AId' X
  | APlus a1 a2   => APlus' (ainj a1) (ainj a2)
  | AMinus a1 a2  => AMinus' (ainj a1) (ainj a2)
  | AMult a1 a2   => AMult' (ainj a1) (ainj a2)
  end.

Fixpoint binj (b : bexp): bexp' :=
  match b with
  | BTrue       => BTrue'
  | BFalse      => BFalse'
  | BEq a1 a2   => BEq' (ainj a1) (ainj a2)
  | BLe a1 a2   => BLe' (ainj a1) (ainj a2)
  | BNot b1     => BNot' (binj b1)
  | BAnd b1 b2  => BAnd' (binj b1) (binj b2)
  end.

(** The following two lines of [Coercion] definition say that Coq will treat
[a] as [ainj b] and treat [b] a s [binj b] automatically when a variable
expression is needed. *)

Coercion ainj: aexp >-> aexp'.
Coercion binj: bexp >-> bexp'.

Inductive Assertion : Type :=
  | AssnLe (t1 t2 : term)
  | AssnLt (t1 t2 : term)
  | AssnEq (t1 t2 : term)
  | AssnDenote (b: bexp')
  | AssnOr (P1 P2 : Assertion)
  | AssnAnd (P1 P2 : Assertion)
  | AssnImpl (P1 P2 : Assertion)
  | AssnNot (P: Assertion)
  | AssnExists (x: logical_var) (P: Assertion)
  | AssnForall (x: logical_var) (P: Assertion).

Bind Scope assert_scope with Assertion.
Delimit Scope assert_scope with assert.

Notation "x <= y" := (AssnLe ((x)%term) ((y)%term)) (at level 70, no associativity) : assert_scope.
Notation "x '<' y" := (AssnLt ((x)%term) ((y)%term)) (at level 70, no associativity) : assert_scope.
Notation "x == y" := (AssnEq ((x)%term) ((y)%term)) (at level 70, no associativity) : assert_scope.
Notation "{[ b ]}" := (AssnDenote ((b)%vimp)) (at level 30, no associativity) : assert_scope.
Notation "P1 'OR' P2" := (AssnOr P1 P2) (at level 76, left associativity) : assert_scope.
Notation "P1 'AND' P2" := (AssnAnd P1 P2) (at level 74, left associativity) : assert_scope.
Notation "P1 'IMPLY' P2" := (AssnImpl P1 P2) (at level 77, right associativity) : assert_scope.
Notation "'NOT' P" := (AssnNot P) (at level 73, right associativity) : assert_scope.
Notation "'EXISTS' x ',' P " := (AssnExists x ((P)%assert)) (at level 79,  right associativity) : assert_scope.
Notation "'FORALL' x ',' P " := (AssnForall x ((P)%assert)) (at level 79, right associativity) : assert_scope.

Fixpoint aexp_rename (x y: logical_var) (a: aexp'): aexp' :=
    match a with
    | ANum' t => ANum' (term_rename x y t)
    | AId' X => AId' X
    | APlus' a1 a2 => APlus' (aexp_rename x y a1) (aexp_rename x y a2)
    | AMinus' a1 a2 => AMinus' (aexp_rename x y a1) (aexp_rename x y a2)
    | AMult' a1 a2 => AMult' (aexp_rename x y a1) (aexp_rename x y a2)
    end
with term_rename (x y: logical_var) (t: term) :=
    match t with
    | TNum n => TNum n
    | TId x' => 
        if Nat.eq_dec x x'
        then TId y
        else TId x'
    | TDenote a => TDenote (aexp_rename x y a)
    | TPlus t1 t2 => TPlus (term_rename x y t1) (term_rename x y t2)
    | TMinus t1 t2 => TMinus (term_rename x y t1) (term_rename x y t2)
    | TMult t1 t2 => TMult (term_rename x y t1) (term_rename x y t2)
    end.

Fixpoint bexp_rename (x y: logical_var) (b: bexp'): bexp' :=
    match b with
    | BTrue' => BTrue'
    | BFalse' => BFalse'
    | BEq' a1 a2 => BEq' (aexp_rename x y a1) (aexp_rename x y a2)
    | BLe' a1 a2 => BLe' (aexp_rename x y a1) (aexp_rename x y a2)
    | BNot' b => BNot' (bexp_rename x y b)
    | BAnd' b1 b2 => BAnd' (bexp_rename x y b1) (bexp_rename x y b2)
    end.

Fixpoint assn_rename (x y: logical_var) (d: Assertion): Assertion :=
    match d with
    | AssnLe t1 t2    => AssnLe (term_rename x y t1) (term_rename x y t2)
    | AssnLt t1 t2    => AssnLt (term_rename x y t1) (term_rename x y t2)
    | AssnEq t1 t2    => AssnEq (term_rename x y t1) (term_rename x y t2)
    | AssnDenote b    => AssnDenote (bexp_rename x y b)
    | AssnOr P1 P2    => AssnOr (assn_rename x y P1) (assn_rename x y P2)
    | AssnAnd P1 P2   => AssnAnd (assn_rename x y P1) (assn_rename x y P2)
    | AssnImpl P1 P2  => AssnImpl (assn_rename x y P1) (assn_rename x y P2)
    | AssnNot P       => AssnNot (assn_rename x y P)
    | AssnExists x' P => if Nat.eq_dec x x'
                         then AssnExists x' P
                         else AssnExists x' (assn_rename x y P)
    | AssnForall x' P => if Nat.eq_dec x x'
                         then AssnForall x' P
                         else AssnForall x' (assn_rename x y P)
    end.

Fixpoint aexp_max_var (a: aexp'): logical_var :=
    match a with
    | ANum' t => term_max_var t
    | AId' X => O
    | APlus' a1 a2 => max (aexp_max_var a1) (aexp_max_var a2)
    | AMinus' a1 a2 => max (aexp_max_var a1) (aexp_max_var a2)
    | AMult' a1 a2 => max (aexp_max_var a1) (aexp_max_var a2)
    end
with term_max_var (t: term): logical_var :=
    match t with
    | TNum n => O
    | TId x => x
    | TDenote a => aexp_max_var a
    | TPlus t1 t2 => max (term_max_var t1) (term_max_var t2)
    | TMinus t1 t2 => max (term_max_var t1) (term_max_var t2)
    | TMult t1 t2 => max (term_max_var t1) (term_max_var t2)
    end.

Fixpoint bexp_max_var (b: bexp'): logical_var :=
    match b with
    | BTrue' => O
    | BFalse' => O
    | BEq' a1 a2 => max (aexp_max_var a1) (aexp_max_var a2)
    | BLe' a1 a2 => max (aexp_max_var a1) (aexp_max_var a2)
    | BNot' b => bexp_max_var b
    | BAnd' b1 b2 => max (bexp_max_var b1) (bexp_max_var b2)
    end.

Fixpoint assn_max_var (d: Assertion): logical_var :=
    match d with
    | AssnLe t1 t2    => max (term_max_var t1) (term_max_var t2)
    | AssnLt t1 t2    => max (term_max_var t1) (term_max_var t2)
    | AssnEq t1 t2    => max (term_max_var t1) (term_max_var t2)
    | AssnDenote b    => bexp_max_var b
    | AssnOr P1 P2    => max (assn_max_var P1) (assn_max_var P2)
    | AssnAnd P1 P2   => max (assn_max_var P1) (assn_max_var P2)
    | AssnImpl P1 P2  => max (assn_max_var P1) (assn_max_var P2)
    | AssnNot P       => assn_max_var P
    | AssnExists x' P => max x' (assn_max_var P)
    | AssnForall x' P => max x' (assn_max_var P)
    end.

Definition new_var (P: Assertion) (E: aexp'): logical_var :=
  S (max (assn_max_var P) (aexp_max_var E)).

Fixpoint aexp_sub (X: var) (E: aexp') (a: aexp'): aexp' :=
    match a with
    | ANum' t => ANum' (term_sub X E t)
    | AId' X' =>
         if Nat.eq_dec X X'
         then E
         else AId' X'
    | APlus' a1 a2 => APlus' (aexp_sub X E a1) (aexp_sub X E a2)
    | AMinus' a1 a2 => AMinus' (aexp_sub X E a1) (aexp_sub X E a2)
    | AMult' a1 a2 => AMult' (aexp_sub X E a1) (aexp_sub X E a2)
    end
with term_sub (X: var) (E: aexp') (t: term) :=
    match t with
    | TNum n => TNum n
    | TId x => TId x
    | TDenote a => TDenote (aexp_sub X E a)
    | TPlus t1 t2 => TPlus (term_sub X E t1) (term_sub X E t2)
    | TMinus t1 t2 => TMinus (term_sub X E t1) (term_sub X E t2)
    | TMult t1 t2 => TMult (term_sub X E t1) (term_sub X E t2)
    end.

Fixpoint bexp_sub (X: var) (E: aexp') (b: bexp'): bexp' :=
    match b with
    | BTrue' => BTrue'
    | BFalse' => BFalse'
    | BEq' a1 a2 => BEq' (aexp_sub X E a1) (aexp_sub X E a2)
    | BLe' a1 a2 => BLe' (aexp_sub X E a1) (aexp_sub X E a2)
    | BNot' b => BNot' (bexp_sub X E b)
    | BAnd' b1 b2 => BAnd' (bexp_sub X E b1) (bexp_sub X E b2)
    end.

Fixpoint aexp_occur (x: logical_var) (a: aexp'): nat :=
    match a with
    | ANum' t => term_occur x t
    | AId' X => O
    | APlus' a1 a2 => (aexp_occur x a1) + (aexp_occur x a2)
    | AMinus' a1 a2 => (aexp_occur x a1) + (aexp_occur x a2)
    | AMult' a1 a2 => (aexp_occur x a1) + (aexp_occur x a2)
    end
with term_occur (x: logical_var) (t: term): nat :=
    match t with
    | TNum n => O
    | TId x' => if Nat.eq_dec x x' then S O else O
    | TDenote a => aexp_occur x a
    | TPlus t1 t2 => (term_occur x t1) + (term_occur x t2)
    | TMinus t1 t2 => (term_occur x t1) + (term_occur x t2)
    | TMult t1 t2 => (term_occur x t1) + (term_occur x t2)
    end.

Fixpoint bexp_occur (x: logical_var) (b: bexp'): nat :=
    match b with
    | BTrue' => O
    | BFalse' => O
    | BEq' a1 a2 => (aexp_occur x a1) + (aexp_occur x a2)
    | BLe' a1 a2 => (aexp_occur x a1) + (aexp_occur x a2)
    | BNot' b => bexp_occur x b
    | BAnd' b1 b2 => (bexp_occur x b1) + (bexp_occur x b2)
    end.

Fixpoint assn_free_occur (x: logical_var) (d: Assertion): nat :=
    match d with
    | AssnLe t1 t2    => (term_occur x t1) + (term_occur x t2)
    | AssnLt t1 t2    => (term_occur x t1) + (term_occur x t2)
    | AssnEq t1 t2    => (term_occur x t1) + (term_occur x t2)
    | AssnDenote b    => bexp_occur x b
    | AssnOr P1 P2    => (assn_free_occur x P1) + (assn_free_occur x P2)
    | AssnAnd P1 P2   => (assn_free_occur x P1) + (assn_free_occur x P2)
    | AssnImpl P1 P2  => (assn_free_occur x P1) + (assn_free_occur x P2)
    | AssnNot P       => assn_free_occur x P
    | AssnExists x' P => if Nat.eq_dec x x'
                         then O
                         else assn_free_occur x P
    | AssnForall x' P => if Nat.eq_dec x x'
                         then O
                         else assn_free_occur x P
    end.

Fixpoint assn_occur (x: logical_var) (d: Assertion): nat :=
    match d with
    | AssnLe t1 t2    => (term_occur x t1) + (term_occur x t2)
    | AssnLt t1 t2    => (term_occur x t1) + (term_occur x t2)
    | AssnEq t1 t2    => (term_occur x t1) + (term_occur x t2)
    | AssnDenote b    => bexp_occur x b
    | AssnOr P1 P2    => (assn_occur x P1) + (assn_occur x P2)
    | AssnAnd P1 P2   => (assn_occur x P1) + (assn_occur x P2)
    | AssnImpl P1 P2  => (assn_occur x P1) + (assn_occur x P2)
    | AssnNot P       => assn_occur x P
    | AssnExists x' P => if Nat.eq_dec x x'
                         then S (assn_occur x P)
                         else assn_occur x P
    | AssnForall x' P => if Nat.eq_dec x x'
                         then S (assn_occur x P)
                         else assn_occur x P
    end.

Lemma assn_occur_free_occur: forall x P,
  (assn_free_occur x P <= assn_occur x P)%nat.
Proof.
  intros.
  induction P; simpl.
  - apply le_n.
  - apply le_n.
  - apply le_n.
  - apply le_n.
  - apply plus_le_compat; tauto.
  - apply plus_le_compat; tauto.
  - apply plus_le_compat; tauto.
  - exact IHP.
  - destruct (Nat.eq_dec x x0).
    * apply Nat.le_0_l.
    * exact IHP.
  - destruct (Nat.eq_dec x x0).
    * apply Nat.le_0_l.
    * exact IHP.
Qed.

Corollary assn_occur_O: forall x P,
  assn_occur x P = O ->
  assn_free_occur x P = O.
Proof.
  intros.
  pose proof assn_occur_free_occur x P.
  rewrite H in H0.
  inversion H0.
  reflexivity.
Qed.

Fixpoint rename_all (E: aexp') (d: Assertion): Assertion :=
    match d with
    | AssnLe t1 t2   => AssnLe t1 t2
    | AssnLt t1 t2   => AssnLt t1 t2
    | AssnEq t1 t2   => AssnEq t1 t2
    | AssnDenote b   => AssnDenote b
    | AssnOr P1 P2   => AssnOr (rename_all E P1) (rename_all E P2)
    | AssnAnd P1 P2  => AssnAnd (rename_all E P1) (rename_all E P2)
    | AssnImpl P1 P2 => AssnImpl (rename_all E P1) (rename_all E P2)
    | AssnNot P      => AssnNot (rename_all E P)
    | AssnExists x P => match aexp_occur x E with
                        | O => AssnExists x (rename_all E P)
                        | _ => AssnExists
                                 (new_var (rename_all E P) E)
                                 (assn_rename x
                                   (new_var (rename_all E P) E)
                                   (rename_all E P))
                        end
    | AssnForall x P => match aexp_occur x E with
                        | O => AssnForall x (rename_all E P)
                        | _ => AssnForall
                                 (new_var (rename_all E P) E)
                                 (assn_rename x
                                   (new_var (rename_all E P) E)
                                   (rename_all E P))
                        end
    end.

Fixpoint naive_sub (X: var) (E: aexp') (d: Assertion): Assertion :=
    match d with
    | AssnLe t1 t2   => AssnLe (term_sub X E t1) (term_sub X E t2)
    | AssnLt t1 t2   => AssnLt (term_sub X E t1) (term_sub X E t2)
    | AssnEq t1 t2   => AssnEq (term_sub X E t1) (term_sub X E t2)
    | AssnDenote b   => AssnDenote (bexp_sub X E b)
    | AssnOr P1 P2   => AssnOr (naive_sub X E P1) (naive_sub X E P2)
    | AssnAnd P1 P2  => AssnAnd (naive_sub X E P1) (naive_sub X E P2)
    | AssnImpl P1 P2 => AssnImpl (naive_sub X E P1) (naive_sub X E P2)
    | AssnNot P      => AssnNot (naive_sub X E P)
    | AssnExists x P => AssnExists x (naive_sub X E P)
    | AssnForall x P => AssnForall x (naive_sub X E P)
    end.

Definition assn_sub (X: var) (E: aexp') (P: Assertion): Assertion :=
  naive_sub X E (rename_all E P).


Notation "d [ X |-> a ]" := (assn_sub X a ((d)%assert)) (at level 10, X at next level) : assert_scope.
Notation "a0 [ X |-> a ]" := (aexp_sub X a ((a0)%imp)) (at level 10, X at next level) : imp_scope.

Inductive hoare_triple: Type :=
| Build_hoare_triple (P: Assertion) (c: com) (Q: Assertion) (QB: Assertion) (QC: Assertion).

Notation "{{ P }}  c  {{ Q }} {{ QB }} {{ QC }}" :=
  (Build_hoare_triple P c%imp Q QB QC) (at level 90, c at next level).


Class FirstOrderLogic: Type := {
  FOL_provable: Assertion -> Prop
}.

Definition derives {T: FirstOrderLogic} (P Q: Assertion): Prop :=
  FOL_provable (P IMPLY Q).

Notation "P '|--' Q" :=
  (derives ((P)%assert) ((Q)%assert)) (at level 90, no associativity).

Inductive provable {T: FirstOrderLogic}: hoare_triple -> Prop :=
  | hoare_seq : forall (P Q R RB RC: Assertion) (c1 c2: com),
      provable ({{P}} c1 {{Q}} {{RB}} {{RC}}) ->
      provable ({{Q}} c2 {{R}} {{RB}} {{RC}}) ->
      provable ({{P}} c1;;c2 {{R}} {{RB}} {{RC}})
  | hoare_skip : forall P,
      provable ({{P}} CSkip {{P}} {{ {[ BFalse]} }} {{ {[ BFalse]} }})
  | hoare_if : forall P Q QB QC (b: bexp) c1 c2,
      provable ({{ P AND {[b]} }} c1 {{ Q }} {{QB}} {{QC}}) ->
      provable ({{ P AND NOT {[b]} }} c2 {{ Q }} {{QB}} {{QC}}) ->
      provable ({{ P }} If b Then c1 Else c2 EndIf {{ Q }} {{QB}} {{QC}})
  | hoare_while : forall I P (b: bexp) c,
      provable ({{ I AND {[b]} }} c {{I}} {{P}} {{I}}) ->
      provable ({{I}} While b Do c EndWhile {{ P OR (I AND NOT {[b]}) }} {{ {[ BFalse]} }} {{ {[ BFalse]} }})
  | hoare_asgn_bwd : forall P (X: var) (E: aexp),
      provable ({{ P [ X |-> E] }} X ::= E {{ P }} {{ {[ BFalse]} }} {{ {[ BFalse]} }})
  | hoare_consequence : forall (P P' Q Q' QB QB' QC QC' : Assertion) c,
      P |-- P' ->
      provable ({{P'}} c {{Q'}} {{QB'}} {{QC'}}) ->
      Q' |-- Q ->
      QB' |-- QB ->
      QC' |-- QC ->
      provable ({{P}} c {{Q}} {{QB}} {{QC}})
   | hoare_break: forall P,
      provable({{P}} CBreak {{ {[BFalse]} }} {{P}} {{ {[BFalse]} }})
   | hoare_cont: forall P,
      provable({{P}} CCont {{ {[BFalse]} }} {{ {[BFalse]} }} {{P}}).


Notation "|--  tr" := (provable tr) (at level 91, no associativity).

Definition Lassn: Type := logical_var -> Z.

Definition Lassn_update (La: Lassn) (x: logical_var) (v: Z): Lassn :=
  fun y => if (Nat.eq_dec x y) then v else La y.

Lemma Lassn_update_spec: forall La x v,
  (Lassn_update La x v) x = v /\
  (forall y, x <> y -> La y = (Lassn_update La x v) y).
Proof.
  intros.
  unfold Lassn_update.
  split.
  + destruct (Nat.eq_dec x x).
    - reflexivity.
    - assert (x = x). { reflexivity. }
      tauto.
  + intros.
    destruct (Nat.eq_dec x y).
    - tauto.
    - reflexivity.
Qed.

Definition Interp: Type := state * Lassn.

Definition Interp_Lupdate (J: Interp) (x: logical_var) (v: Z): Interp :=
  (fst J, Lassn_update (snd J) x v).

Fixpoint aexp'_denote (J: Interp) (a: aexp'): Z :=
    match a with
    | ANum' t => term_denote J t
    | AId' X => (fst J) X
    | APlus' a1 a2 => aexp'_denote J a1 + aexp'_denote J a2
    | AMinus' a1 a2 => aexp'_denote J a1 - aexp'_denote J a2
    | AMult' a1 a2 => aexp'_denote J a1 * aexp'_denote J a2
    end
with term_denote (J: Interp) (t: term): Z :=
    match t with
    | TNum n => n
    | TId x => (snd J) x
    | TDenote a => aexp'_denote J a
    | TPlus t1 t2 => term_denote J t1 + term_denote J t2
    | TMinus t1 t2 => term_denote J t1 - term_denote J t2
    | TMult t1 t2 => term_denote J t1 * term_denote J t2
    end.

Fixpoint bexp'_denote (J: Interp) (b: bexp'): Prop :=
    match b with
    | BTrue' => True
    | BFalse' => False
    | BEq' a1 a2 => aexp'_denote J a1 = aexp'_denote J a2
    | BLe' a1 a2 => (aexp'_denote J a1 <= aexp'_denote J a2)%Z
    | BNot' b => ~ bexp'_denote J b
    | BAnd' b1 b2 => bexp'_denote J b1 /\ bexp'_denote J b2
    end.

Fixpoint satisfies (J: Interp) (d: Assertion): Prop :=
    match d with
    | AssnLe t1 t2 => (term_denote J t1 <= term_denote J t2)%Z
    | AssnLt t1 t2 => (term_denote J t1 < term_denote J t2)%Z
    | AssnEq t1 t2 => (term_denote J t1 = term_denote J t2)%Z
    | AssnDenote b => bexp'_denote J b
    | AssnOr P1 P2 => (satisfies J P1) \/ (satisfies J P2)
    | AssnAnd P1 P2 => (satisfies J P1) /\ (satisfies J P2)
    | AssnImpl P1 P2 => ~ (satisfies J P1) \/ (satisfies J P2)
    | AssnNot P => ~ (satisfies J P)
    | AssnExists x P => exists v, satisfies (Interp_Lupdate J x v) P
    | AssnForall x P => forall v, satisfies (Interp_Lupdate J x v) P
    end.

Notation "J  |==  x" := (satisfies J x) (at level 90, no associativity).


Definition valid (Tr: hoare_triple): Prop :=
  match Tr with
  | Build_hoare_triple P c Q QB QC =>
      forall La st1 st2 st3 st4,
        (st1, La) |== P -> (ceval c st1 EK_Normal st2 -> (st2, La) |== Q) /\
        (ceval c st1 EK_Break st3 -> (st3, La) |== QB) /\
        (ceval c st1 EK_Cont st4 -> (st4, La) |== QC)
  end.
(*   match Tr with
  | Build_hoare_triple P c Q QB QC =>
      forall La st1 st2 st3 st4,
        (st1, La) |== P -> ceval c st1 EK_Normal st2
        -> ceval c st1 EK_Break st3 -> ceval c st1 EK_Cont st4
        -> ((st2, La) |== Q) /\ ((st3, La) |== QB) /\ ((st4, La) |== QC)
  end. *)

Notation "|==  Tr" := (valid Tr) (at level 91, no associativity).

Lemma aeval_aexp'_denote: forall st La a,
  aeval a st = aexp'_denote (st, La) (ainj a).
Proof.
  intros.
  induction a; simpl.
  + reflexivity.
  + reflexivity.
  + rewrite IHa1, IHa2.
    reflexivity.
  + rewrite IHa1, IHa2.
    reflexivity.
  + rewrite IHa1, IHa2.
    reflexivity.
Qed.

Lemma beval_bexp'_denote: forall st La b,
  beval b st <-> bexp'_denote (st, La) (binj b).
Proof.
  intros.
  induction b; simpl.
  + tauto.
  + tauto.
  + rewrite <- aeval_aexp'_denote.
    rewrite <- aeval_aexp'_denote.
    tauto.
  + rewrite <- aeval_aexp'_denote.
    rewrite <- aeval_aexp'_denote.
    tauto.
  + tauto.
  + tauto.
Qed.

Record Interp_Equiv (J1 J2: Interp): Prop := {
  state_equiv: forall X: var, fst J1 X = fst J2 X;
  Lassn_equiv: forall x: logical_var, snd J1 x = snd J2 x
}.

Lemma Interp_Equiv_trans: forall J1 J2 J3,
  Interp_Equiv J1 J2 ->
  Interp_Equiv J2 J3 ->
  Interp_Equiv J1 J3.
Proof.
  intros.
  destruct H as [?H ?H].
  destruct H0 as [?H ?H].
  constructor.
  + intros.
    specialize (H X).
    specialize (H0 X).
    rewrite H, H0.
    reflexivity.
  + intros.
    specialize (H1 x).
    specialize (H2 x).
    rewrite H1, H2.
    reflexivity.
Qed.

Lemma Interp_Equiv_sym: forall J1 J2,
  Interp_Equiv J1 J2 ->
  Interp_Equiv J2 J1.
Proof.
  intros.
  destruct H as [?H ?H].
  constructor.
  + intros.
    rewrite H; reflexivity.
  + intros.
    rewrite H0; reflexivity.
Qed.

Lemma Interp_Equiv_Interp_Lupdate: forall J1 J2 x v,
  Interp_Equiv J1 J2 ->
  Interp_Equiv (Interp_Lupdate J1 x v) (Interp_Lupdate J2 x v).
Proof.
  intros.
  apply Build_Interp_Equiv.
  + intros.
    simpl.
    apply state_equiv.
    exact H.
  + intros.
    destruct J1 as [st1 La1], J2 as [st2 La2].
    simpl.
    unfold Lassn_update.
    destruct (Nat.eq_dec x x0).
    - reflexivity.
    - pose proof Lassn_equiv _ _ H.
      simpl in H0.
      apply H0.
Qed.

Lemma Lassn_update_update_self: forall st La x,
  Interp_Equiv
    (st, Lassn_update La x (La x))
    (st, La).
Proof.
  intros.
  apply Build_Interp_Equiv.
  + intros.
    simpl.
    reflexivity.
  + intros.
    simpl.
    unfold Lassn_update.
    destruct (Nat.eq_dec x x0).
    - subst x0;
      reflexivity.
    - reflexivity.
Qed.

Lemma Lassn_update_update_same: forall st La x v1 v2,
  Interp_Equiv
    (st, Lassn_update (Lassn_update La x v1) x v2)
    (st, Lassn_update La x v2).
Proof.
  intros.
  apply Build_Interp_Equiv.
  + intros.
    simpl.
    reflexivity.
  + intros.
    simpl.
    unfold Lassn_update.
    destruct (Nat.eq_dec x x0).
    - reflexivity.
    - reflexivity.
Qed.

Lemma Lassn_update_update_diff: forall st La x1 x2 v1 v2,
  x1 <> x2 ->
  Interp_Equiv
    (st, Lassn_update (Lassn_update La x1 v1) x2 v2)
    (st, Lassn_update (Lassn_update La x2 v2) x1 v1).
Proof.
  intros.
  apply Build_Interp_Equiv.
  + intros.
    simpl.
    reflexivity.
  + intros.
    simpl.
    unfold Lassn_update.
    destruct (Nat.eq_dec x1 x), (Nat.eq_dec x2 x).
    - exfalso.
      apply H; subst; reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
Qed.

Definition state_update (st: state) (X: var) (v: Z): state :=
  fun Y => if (Nat.eq_dec X Y) then v else st Y.

Lemma state_update_spec: forall st X v,
  (state_update st X v) X = v /\
  (forall Y, X <> Y -> st Y = (state_update st X v) Y).
Proof.
  intros.
  unfold state_update.
  split.
  + destruct (Nat.eq_dec X X).
    - reflexivity.
    - assert (X = X). { reflexivity. }
      tauto.
  + intros.
    destruct (Nat.eq_dec X Y).
    - tauto.
    - reflexivity.
Qed.

Lemma state_update_update_same: forall st La X v1 v2,
  Interp_Equiv
    (state_update (state_update st X v1) X v2, La)
    (state_update st X v2, La).
Proof.
  intros.
  apply Build_Interp_Equiv.
  + intros.
    simpl.
    unfold state_update.
    destruct (Nat.eq_dec X X0).
    - reflexivity.
    - reflexivity.
  + intros.
    simpl.
    reflexivity.
Qed.

Lemma state_update_update_diff: forall st La X1 X2 v1 v2,
  X1 <> X2 ->
  Interp_Equiv
    (state_update (state_update st X1 v1) X2 v2, La)
    (state_update (state_update st X2 v2) X1 v1, La).
Proof.
  intros.
  apply Build_Interp_Equiv.
  + intros.
    simpl.
    unfold state_update.
    destruct (Nat.eq_dec X1 X), (Nat.eq_dec X2 X).
    - exfalso.
      apply H; subst; reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
  + intros.
    simpl.
    reflexivity.
Qed.

Lemma state_update_update_self: forall st La X,
  Interp_Equiv
    (state_update st X (st X), La)
    (st, La).
Proof.
  intros.
  apply Build_Interp_Equiv.
  + intros.
    simpl.
    unfold state_update.
    destruct (Nat.eq_dec X X0).
    - subst X0;
      reflexivity.
    - reflexivity.
  + intros.
    simpl.
    reflexivity.
Qed.

Fixpoint com'_rename(c:com'):=
match c with
  |CNormal s c=>CNormal s c
  |CLoopCond s b=>CNormal s CSkip
  end.
Lemma aexp'_denote_Interp_Equiv: forall J1 J2 a,
  Interp_Equiv J1 J2 ->
  aexp'_denote J1 a = aexp'_denote J2 a
with term_denote_Interp_Equiv: forall J1 J2 t,
  Interp_Equiv J1 J2 ->
  term_denote J1 t = term_denote J2 t.
Proof.
{
  clear aexp'_denote_Interp_Equiv.
  intros.
  induction a; simpl.
  + apply term_denote_Interp_Equiv.
    exact H.
  + apply state_equiv.
    exact H.
  + rewrite IHa1, IHa2.
    reflexivity.
  + rewrite IHa1, IHa2.
    reflexivity.
  + rewrite IHa1, IHa2.
    reflexivity.
}
{
  clear term_denote_Interp_Equiv.
  intros.
  induction t; simpl.
  + reflexivity.
  + apply Lassn_equiv.
    exact H.
  + apply aexp'_denote_Interp_Equiv.
    exact H.
  + rewrite IHt1, IHt2.
    reflexivity.
  + rewrite IHt1, IHt2.
    reflexivity.
  + rewrite IHt1, IHt2.
    reflexivity.
}
Qed.

Lemma bexp'_denote_Interp_Equiv: forall J1 J2 b,
  Interp_Equiv J1 J2 ->
  (bexp'_denote J1 b <-> bexp'_denote J2 b).
Proof.
  intros.
  induction b; simpl.
  + tauto.
  + tauto.
  + pose proof aexp'_denote_Interp_Equiv _ _ a1 H.
    pose proof aexp'_denote_Interp_Equiv _ _ a2 H.
    rewrite H0, H1.
    tauto.
  + pose proof aexp'_denote_Interp_Equiv _ _ a1 H.
    pose proof aexp'_denote_Interp_Equiv _ _ a2 H.
    rewrite H0, H1.
    tauto.
  + tauto.
  + tauto.
Qed.

Lemma satisfies_Interp_Equiv: forall J1 J2 P,
  Interp_Equiv J1 J2 ->
  (J1 |== P <-> J2 |== P).
Proof.
  intros.
  revert J1 J2 H; induction P; simpl; intros.
  + pose proof term_denote_Interp_Equiv _ _ t1 H.
    pose proof term_denote_Interp_Equiv _ _ t2 H.
    rewrite H0, H1.
    tauto.
  + pose proof term_denote_Interp_Equiv _ _ t1 H.
    pose proof term_denote_Interp_Equiv _ _ t2 H.
    rewrite H0, H1.
    tauto.
  + pose proof term_denote_Interp_Equiv _ _ t1 H.
    pose proof term_denote_Interp_Equiv _ _ t2 H.
    rewrite H0, H1.
    tauto.
  + apply bexp'_denote_Interp_Equiv.
    exact H.
  + specialize (IHP1 _ _ H).
    specialize (IHP2 _ _ H).
    tauto.
  + specialize (IHP1 _ _ H).
    specialize (IHP2 _ _ H).
    tauto.
  + specialize (IHP1 _ _ H).
    specialize (IHP2 _ _ H).
    tauto.
  + specialize (IHP _ _ H).
    tauto.
  + apply Morphisms_Prop.ex_iff_morphism.
    hnf; intros v.
    apply IHP.
    apply Interp_Equiv_Interp_Lupdate.
    exact H.
  + apply Morphisms_Prop.all_iff_morphism.
    hnf; intros v.
    apply IHP.
    apply Interp_Equiv_Interp_Lupdate.
    exact H.
Qed.

Lemma multi_astep_ind_1n: forall st (P: aexp -> aexp -> Prop),
  (forall a, P a a) ->
  (forall a1 a2 a3 (IH: P a2 a3),
    astep st a1 a2 ->
    multi_astep st a2 a3 ->
    P a1 a3) ->
  (forall a1 a2,
    multi_astep st a1 a2 ->
    P a1 a2).
Proof.
  intros.
  unfold multi_astep in H1.
  apply Operators_Properties.clos_rt_rt1n_iff in H1.
  induction H1.
  + apply H.
  + apply Operators_Properties.clos_rt_rt1n_iff in H2.
    unfold multi_astep in H0.
    pose proof H0 _ y _ IHclos_refl_trans_1n H1 H2.
    exact H3.
Qed.

Lemma multi_bstep_ind_1n: forall st (P: bexp -> bexp -> Prop),
  (forall b, P b b) ->
  (forall b1 b2 b3 (IH: P b2 b3),
    bstep st b1 b2 ->
    multi_bstep st b2 b3 ->
    P b1 b3) ->
  (forall b1 b2,
    multi_bstep st b1 b2 ->
    P b1 b2).
Proof.
  intros.
  unfold multi_bstep in H1.
  apply Operators_Properties.clos_rt_rt1n_iff in H1.
  induction H1.
  + apply H.
  + apply Operators_Properties.clos_rt_rt1n_iff in H2.
    unfold multi_bstep in H0.
    pose proof H0 _ y _ IHclos_refl_trans_1n H1 H2.
    exact H3.
Qed.

Lemma multi_cstep_ind_1n: forall (P: com' -> state -> com' -> state -> Prop),
  (forall c st, P c st c st) ->
  (forall c1 c2 c3 st1 st2 st3 (IH: P c2 st2 c3 st3),
    cstep (c1, st1) (c2, st2) ->
    multi_cstep (c2, st2) (c3, st3) ->
    P c1 st1 c3 st3) ->
  (forall c1 c2 st1 st2,
    multi_cstep (c1, st1) (c2, st2) ->
    P c1 st1 c2 st2).
    Proof.
    intros.
  unfold multi_cstep in H1.
  apply Operators_Properties.clos_rt_rt1n_iff in H1.
  remember  (c1, st1)as cst1 eqn:HH1.
  remember ( c2, st2)as cst2 eqn:HH2.
  revert  c1 c2  st1 st2 HH1 HH2; induction H1; intros; subst.
  + injection HH2 as ? ?.
    subst.
    apply H.
  + apply Operators_Properties.clos_rt_rt1n_iff in H2.
    destruct y as [c0 st0].
    unfold multi_cstep in H0.
    assert ((c0, st0) = (c0, st0)). { reflexivity. }
    assert ((c2, st2) = (c2, st2)). { reflexivity. }
    pose proof IHclos_refl_trans_1n _ _ _ _ H3 H4.
    pose proof H0 _ c0 _ _ st0 _ H5 H1 H2.
    exact H6.
Qed.

Ltac induction_1n H :=
  match type of H with
  | multi_astep ?st ?a1 ?a2 =>
      match goal with
      | |- ?P =>
           let Q := eval pattern a1, a2 in P in
           match Q with
           | ?R a1 a2 =>
             revert a1 a2 H;
             refine (multi_astep_ind_1n st R _ _);
             [intros a1 | intros a1 ?a1 a2 ? ? ?]
           end
      end
  | multi_bstep ?st ?b1 ?b2 =>
      match goal with
      | |- ?P =>
           let Q := eval pattern b1, b2 in P in
           match Q with
           | ?R b1 b2 =>
             revert b1 b2 H;
             refine (multi_bstep_ind_1n st R _ _);
             [intros b1 | intros b1 ?b1 b2 ? ? ?]
           end
      end
  | multi_cstep (?c1, ?st1) (?c2, ?st2) =>
      match goal with
      | |- ?P =>
           let Q := eval pattern c1, st1, c2, st2 in P in
           match Q with
           | ?R c1 st1 c2 st2 =>
             revert c1 c2 st1 st2 H;
             refine (multi_cstep_ind_1n R _ _);
             [intros c1 st1 | intros c1 ?c1 c2 st1 ?st1 st2 ? ? ?]
           end
      end 
  end.
End Assertion_D.

(** PAN addition**)

(* Mon May 6 16:26:02 UTC 2019 *)
