Require Import PL.Imp.
Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Relations.Relation_Definitions.
Import Assertion_D.

Arguments clos_refl_trans {A} _ _ _.
Arguments clos_refl_trans_1n {A} _ _ _.
Arguments clos_refl_trans_n1 {A} _ _ _.
Lemma multi_astep_refl: forall st a,
  multi_astep st a a.
Proof.
  unfold multi_astep.
  intros.
  apply rt_refl.
Qed.

Lemma multi_astep_step: forall {st a1 a2},
  astep st a1 a2 ->
  multi_astep st a1 a2.
Proof.
  unfold multi_astep.
  intros.
  apply rt_step.
  exact H.
Qed.

Lemma multi_astep_trans: forall {st a1 a2 a3},
  multi_astep st a1 a2 ->
  multi_astep st a2 a3 ->
  multi_astep st a1 a3.
Proof.
  unfold multi_astep.
  intros.
  eapply rt_trans.
  + exact H.
  + exact H0.
Qed.

Lemma multi_astep_trans_n1: forall {st a1 a2 a3},
  multi_astep st a1 a2 ->
  astep st a2 a3 ->
  multi_astep st a1 a3.
Proof.
  unfold multi_astep.
  intros.
  eapply rt_trans.
  + exact H.
  + apply rt_step.
    exact H0.
Qed.

Lemma multi_astep_trans_1n: forall {st a1 a2 a3},
  astep st a1 a2 ->
  multi_astep st a2 a3 ->
  multi_astep st a1 a3.
Proof.
  unfold multi_astep.
  intros.
  eapply rt_trans.
  + apply rt_step.
    exact H.
  + exact H0.
Qed.

Lemma multi_bstep_refl: forall st b,
  multi_bstep st b b.
Proof.
  unfold multi_bstep.
  intros.
  apply rt_refl.
Qed.

Lemma multi_bstep_step: forall {st b1 b2},
  bstep st b1 b2 ->
  multi_bstep st b1 b2.
Proof.
  unfold multi_bstep.
  intros.
  apply rt_step.
  exact H.
Qed.

Lemma multi_bstep_trans: forall {st b1 b2 b3},
  multi_bstep st b1 b2 ->
  multi_bstep st b2 b3 ->
  multi_bstep st b1 b3.
Proof.
  unfold multi_bstep.
  intros.
  eapply rt_trans.
  + exact H.
  + exact H0.
Qed.

Lemma multi_bstep_trans_n1: forall {st b1 b2 b3},
  multi_bstep st b1 b2 ->
  bstep st b2 b3 ->
  multi_bstep st b1 b3.
Proof.
  unfold multi_bstep.
  intros.
  eapply rt_trans.
  + exact H.
  + apply rt_step.
    exact H0.
Qed.

Lemma multi_bstep_trans_1n: forall {st b1 b2 b3},
  bstep st b1 b2 ->
  multi_bstep st b2 b3 ->
  multi_bstep st b1 b3.
Proof.
  unfold multi_bstep.
  intros.
  eapply rt_trans.
  + apply rt_step.
    exact H.
  + exact H0.
Qed.

Lemma multi_cstep_refl: forall st c,
  multi_cstep (c, st) (c, st).
Proof.
  unfold multi_cstep.
  intros.
  apply rt_refl.
Qed.

Lemma multi_cstep_step: forall {st1 st2 c1 c2},
  cstep (c1, st1) (c2, st2) ->
  multi_cstep (c1, st1) (c2, st2).
Proof.
  unfold multi_cstep.
  intros.
  apply rt_step.
  exact H.
Qed.

Lemma multi_cstep_trans: forall {st1 st2 st3 c1 c2 c3},
  multi_cstep (c1, st1) (c2, st2) ->
  multi_cstep (c2, st2) (c3, st3) ->
  multi_cstep (c1, st1) (c3, st3).
Proof.
  unfold multi_cstep.
  intros.
  eapply rt_trans.
  + exact H.
  + exact H0.
Qed.

Lemma multi_cstep_trans_n1: forall {st1 st2 st3 c1 c2 c3},
  multi_cstep (c1, st1) (c2, st2) ->
  cstep (c2, st2) (c3, st3) ->
  multi_cstep (c1, st1) (c3, st3).
Proof.
  unfold multi_cstep.
  intros.
  eapply rt_trans.
  + exact H.
  + apply rt_step.
    exact H0.
Qed.

Lemma multi_cstep_trans_1n: forall {st1 st2 st3 c1 c2 c3},
  cstep (c1, st1) (c2, st2) ->
  multi_cstep (c2, st2) (c3, st3) ->
  multi_cstep (c1, st1) (c3, st3).
Proof.
  unfold multi_cstep.
  intros.
  eapply rt_trans.
  + apply rt_step.
    exact H.
  + exact H0.
Qed.

(* ################################################################# *)
(** * Auxiliary Lemmas For Induction *)

Lemma multi_astep_ind_n1: forall st (P: aexp -> aexp -> Prop),
  (forall a, P a a) ->
  (forall a1 a2 a3 (IH: P a1 a2),
    multi_astep st a1 a2 ->
    astep st a2 a3 ->
    P a1 a3) ->
  (forall a1 a2,
    multi_astep st a1 a2 ->
    P a1 a2).
Proof.
  intros.
  unfold multi_astep in H1.
  apply Operators_Properties.clos_rt_rtn1_iff in H1.
  induction H1.
  + apply H.
  + apply Operators_Properties.clos_rt_rtn1_iff in H2.
    unfold multi_astep in H0.
    pose proof H0 _ y _ IHclos_refl_trans_n1 H2 H1.
    exact H3.
Qed.

Lemma multi_bstep_ind_n1: forall st (P: bexp -> bexp -> Prop),
  (forall b, P b b) ->
  (forall b1 b2 b3 (IH: P b1 b2),
    multi_bstep st b1 b2 ->
    bstep st b2 b3 ->
    P b1 b3) ->
  (forall b1 b2,
    multi_bstep st b1 b2 ->
    P b1 b2).
Proof.
  intros.
  unfold multi_bstep in H1.
  apply Operators_Properties.clos_rt_rtn1_iff in H1.
  induction H1.
  + apply H.
  + apply Operators_Properties.clos_rt_rtn1_iff in H2.
    unfold multi_bstep in H0.
    pose proof H0 _ y _ IHclos_refl_trans_n1 H2 H1.
    exact H3.
Qed.

Lemma multi_cstep_ind_n1: forall (P: com' -> state -> com' -> state -> Prop),
  (forall c st, P c st c st) ->
  (forall c1 c2 c3 st1 st2 st3 (IH: P c1 st1 c2 st2),
    multi_cstep (c1, st1) (c2, st2) ->
    cstep (c2, st2) (c3, st3) ->
    P c1 st1 c3 st3) ->
  (forall c1 c2 st1 st2,
    multi_cstep (c1, st1) (c2, st2) ->
    P c1 st1 c2 st2).
Proof.
  intros.
  unfold multi_cstep in H1.
  apply Operators_Properties.clos_rt_rtn1_iff in H1.
  remember (c1, st1) as cst1 eqn:HH1.
  remember (c2, st2) as cst2 eqn:HH2.
  revert c1 c2 st1 st2 HH1 HH2; induction H1; intros; subst.
  + injection HH2 as ? ?.
    subst.
    apply H.
  + apply Operators_Properties.clos_rt_rtn1_iff in H2.
    destruct y as [c0 st0].
    unfold multi_cstep in H0.
    assert ((c1, st1) = (c1, st1)). { reflexivity. }
    assert ((c0, st0) = (c0, st0)). { reflexivity. }
    pose proof IHclos_refl_trans_n1 _ _ _ _ H3 H4.
    pose proof H0 _ c0 _ _ st0 _ H5 H2 H1.
    exact H6.
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
  remember (c1, st1) as cst1 eqn:HH1.
  remember (c2, st2) as cst2 eqn:HH2.
  revert c1 c2 st1 st2 HH1 HH2; induction H1; intros; subst.
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

Ltac induction_n1 H :=
  match type of H with
  | multi_astep ?st ?a1 ?a2 =>
      match goal with
      | |- ?P =>
           let Q := eval pattern a1, a2 in P in
           match Q with
           | ?R a1 a2 =>
             revert a1 a2 H;
             refine (multi_astep_ind_n1 st R _ _);
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
             refine (multi_bstep_ind_n1 st R _ _);
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
             refine (multi_cstep_ind_n1 R _ _);
             [intros c1 st1 | intros c1 ?c1 c2 st1 ?st1 st2 ? ? ?]
           end
      end
  end.

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

(* ################################################################# *)
(** * Congruence Theorems of Multi-step Relations *)

Theorem multi_congr_APlus1: forall st a1 a1' a2,
  multi_astep st a1 a1' ->
  multi_astep st (a1 + a2) (a1' + a2).
Proof.
  intros.
  induction_n1 H.
  + apply multi_astep_refl.
  + eapply multi_astep_trans_n1.
    - exact IH.
    - apply AS_Plus1.
      exact H0.
Qed.

Theorem multi_congr_APlus2: forall st a1 a2 a2',
  aexp_halt a1 ->
  multi_astep st a2 a2' ->
  multi_astep st (a1 + a2) (a1 + a2').
Proof.
  intros.
  induction_n1 H0.
  + apply multi_astep_refl.
  + eapply multi_astep_trans_n1.
    - exact IH.
    - apply AS_Plus2.
      * exact H.
      * exact H1.
Qed.

Theorem multi_congr_AMinus1: forall st a1 a1' a2,
  multi_astep st a1 a1' ->
  multi_astep st (a1 - a2) (a1' - a2).
Proof.
  intros.
  induction_n1 H.
  + apply multi_astep_refl.
  + eapply multi_astep_trans_n1.
    - exact IH.
    - apply AS_Minus1.
      exact H0.
Qed.

Theorem multi_congr_AMinus2: forall st a1 a2 a2',
  aexp_halt a1 ->
  multi_astep st a2 a2' ->
  multi_astep st (a1 - a2) (a1 - a2').
Proof.
  intros.
  induction_n1 H0.
  + apply multi_astep_refl.
  + eapply multi_astep_trans_n1.
    - exact IH.
    - apply AS_Minus2.
      * exact H.
      * exact H1.
Qed.

Theorem multi_congr_AMult1: forall st a1 a1' a2,
  multi_astep st a1 a1' ->
  multi_astep st (a1 * a2) (a1' * a2).
Proof.
  intros.
  induction_n1 H.
  + apply multi_astep_refl.
  + eapply multi_astep_trans_n1.
    - exact IH.
    - apply AS_Mult1.
      exact H0.
Qed.

Theorem multi_congr_AMult2: forall st a1 a2 a2',
  aexp_halt a1 ->
  multi_astep st a2 a2' ->
  multi_astep st (a1 * a2) (a1 * a2').
Proof.
  intros.
  induction_n1 H0.
  + apply multi_astep_refl.
  + eapply multi_astep_trans_n1.
    - exact IH.
    - apply AS_Mult2.
      * exact H.
      * exact H1.
Qed.

Theorem multi_congr_BEq1: forall st a1 a1' a2,
  multi_astep st a1 a1' ->
  multi_bstep st (a1 == a2) (a1' == a2).
Proof.
  intros.
  induction_n1 H.
  + apply multi_bstep_refl.
  + eapply multi_bstep_trans_n1.
    - exact IH.
    - apply BS_Eq1.
      exact H0.
Qed.

Theorem multi_congr_BEq2: forall st a1 a2 a2',
  aexp_halt a1 ->
  multi_astep st a2 a2' ->
  multi_bstep st (a1 == a2) (a1 == a2').
Proof.
  intros.
  induction_n1 H0.
  + apply multi_bstep_refl.
  + eapply multi_bstep_trans_n1.
    - exact IH.
    - apply BS_Eq2.
      * exact H.
      * exact H1.
Qed.

Theorem multi_congr_BLe1: forall st a1 a1' a2,
  multi_astep st a1 a1' ->
  multi_bstep st (a1 <= a2) (a1' <= a2).
Proof.
  intros.
  induction_n1 H.
  + apply multi_bstep_refl.
  + eapply multi_bstep_trans_n1.
    - exact IH.
    - apply BS_Le1.
      exact H0.
Qed.

Theorem multi_congr_BLe2: forall st a1 a2 a2',
  aexp_halt a1 ->
  multi_astep st a2 a2' ->
  multi_bstep st (a1 <= a2) (a1 <= a2').
Proof.
  intros.
  induction_n1 H0.
  + apply multi_bstep_refl.
  + eapply multi_bstep_trans_n1.
    - exact IH.
    - apply BS_Le2.
      * exact H.
      * exact H1.
Qed.

Theorem multi_congr_BNot: forall st b b',
  multi_bstep st b b' ->
  multi_bstep st (BNot b) (BNot b').
Proof.
  intros.
  induction_n1 H.
  + apply multi_bstep_refl.
  + eapply multi_bstep_trans_n1.
    - apply IH.
    - apply BS_NotStep.
      exact H0.
Qed.

Theorem multi_congr_BAnd: forall st b1 b1' b2,
  multi_bstep st b1 b1' ->
  multi_bstep st (BAnd b1 b2) (BAnd b1' b2).
Proof.
  intros.
  induction_n1 H.
  + apply multi_bstep_refl.
  + eapply multi_bstep_trans_n1.
    - apply IH.
    - apply BS_AndStep.
      exact H0.
Qed.

Theorem multi_congr_CAss: forall st s X a a',
  multi_astep st a a' ->
  multi_cstep(CNormal s (CAss X a), st) (CNormal s (CAss X a'), st).
Proof.
  intros.
  induction_n1 H.
  + apply multi_cstep_refl.
  + eapply multi_cstep_trans_n1.
    - exact IH.
    - apply CS_AssStep.
      exact H0.
Qed.

Theorem semantic_equiv_aexp1: forall st a n,
  aeval a st = n -> multi_astep st a (ANum n).
Proof.
  intros.
  revert n H; induction a; intros; simpl in H.
  + simpl in H.
    rewrite H.
    apply multi_astep_refl.
  + rewrite <- H.
    apply multi_astep_step.
    apply AS_Id.
  + assert (aeval a1 st = aeval a1 st).
    { reflexivity. }
    pose proof IHa1 _ H0.
    pose proof multi_congr_APlus1 _ _ _ a2 H1 as IH1.
    clear IHa1 H0 H1.
    assert (aeval a2 st = aeval a2 st).
    { reflexivity. }
    pose proof IHa2 _ H0.
    pose proof AH_num (aeval a1 st).
    pose proof multi_congr_APlus2 _ _ _ _ H2 H1 as IH2.
    clear IHa2 H0 H1 H2.
    pose proof AS_Plus st (aeval a1 st) (aeval a2 st).
    rewrite H in H0.
    pose proof multi_astep_trans IH1 IH2.
    pose proof multi_astep_trans_n1 H1 H0.
    exact H2.
  + assert (aeval a1 st = aeval a1 st).
    { reflexivity. }
    pose proof IHa1 _ H0.
    pose proof multi_congr_AMinus1 _ _ _ a2 H1 as IH1.
    clear IHa1 H0 H1.
    assert (aeval a2 st = aeval a2 st).
    { reflexivity. }
    pose proof IHa2 _ H0.
    pose proof AH_num (aeval a1 st).
    pose proof multi_congr_AMinus2 _ _ _ _ H2 H1 as IH2.
    clear IHa2 H0 H1 H2.
    pose proof AS_Minus st (aeval a1 st) (aeval a2 st).
    rewrite H in H0.
    pose proof multi_astep_trans IH1 IH2.
    pose proof multi_astep_trans_n1 H1 H0.
    exact H2.
  + assert (aeval a1 st = aeval a1 st).
    { reflexivity. }
    pose proof IHa1 _ H0.
    pose proof multi_congr_AMult1 _ _ _ a2 H1 as IH1.
    clear IHa1 H0 H1.
    assert (aeval a2 st = aeval a2 st).
    { reflexivity. }
    pose proof IHa2 _ H0.
    pose proof AH_num (aeval a1 st).
    pose proof multi_congr_AMult2 _ _ _ _ H2 H1 as IH2.
    clear IHa2 H0 H1 H2.
    pose proof AS_Mult st (aeval a1 st) (aeval a2 st).
    rewrite H in H0.
    pose proof multi_astep_trans IH1 IH2.
    pose proof multi_astep_trans_n1 H1 H0.
    exact H2.
Qed.

Theorem semantic_equiv_bexp1: forall st b,
  (beval b st -> multi_bstep st b BTrue) /\
  (~ beval b st -> multi_bstep st b BFalse).
Proof.
  intros.
  induction b; simpl.
  + split.
    - intros.
      apply multi_bstep_refl.
    - tauto.
  + split.
    - tauto.
    - intros.
      apply multi_bstep_refl.
  + assert (aeval a1 st = aeval a1 st).
    { reflexivity. }
    pose proof semantic_equiv_aexp1 st a1 _ H.
    pose proof multi_congr_BEq1 _ _ _ a2 H0 as IH1.
    clear H H0.
    assert (aeval a2 st = aeval a2 st).
    { reflexivity. }
    pose proof semantic_equiv_aexp1 st a2 _ H.
    pose proof AH_num (aeval a1 st).
    pose proof multi_congr_BEq2 _ _ _ _ H1 H0 as IH2.
    clear H H0 H1.
    
    split; intros.
    - pose proof BS_Eq_True st _ _ H.
      pose proof multi_bstep_trans IH1 IH2.
      pose proof multi_bstep_trans_n1 H1 H0.
      exact H2.
    - pose proof BS_Eq_False st _ _ H.
      pose proof multi_bstep_trans IH1 IH2.
      pose proof multi_bstep_trans_n1 H1 H0.
      exact H2.
  + assert (aeval a1 st = aeval a1 st).
    { reflexivity. }
    pose proof semantic_equiv_aexp1 st a1 _ H.
    pose proof multi_congr_BLe1 _ _ _ a2 H0 as IH1.
    clear H H0.
    assert (aeval a2 st = aeval a2 st).
    { reflexivity. }
    pose proof semantic_equiv_aexp1 st a2 _ H.
    pose proof AH_num (aeval a1 st).
    pose proof multi_congr_BLe2 _ _ _ _ H1 H0 as IH2.
    clear H H0 H1.
    
    split; intros.
    - pose proof BS_Le_True st _ _ H.
      pose proof multi_bstep_trans IH1 IH2.
      pose proof multi_bstep_trans_n1 H1 H0.
      exact H2.
    - assert (aeval a1 st > aeval a2 st). { omega. }
      pose proof BS_Le_False st _ _ H0.
      pose proof multi_bstep_trans IH1 IH2.
      pose proof multi_bstep_trans_n1 H2 H1.
      exact H3.
  + destruct IHb as [IH1 IH2].
    split; intros.
    - specialize (IH2 H).
      pose proof multi_congr_BNot st _ _ IH2.
      pose proof BS_NotFalse st.
      pose proof multi_bstep_trans_n1 H0 H1.
      exact H2.
    - assert (multi_bstep st b BTrue). { tauto. }
      pose proof multi_congr_BNot st _ _ H0.
      pose proof BS_NotTrue st.
      pose proof multi_bstep_trans_n1 H1 H2.
      exact H3.
  + destruct IHb1 as [IHb11 IHb12].
    destruct IHb2 as [IHb21 IHb22].
    pose proof classic (beval b1 st).
    destruct H.
    - specialize (IHb11 H).
      pose proof multi_congr_BAnd _ _ _ b2 IHb11.
      pose proof BS_AndTrue st b2.
      split.
      * intros.
        destruct H2.
        specialize (IHb21 H3).
        pose proof multi_bstep_trans_n1 H0 H1.
        pose proof multi_bstep_trans H4 IHb21.
        exact H5.
      * intros.
        assert (~beval b2 st). { tauto. }
        specialize (IHb22 H3).
        pose proof multi_bstep_trans_n1 H0 H1.
        pose proof multi_bstep_trans H4 IHb22.
        exact H5.
    - split; intros. { tauto. }
      specialize (IHb12 H).
      pose proof multi_congr_BAnd _ _ _ b2 IHb12.
      pose proof BS_AndFalse st b2.
      pose proof multi_bstep_trans_n1 H1 H2.
      exact H3.
Qed.

Theorem multi_congr_CIf: forall st s b b' c1 c2,
  multi_bstep st b b' ->
  multi_cstep
    (CNormal s (CIf b c1 c2), st)
    (CNormal s (CIf b' c1 c2), st).
Proof.
  intros.
  induction_n1 H.
  + apply multi_cstep_refl.
  + eapply multi_cstep_trans_n1.
    - exact IH.
    - apply CS_IfStep.
      exact H0.
Qed.

Theorem multi_CS_WhileStep:forall st s b b' b'' c1 c2, 
      multi_bstep st b' b'' ->
      multi_cstep
        (CLoopCond (cons (b, c1, c2) s) b', st)
        (CLoopCond (cons (b, c1, c2) s) b'', st).
Proof.
  intros.
  induction H.
  + apply rt_step.
    apply CS_WhileStep.
    exact H.
  + apply rt_refl.
  + apply rt_trans with (CLoopCond((b, c1, c2) :: s)%list y,st).
    exact IHclos_refl_trans1.
    exact IHclos_refl_trans2.
Qed.

Theorem multi_CS_WhileFalse : forall st s b c1 c2,
      multi_cstep
        (CLoopCond (cons (b, c1, c2) s) BFalse, st)
        (CNormal s c2, st).
Proof.
  intros.
  induction s.
  apply rt_step.
  apply CS_WhileFalse.
  apply rt_step.
  apply CS_WhileFalse.
Qed.

Theorem multi_CS_WhileTrue : forall st s b c1 c2,
      multi_cstep
        (CLoopCond (cons (b, c1, c2) s) BTrue, st)
        (CNormal (cons (b, c1, c2) s) c1, st).
Proof.
  intros.
  induction s.
  apply rt_step.
  apply CS_WhileTrue.
  apply rt_step.
  apply CS_WhileTrue.
Qed.

Theorem multi_CS_While: forall st s b c c1 c2,
      start_with_loop c b c1 c2 ->
      multi_cstep
        (CNormal s c, st)
        (CLoopCond (cons (b, c1, c2) s) b, st).
Proof.
  intros.
  induction s.
  apply rt_step.
  apply CS_While.
  exact H.
  assert(start_with_loop (CWhile b c) b c CSkip).
  apply SWL_While.
  apply rt_step.
  apply CS_While.
  exact H.
Qed.


Theorem semantic_equiv1:forall c st1 st2 s,
((ceval c st1 EK_Normal st2) -> multi_cstep (CNormal s c ,st1) (CNormal s CSkip ,st2))/\
((ceval c st1 EK_Break st2) -> (exists c':com,multi_cstep (CNormal s c ,st1) (CNormal s c' ,st2)/\ start_with_break c'))/\
((ceval c st1 EK_Cont st2) -> (exists c':com,multi_cstep (CNormal nil c ,st1) (CNormal nil c' ,st2)/\ start_with_cont c')).
Proof.
  intros.
  split.
  induction c.
  + intros.
    destruct H.
    unfold multi_cstep.
    rewrite H.
    apply rt_refl.
  + intros.
    destruct H as [?[? ?]].
    assert (aeval a st1 = aeval a st1).
    { reflexivity. }
    admit.
  + admit.
  + intros.
    pose proof semantic_equiv_bexp1 st1 b.
    destruct H0.
    destruct H as [[? ?] | [? ?]].
    - specialize (H0 H2).
      pose proof IHc1 H.
      clear H H1 H2 IHc1 IHc2.
      pose proof multi_congr_CIf st1 s b BTrue c1 c2.
      pose proof CS_IfTrue st1 s c1 c2.
      pose proof H H0.
      apply rt_trans with (CNormal s (If BTrue Then c1 Else c2 EndIf), st1).
      exact H2.
      apply rt_trans with (CNormal s c1, st1).
      apply rt_step.
      exact H1.
      exact H3.
    - pose proof H1 H2.
      pose proof IHc2 H.
      clear H H0 H2 IHc1 IHc2.
      pose proof multi_congr_CIf st1 s b BFalse c1 c2 H3.
      apply rt_trans with (CNormal s (If BFalse Then c1 Else c2 EndIf), st1).
      exact H.
      pose proof CS_IfFalse st1 s c1 c2.
      apply rt_trans with (CNormal s c2, st1).
      apply rt_step.
      exact H0.
      exact H4.
  + intros.
     simpl in H.
     unfold loop_sem in H.
     destruct H as [n [? ?]].
     induction n.
    - unfold iter_loop_body in H.
      destruct H.
      pose proof semantic_equiv_bexp1 st1 b.
      destruct H2.
      pose proof H3 H1.
      clear H1 H0 H2 H3.
      subst st2.
      pose proof multi_CS_WhileStep st1 s b b BFalse c Skip H4.
      pose proof multi_CS_WhileFalse st1 s b c Skip.
      assert(multi_cstep (CLoopCond ((b, c, Skip%imp) :: s)%list b,
        st1)(CNormal s Skip, st1)).
      apply rt_trans with (CLoopCond((b, c, Skip%imp) :: s)%list BFalse, st1) .
      exact H.
      exact H0.
      clear H4 H H0.
      apply rt_trans with (CLoopCond ((b, c, Skip%imp) :: s)%list b,st1).
      apply multi_CS_While.
      apply SWL_While.
      exact H1.
    - simpl in H.
      admit.
  + intros.
    destruct H.
    rewrite H.
    discriminate.
  + intros.
    destruct H.
    discriminate.
  + split.
    - intros.
      induction c.
      * destruct H.
        rewrite H.
        discriminate.
      * destruct H as [? [? ?]].
        discriminate.
      * admit.
      * destruct H.
        destruct H.
        pose proof IHc1 H.
        destruct H1.
        destruct H1.
        pose proof semantic_equiv_bexp1 st1 b.
        destruct H3.
        pose proof H3 H0.
        pose proof multi_congr_CIf st1 s b BTrue c1 c2 H5.
        pose proof CS_IfTrue st1 s c1 c2.
        clear H H0 IHc1 IHc2 H3 H4 H5.
        exists x.
        split.
        apply rt_trans with (CNormal s (If BTrue Then c1 Else c2 EndIf),st1).
        exact H6.
        apply rt_trans with (CNormal s c1, st1).
        apply rt_step.
        exact H7.
        exact H1.
        exact H2.
        destruct H.
        pose proof IHc2 H.
        pose proof semantic_equiv_bexp1 st1 b.
        destruct H2.
        pose proof H3 H0.
        pose proof multi_congr_CIf st1 s b BFalse c1 c2 H4.
        pose proof CS_IfFalse st1 s c1 c2.
        clear H H0 IHc1 IHc2 H2 H3 H4.
        destruct H1.
        destruct H.
        exists x.
        split.
        apply rt_trans with (CNormal s (If BFalse Then c1 Else c2 EndIf), st1).
        exact H5.
        apply rt_trans with (CNormal s c2, st1).
        apply rt_step.
        exact H6.
        exact H.
        exact H0.
      * simpl in H.
        unfold loop_sem in H.
        destruct H as [n [? ?]].
        discriminate.
      * destruct H.
        rewrite H.
        exists CBreak.
        split.
        apply rt_refl.
        apply SWB_Break.
      * destruct H.
        discriminate.
    - intros.
      induction c.
      * destruct H.
        rewrite H.
        discriminate.
      * destruct H as [? [? ?]].
        discriminate.
      * admit.
      * destruct H.
        destruct H.
        pose proof IHc1 H.
        destruct H1.
        destruct H1.
        pose proof semantic_equiv_bexp1 st1 b.
        destruct H3.
        pose proof H3 H0.
        pose proof multi_congr_CIf st1 nil b BTrue c1 c2 H5.
        pose proof CS_IfTrue st1 nil c1 c2.
        clear H H0 IHc1 IHc2 H3 H4 H5.
        exists x.
        split.
        apply rt_trans with (CNormal nil (If BTrue Then c1 Else c2 EndIf),st1).
        exact H6.
        apply rt_trans with (CNormal nil c1, st1).
        apply rt_step.
        exact H7.
        exact H1.
        exact H2.
        destruct H.
        pose proof IHc2 H.
        pose proof semantic_equiv_bexp1 st1 b.
        destruct H2.
        pose proof H3 H0.
        pose proof multi_congr_CIf st1 nil b BFalse c1 c2 H4.
        pose proof CS_IfFalse st1 nil c1 c2.
        clear H H0 IHc1 IHc2 H2 H3 H4.
        destruct H1.
        destruct H.
        exists x.
        split.
        apply rt_trans with (CNormal nil (If BFalse Then c1 Else c2 EndIf), st1).
        exact H5.
        apply rt_trans with (CNormal nil c2, st1).
        apply rt_step.
        exact H6.
        exact H.
        exact H0.
      * simpl in H.
        unfold loop_sem in H.
        destruct H as [n [? ?]].
        discriminate.
      * destruct H.
        discriminate.
      * destruct H.
        exists CCont.
        split.
        rewrite H.
        apply rt_refl.
        apply SWC_Cont.
  Admitted.






