Require Import PL.Imp.
Require Import PL.Assertion_Sub_Spec_Lemma.
Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Relations.Relation_Definitions.

Module Hoare_Soundness.

Import Assertion_D.
Import Assertion_Sub_Spec_Lemma_Module.


Definition hoare_sound (T: FirstOrderLogic): Prop :=
  forall P c Q1 Q2 Q3,
   |-- {{P}} c {{Q1}} {{Q2}} {{Q3}} -> |== {{P}} c {{Q1}} {{Q2}} {{Q3}}.

Definition FOL_valid {T: FirstOrderLogic} (P: Assertion): Prop :=
  forall J: Interp, J |== P.

Definition FOL_sound (T: FirstOrderLogic): Prop :=
  forall P: Assertion, FOL_provable P -> FOL_valid P.

Lemma hoare_seq_sound : forall (P Q R RB RC: Assertion) (c1 c2: com),
  |== {{P}} c1 {{Q}}{{RB}}{{RC}} ->
  |== {{Q}} c2 {{R}}{{RB}}{{RC}} ->
  |== {{P}} c1;; c2 {{R}}{{RB}}{{RC}}.
Proof.
  unfold valid.
  intros.
  split; intros.
  2:split; intros.
  + simpl in H2.
    unfold seq_sem in H2.
    destruct H2.
    - destruct H2 as [st5 [? ?]].
      specialize (H La st1 st5 st3 st4 H1).
      destruct H as [EKN1 [EKB1 EKC1]].
      specialize (EKN1 H2).
      specialize (H0 La st5 st2 st3 st4 EKN1).
      destruct H0 as [EKN2 [EKB2 EKC2]].
      specialize (EKN2 H3).
      exact EKN2.
    - destruct H2.
      tauto.
  + simpl in H2.
    unfold seq_sem in H2.
    destruct H2.
    - destruct H2 as [st5 [? ?]].
      specialize (H La st1 st5 st3 st4 H1).
      destruct H as [EKN1 [EKB1 EKC1]].
      specialize (EKN1 H2).
      specialize (H0 La st5 st2 st3 st4 EKN1).
      destruct H0 as [EKN2 [EKB2 EKC2]].
      specialize (EKB2 H3).
      exact EKB2.
    - destruct H2.
      clear H3 H0.
      specialize (H La st1 st2 st3 st4 H1).
      destruct H as [EKN1 [EKB1 EKC1]].
      specialize (EKB1 H2).
      exact EKB1.
  + simpl in H2.
    unfold seq_sem in H2.
    destruct H2.
    - destruct H2 as [st5 [? ?]].
      specialize (H La st1 st5 st3 st4 H1).
      destruct H as [EKN1 [EKB1 EKC1]].
      specialize (EKN1 H2).
      specialize (H0 La st5 st2 st3 st4 EKN1).
      destruct H0 as [EKN2 [EKB2 EKC2]].
      specialize (EKC2 H3).
      exact EKC2.
    - destruct H2.
      clear H3 H0.
      specialize (H La st1 st2 st3 st4 H1).
      destruct H as [EKN1 [EKB1 EKC1]].
      specialize (EKC1 H2).
      exact EKC1.
Qed.

Lemma hoare_skip_sound : forall P,
  |== {{P}} Skip {{P}}{{{[BFalse]}}}{{{[BFalse]}}}.
Proof.
  unfold valid.
  intros.
  split; intros.
  2: split; intros.
  + simpl in H0.
    unfold skip_sem in H0.
    destruct H0.
    rewrite <- H0.
    exact H.
  + simpl in H0.
    unfold skip_sem in H0.
    destruct H0.
    discriminate.
  + simpl in H0.
    unfold skip_sem in H0.
    destruct H0.
    discriminate.
Qed.

Lemma hoare_if_sound : forall P Q QB QC (b: bexp) c1 c2,
  |== {{P AND {[b]}}} c1 {{Q}}{{QB}}{{QC}} ->
  |== {{P AND NOT {[b]}}} c2 {{Q}}{{QB}}{{QC}} ->
  |== {{P}} If b Then c1 Else c2 EndIf {{Q}}{{QB}}{{QC}}.
Proof.
  unfold valid.
  intros.
  split; intros.
  2: split; intros.
  + simpl in H2.
    unfold if_sem in H2.
    destruct H2 as [[? ?] | [? ?]].
    - clear H0.
      assert ((st1, La) |== P AND {[b]}).
      {
        simpl.
        pose proof beval_bexp'_denote st1 La b.
        tauto.
      }
      specialize (H La st1 st2 st3 st4 H0).
      destruct H.
      apply H.
      exact H2.
    - clear H.
      assert ((st1, La) |== P AND NOT {[b]}).
      {
        simpl.
        pose proof beval_bexp'_denote st1 La b.
        tauto.
      }
      specialize (H0 La st1 st2 st3 st4 H).
      destruct H0.
      apply H0.
      exact H2.
  + simpl in H2.
    unfold if_sem in H2.
    destruct H2 as [[? ?] | [? ?]].
    - clear H0.
      assert ((st1, La) |== P AND {[b]}).
      {
        simpl.
        pose proof beval_bexp'_denote st1 La b.
        tauto.
      }
      specialize (H La st1 st2 st3 st4 H0).
      destruct H.
      destruct H4.
      apply H4.
      exact H2.
    - clear H.
      assert ((st1, La) |== P AND NOT {[b]}).
      {
        simpl.
        pose proof beval_bexp'_denote st1 La b.
        tauto.
      }
      specialize (H0 La st1 st2 st3 st4 H).
      destruct H0.
      destruct H4.
      apply H4.
      exact H2.
  + simpl in H2.
    unfold if_sem in H2.
    destruct H2 as [[? ?] | [? ?]].
    - clear H0.
      assert ((st1, La) |== P AND {[b]}).
      {
        simpl.
        pose proof beval_bexp'_denote st1 La b.
        tauto.
      }
      specialize (H La st1 st2 st3 st4 H0).
      destruct H.
      destruct H4.
      apply H5.
      exact H2.
    - clear H.
      assert ((st1, La) |== P AND NOT {[b]}).
      {
        simpl.
        pose proof beval_bexp'_denote st1 La b.
        tauto.
      }
      specialize (H0 La st1 st2 st3 st4 H).
      destruct H0.
      destruct H4.
      apply H5.
      exact H2.
Qed.

Lemma hoare_while_sound : forall I P (b: bexp) c,
  |== {{I AND {[b]}}} c {{I}}{{P}}{{I}} ->
  |== {{I}} While b Do c EndWhile {{P OR (I AND NOT {[b]})}}{{{[BFalse]}}}{{{[BFalse]}}}.
Proof.
  unfold valid.
  intros.
  split; intros.
  2: split; intros.
  + simpl in H1.
    unfold loop_sem in H1.
    destruct H1 as [n []].
    clear H2.
    revert st1 H0 H1; induction n; intros.
    - simpl in H1.
      destruct H1.
      subst st2.
      simpl.
      pose proof beval_bexp'_denote st1 La b.
      tauto.
    - simpl in H1.
      destruct H1.
      destruct H1.
      * destruct H1.
        destruct H1.
        apply IHn with x.
        ++ assert ((st1, La) |== I AND {[b]}).
           {
             simpl.
             pose proof beval_bexp'_denote st1 La b.
             tauto.
           }
           specialize (H La st1 x st3 st4 H4).
           destruct H.
           apply H.
           exact H1.
        ++ exact H3.
      * destruct H1.
        ++ simpl.
           (* pose proof beval_bexp'_denote st1 La b. *)
           left.
           assert ((st1, La) |== I AND {[b]}).
           {
             simpl.
             pose proof beval_bexp'_denote st1 La b.
             tauto.
           }
           specialize (H La st1 st2 st2 st4 H3).
           destruct H.
           destruct H4.
           apply H4.
           exact H1.
        ++ destruct H1 as [? []].
           apply IHn with x.
           -- assert ((st1, La) |== I AND {[b]}).
              {
                simpl.
                pose proof beval_bexp'_denote st1 La b.
                tauto.
              }
              specialize (H La st1 st2 st3 x H4).
              destruct H.
              destruct H5.
              apply H6.
              exact H1.
           -- exact H3.
  + simpl in H1.
    unfold loop_sem in H1.
    destruct H1 as [? []].
    discriminate.
  + simpl in H1.
    unfold loop_sem in H1.
    destruct H1 as [? []].
    discriminate.
Qed.

Lemma hoare_asgn_bwd_sound : forall P (X: var) (E: aexp),
  |== {{P [X |-> E] }} CAss X E {{P}}{{{[BFalse]}}}{{{[BFalse]}}}.
Proof.
  unfold valid.
  intros.
  split; intros.
  2:split; intros.
  - simpl in H0.
    unfold asgn_sem in H0.
    destruct H0 as [? [ ]].
    simpl in H0.
    clear H0.
    pose proof aeval_aexp'_denote st1 La E.
    rewrite H0 in H1.
    pose proof Assertion_sub_spec st1 st2 _ P _ _ H1 H2.
    rewrite <- H3.
    exact H.
  - simpl in H0.
    unfold asgn_sem in H0.
    destruct H0 as [? [ ]].
    discriminate.
  - simpl in H0.
    unfold asgn_sem in H0.
    destruct H0 as [? [ ]].
    discriminate.
Qed.

Lemma hoare_consequence_sound : forall (T: FirstOrderLogic) (P P' Q Q' QB QB' QC QC': Assertion) c,
  FOL_sound T ->
  P |-- P' ->
  |== {{P'}} c {{Q'}}{{QB'}}{{QC'}} ->
  Q' |-- Q ->
  QB' |-- QB ->
  QC' |-- QC ->
  |== {{P}} c {{Q}}{{QB}}{{QC}}.
Proof.
  intros.
  unfold FOL_sound in H.
  unfold derives in H0, H2, H3, H4.
  apply H in H0.
  apply H in H2.
  apply H in H3.
  apply H in H4.
  unfold FOL_valid in H0, H2, H3, H4.
  simpl in H0, H2, H3, H4.
  unfold valid in H1.
  unfold valid.
  intros.
  assert ((st1, La) |== P').
  {
    specialize (H0 (st1, La)).
    tauto.
  }
  pose proof H1 La st1 st2 st3 st4 H6.
  destruct H7.
  destruct H8.
  split; intros.
  2:split; intros.
  + specialize (H7 H10).
    specialize (H2 (st2, La)).
    tauto.
  + specialize (H8 H10).
    specialize (H3 (st3, La)).
    tauto.
  + specialize (H9 H10).
    specialize (H4 (st4, La)).
    tauto.
Qed.

Lemma hoare_break_sound : forall P,
  |== {{P}} CBreak {{{[BFalse]}}}{{P}}{{{[BFalse]}}}.
Proof.
  unfold valid.
  intros.
  split; intros.
  2:split; intros.
  + simpl in H0.
    unfold break_sem in H0.
    destruct H0.
    discriminate.
  + simpl in H0.
    unfold break_sem in H0.
    destruct H0.
    rewrite <- H0.
    exact H.
  + simpl in H0.
    unfold break_sem in H0.
    destruct H0.
    discriminate.
Qed.

Lemma hoare_cont_sound : forall P,
  |== {{P}} CCont {{{[BFalse]}}}{{{[BFalse]}}}{{P}}.
Proof.
  unfold valid.
  intros.
  split; intros.
  2:split; intros.
  + simpl in H0.
    unfold cont_sem in H0.
    destruct H0.
    discriminate.
  + simpl in H0.
    unfold cont_sem in H0.
    destruct H0.
    discriminate.
  + simpl in H0.
    unfold cont_sem in H0.
    destruct H0.
    rewrite <- H0.
    exact H.
Qed.

Lemma hoare_soundness:forall (T: FirstOrderLogic) (TS: FOL_sound T),
  hoare_sound T.
Proof.
  intros.
  unfold hoare_sound.
  intros.
  remember ({{P}} c {{Q1}}{{Q2}}{{Q3}}) as Tr.
  clear P c Q1 Q2 Q3 HeqTr.
  induction H.
  + eapply hoare_seq_sound.
    - exact IHprovable1.
    - exact IHprovable2.
  + apply hoare_skip_sound.
  + eapply hoare_if_sound.
    - exact IHprovable1.
    - exact IHprovable2.
  + eapply hoare_while_sound.
    exact IHprovable.
  + apply hoare_asgn_bwd_sound.
  + eapply hoare_consequence_sound.
    exact TS.
    exact H.
    exact IHprovable.
    exact H1.
    exact H2.
    exact H3.
  + apply hoare_break_sound.
  + apply hoare_cont_sound.
Qed.

End Hoare_Soundness.