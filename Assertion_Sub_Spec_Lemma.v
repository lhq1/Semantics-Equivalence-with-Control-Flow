Require Import PL.Imp.
Require Import PL.Lemmas_of_Assertion_Sub_Spec_Lemma.
Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Relations.Relation_Definitions.

Module Assertion_Sub_Spec_Lemma_Module.

Import Assertion_D.
Import Lemmas_of_Assertion_Sub_Spec_Lemma_Module.

Lemma Assertion_sub_spec_1: forall st La (P: Assertion) (E: aexp'),
  (st, La) |== P <-> (st, La) |== (rename_all E P).
Proof.
  intros.
  revert La.
  induction P; simpl.
  + reflexivity.
  + reflexivity.
  + reflexivity.
  + reflexivity.
  + intros.
    rewrite IHP1.
    rewrite IHP2.
    reflexivity.
  + intros.
    rewrite IHP1.
    rewrite IHP2.
    reflexivity.
  + intros.
    rewrite IHP1.
    rewrite IHP2.
    reflexivity.
  + intros.
    rewrite IHP.
    reflexivity.
  + intros.
    destruct aexp_occur;
    simpl;
    unfold Interp_Lupdate;
    simpl.
    - split; intros.
      * destruct H.
        exists x0.
        apply IHP.
        exact H.
      * destruct H.
        exists x0.
        apply IHP.
        exact H.
    - split; intros.
      * destruct H.
        exists x0.
        pose proof Assn_rename_assertion_iff st La (rename_all E P) E x0 x.
        specialize (IHP (Lassn_update La x x0)).
        rewrite <- H0.
        rewrite <- IHP.
        exact H.
      * destruct H.
        exists x0.
        pose proof Assn_rename_assertion_iff st La (rename_all E P) E x0 x.
        specialize (IHP (Lassn_update La x x0)).
        rewrite IHP.
        apply H0.
        exact H.
  + destruct aexp_occur;
    simpl;
    unfold Interp_Lupdate;
    simpl.
    - split; intros.
      * specialize (H v).
        apply IHP.
        exact H.
      * specialize (H v).
        apply IHP.
        exact H.
    - split; intros.
      * pose proof Assn_rename_assertion_iff st La (rename_all E P) E v x.
        specialize (IHP (Lassn_update La x v)).
        rewrite <- H0.
        rewrite <- IHP.
        apply H.
      * pose proof Assn_rename_assertion_iff st La (rename_all E P) E v x.
        specialize (IHP (Lassn_update La x v)).
        rewrite IHP.
        apply H0.
        apply H.
Qed.


Lemma Assertion_sub_spec_2: forall st1 st2 La (P: Assertion) (X: var) (E: aexp'),
  st2 X = aexp'_denote (st1, La) E ->
  (forall Y : var, X <> Y -> st1 Y = st2 Y) ->
  (st1, La) |== naive_sub X E (rename_all E P) <-> (st2, La) |== (rename_all E P).
Proof.
  (* intros.
  revert P La H.
  induction E; simpl; intros.
  + admit.
  + admit.
  + admit.
  + 
  + *)
  intros.
  revert E La H H0.
  induction P; simpl; intros.
  + pose proof Term_denote_term_sub st1 st2 La X E t1 H H0.
    pose proof Term_denote_term_sub st1 st2 La X E t2 H H0.
    rewrite H1.
    rewrite H2.
    reflexivity.
  + pose proof Term_denote_term_sub st1 st2 La X E t1 H H0.
    pose proof Term_denote_term_sub st1 st2 La X E t2 H H0.
    rewrite H1.
    rewrite H2.
    reflexivity.
  + pose proof Term_denote_term_sub st1 st2 La X E t1 H H0.
    pose proof Term_denote_term_sub st1 st2 La X E t2 H H0.
    rewrite H1.
    rewrite H2.
    reflexivity.
  + induction b; simpl.
    - reflexivity.
    - reflexivity.
    - pose proof Aexp_denote_aexp_sub st1 st2 La X E a1 H H0.
      pose proof Aexp_denote_aexp_sub st1 st2 La X E a2 H H0.
      rewrite H1.
      rewrite H2.
      reflexivity.
    - pose proof Aexp_denote_aexp_sub st1 st2 La X E a1 H H0.
      pose proof Aexp_denote_aexp_sub st1 st2 La X E a2 H H0.
      rewrite H1.
      rewrite H2.
      reflexivity.
    - rewrite IHb.
      reflexivity.
    - rewrite IHb1.
      rewrite IHb2.
      reflexivity.
  + specialize (IHP1 E La H H0).
    specialize (IHP2 E La H H0).
    rewrite IHP1.
    rewrite IHP2.
    reflexivity.
  + specialize (IHP1 E La H H0).
    specialize (IHP2 E La H H0).
    rewrite IHP1.
    rewrite IHP2.
    reflexivity.
  + specialize (IHP1 E La H H0).
    specialize (IHP2 E La H H0).
    rewrite IHP1.
    rewrite IHP2.
    reflexivity.
  + specialize (IHP E La H H0).
    rewrite IHP.
    reflexivity.
  + destruct aexp_occur; simpl;
    unfold Interp_Lupdate; simpl.
    - split; intros;
      destruct H1 as [v0 ?]; exists v0.
      * admit.
        (* assert (assn_occur x (rename_all E P) = O). admit.
        pose proof no_occ_satisfies_not_free st2 La (rename_all E P) x v0 H2.
        rewrite <- H3.
        pose proof IHP E La H H0.
        rewrite <- H4.
        assert (assn_occur x (naive_sub X E (rename_all E P)) = O). admit.
        pose proof no_occ_satisfies_not_free st1 La (naive_sub X E (rename_all E P)) x v0 H5.
        rewrite H6.
        exact H1. *)
      
        (*
        pose proof Aexp_denote_lassn_update st1 La E x v0.
        rewrite H2 in H.
        pose proof IHP E (Lassn_update La x v0) H H0.
        rewrite H3 in H1.
        exact H1.
        pose proof IHP E 
        pose proof IHP E La H H0.
        admit. *)
      * admit.
    - (* pose proof Assn_rename_assertion_iff. *)
      split; intros;
      destruct H1 as [v0 ?]; exists v0.
      * pose proof Assn_rename_assertion_iff st2 La (rename_all E P) E v0 x.
        rewrite <- H2.
        clear H2.
        admit.
      * admit.
  + destruct aexp_occur; simpl;
    unfold Interp_Lupdate; simpl.
    split; intros.
    - specialize (H1 v).
      admit.
    - specialize (H1 v).
      admit.
Admitted.

(* Use for the proof of hoare_asgn_bwd_sound. *)
Lemma Assertion_sub_spec: forall st1 st2 La (P: Assertion) (X: var) (E: aexp'),
  st2 X = aexp'_denote (st1, La) E ->
  (forall Y : var, X <> Y -> st1 Y = st2 Y) ->
  ((st1, La) |== P[ X |-> E]) <-> ((st2, La) |== P).
Proof.
  intros.
  unfold assn_sub.
  pose proof Assertion_sub_spec_1 st2 La P E.
  pose proof Assertion_sub_spec_2 st1 st2 La P X E H H0.
  rewrite H1.
  exact H2.
Qed.

End Assertion_Sub_Spec_Lemma_Module.