Require Import PL.Imp.
Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Relations.Relation_Definitions.

Module Lemmas_of_Assertion_Sub_Spec_Lemma_Module.

Import Assertion_D.

Lemma Aexp_max_var_to_aexp_occur : forall a x, (aexp_max_var a < x)%nat -> aexp_occur x a = 0%nat
with Term_max_var_to_term_occur : forall t x, (term_max_var t < x)%nat -> term_occur x t = 0%nat.
Proof.
{
  clear Aexp_max_var_to_aexp_occur.
  intros.
  induction a; simpl.
  + simpl in H.
    apply Term_max_var_to_term_occur.
    exact H.
  + reflexivity.
  + simpl in H.
    apply Nat.max_lub_lt_iff in H.
    destruct H.
    specialize (IHa1 H).
    specialize (IHa2 H0).
    rewrite IHa1.
    rewrite IHa2.
    omega.
  + simpl in H.
    apply Nat.max_lub_lt_iff in H.
    destruct H.
    specialize (IHa1 H).
    specialize (IHa2 H0).
    rewrite IHa1.
    rewrite IHa2.
    omega.
  + simpl in H.
    apply Nat.max_lub_lt_iff in H.
    destruct H.
    specialize (IHa1 H).
    specialize (IHa2 H0).
    rewrite IHa1.
    rewrite IHa2.
    omega.
}
{
  clear Term_max_var_to_term_occur.
  intros.
  induction t; simpl.
  + reflexivity.
  + simpl in H.
    destruct Nat.eq_dec.
    - omega.
    - reflexivity.
  + simpl in H.
    apply Aexp_max_var_to_aexp_occur.
    exact H.
  + simpl in H.
    apply Nat.max_lub_lt_iff in H.
    destruct H.
    specialize (IHt1 H).
    specialize (IHt2 H0).
    rewrite IHt1.
    rewrite IHt2.
    omega.
  + simpl in H.
    apply Nat.max_lub_lt_iff in H.
    destruct H.
    specialize (IHt1 H).
    specialize (IHt2 H0).
    rewrite IHt1.
    rewrite IHt2.
    omega.
  + simpl in H.
    apply Nat.max_lub_lt_iff in H.
    destruct H.
    specialize (IHt1 H).
    specialize (IHt2 H0).
    rewrite IHt1.
    rewrite IHt2.
    omega.
}
Qed.

Lemma Assn_new_var_to_occur: forall E P x,
  x = new_var P E -> assn_occur x P = O /\ aexp_occur x E = O.
Proof.
  intros.
  unfold new_var in H.
  assert (((Init.Nat.max (assn_max_var P) (aexp_max_var E)) < x)%nat).
  {omega. }
  clear H.
  apply Nat.max_lub_lt_iff in H0.
  destruct H0.
  split.
  + clear H0 E.
    induction P; simpl; simpl in H.
    - apply Nat.max_lub_lt_iff in H.
      destruct H.
      pose proof Term_max_var_to_term_occur _ _ H.
      pose proof Term_max_var_to_term_occur _ _ H0.
      rewrite H1.
      rewrite H2.
      omega.
    - apply Nat.max_lub_lt_iff in H.
      destruct H.
      pose proof Term_max_var_to_term_occur _ _ H.
      pose proof Term_max_var_to_term_occur _ _ H0.
      rewrite H1.
      rewrite H2.
      omega.
    - apply Nat.max_lub_lt_iff in H.
      destruct H.
      pose proof Term_max_var_to_term_occur _ _ H.
      pose proof Term_max_var_to_term_occur _ _ H0.
      rewrite H1.
      rewrite H2.
      omega.
    - induction b; simpl.
      * reflexivity.
      * reflexivity.
      * simpl in H.
        apply Nat.max_lub_lt_iff in H.
        destruct H.
        pose proof Aexp_max_var_to_aexp_occur _ _ H.
        pose proof Aexp_max_var_to_aexp_occur _ _ H0.
        rewrite H1.
        rewrite H2.
        omega.
      * simpl in H.
        apply Nat.max_lub_lt_iff in H.
        destruct H.
        pose proof Aexp_max_var_to_aexp_occur _ _ H.
        pose proof Aexp_max_var_to_aexp_occur _ _ H0.
        rewrite H1.
        rewrite H2.
        omega.
      * simpl in H.
        specialize (IHb H).
        exact IHb.
      * simpl in H.
        apply Nat.max_lub_lt_iff in H.
        destruct H.
        specialize (IHb1 H).
        specialize (IHb2 H0).
        rewrite IHb1.
        rewrite IHb2.
        omega.
    - apply Nat.max_lub_lt_iff in H.
      destruct H.
      specialize (IHP1 H).
      specialize (IHP2 H0).
      rewrite IHP1.
      rewrite IHP2.
      omega.
    - apply Nat.max_lub_lt_iff in H.
      destruct H.
      specialize (IHP1 H).
      specialize (IHP2 H0).
      rewrite IHP1.
      rewrite IHP2.
      omega.
    - apply Nat.max_lub_lt_iff in H.
      destruct H.
      specialize (IHP1 H).
      specialize (IHP2 H0).
      rewrite IHP1.
      rewrite IHP2.
      omega.
    - specialize (IHP H).
      exact IHP.
    - apply Nat.max_lub_lt_iff in H.
      destruct H.
      specialize (IHP H0).
      rewrite IHP.
      destruct Nat.eq_dec.
      * omega.
      * reflexivity.
    - apply Nat.max_lub_lt_iff in H.
      destruct H.
      specialize (IHP H0).
      rewrite IHP.
      destruct Nat.eq_dec.
      * omega.
      * reflexivity.
  + apply Aexp_max_var_to_aexp_occur.
    exact H0.
Qed.

Lemma term_occur_zero_add_zero: forall x t1 t2,
(term_occur x t1 + term_occur x t2)%nat = O -> term_occur x t1 = O /\ term_occur x t2 = O.
Proof.
  intros.
  omega.
Qed.

Lemma aexp_occur_zero_add_zero: forall x t1 t2,
(aexp_occur x t1 + aexp_occur x t2)%nat = O -> aexp_occur x t1 = O /\ aexp_occur x t2 = O.
Proof.
  intros.
  omega.
Qed.

Lemma bexp_occur_zero_add_zero: forall x t1 t2,
(bexp_occur x t1 + bexp_occur x t2)%nat = O -> bexp_occur x t1 = O /\ bexp_occur x t2 = O.
Proof.
  intros.
  omega.
Qed.

Lemma assn_occur_zero_add_zero: forall x t1 t2,
(assn_occur x t1 + assn_occur x t2)%nat = O -> assn_occur x t1 = O /\ assn_occur x t2 = O.
Proof.
  intros.
  omega.
Qed.

Lemma No_aexp_occur_to_aexp_rename :
forall st La x y v a, aexp_occur y a = O ->
aexp'_denote (st, Lassn_update La x v) a =
aexp'_denote (st, Lassn_update La y v) (aexp_rename x y a)
with No_term_occur_to_term_rename :
forall st La x y v t, term_occur y t = O ->
term_denote (st, Lassn_update La x v) t =
term_denote (st, Lassn_update La y v) (term_rename x y t).
Proof.
{
  clear No_aexp_occur_to_aexp_rename.
  intros.
  induction a; simpl; simpl in H.
  + pose proof No_term_occur_to_term_rename st La x y v t H.
    exact H0.
  + reflexivity.
  + apply aexp_occur_zero_add_zero in H; destruct H.
    specialize (IHa1 H).
    specialize (IHa2 H0).
    rewrite IHa1.
    rewrite IHa2.
    reflexivity.
  + apply aexp_occur_zero_add_zero in H; destruct H.
    specialize (IHa1 H).
    specialize (IHa2 H0).
    rewrite IHa1.
    rewrite IHa2.
    reflexivity.
  + apply aexp_occur_zero_add_zero in H; destruct H.
    specialize (IHa1 H).
    specialize (IHa2 H0).
    rewrite IHa1.
    rewrite IHa2.
    reflexivity.
}
{
  clear No_term_occur_to_term_rename.
  intros.
  induction t; simpl; simpl in H.
  + reflexivity.
  + destruct Nat.eq_dec.
    - discriminate.
    - destruct Nat.eq_dec.
      * subst.
        clear H.
        unfold Lassn_update at 1.
        destruct Nat.eq_dec.
        ++ unfold term_denote; simpl.
           unfold Lassn_update.
           destruct Nat.eq_dec.
           -- reflexivity.
           -- omega.
        ++ omega.
      * unfold Lassn_update at 1.
        destruct Nat.eq_dec.
        ++ omega.
        ++ unfold term_denote; simpl.
           unfold Lassn_update.
           destruct Nat.eq_dec.
           -- omega.
           -- reflexivity.
  + pose proof No_aexp_occur_to_aexp_rename st La x y v a H.
    exact H0.
  + apply term_occur_zero_add_zero in H; destruct H.
    specialize (IHt1 H).
    specialize (IHt2 H0).
    rewrite IHt1.
    rewrite IHt2.
    reflexivity.
  + apply term_occur_zero_add_zero in H; destruct H.
    specialize (IHt1 H).
    specialize (IHt2 H0).
    rewrite IHt1.
    rewrite IHt2.
    reflexivity.
  + apply term_occur_zero_add_zero in H; destruct H.
    specialize (IHt1 H).
    specialize (IHt2 H0).
    rewrite IHt1.
    rewrite IHt2.
    reflexivity.
}
Qed.

Lemma No_aexp_occur_to_aexp :
forall st La x v a, aexp_occur x a = O ->
aexp'_denote (st, La) a =
aexp'_denote (st, Lassn_update La x v) a
with No_term_occur_to_term :
forall st La x v t, term_occur x t = O ->
term_denote (st, La) t =
term_denote (st, Lassn_update La x v) t.
Proof.
{
  clear No_aexp_occur_to_aexp.
  intros.
  induction a; simpl; simpl in H.
  + apply No_term_occur_to_term.
    exact H.
  + reflexivity.
  + apply aexp_occur_zero_add_zero in H; destruct H.
    specialize (IHa1 H).
    specialize (IHa2 H0).
    rewrite IHa1.
    rewrite IHa2.
    reflexivity.
  + apply aexp_occur_zero_add_zero in H; destruct H.
    specialize (IHa1 H).
    specialize (IHa2 H0).
    rewrite IHa1.
    rewrite IHa2.
    reflexivity.
  + apply aexp_occur_zero_add_zero in H; destruct H.
    specialize (IHa1 H).
    specialize (IHa2 H0).
    rewrite IHa1.
    rewrite IHa2.
    reflexivity.
}
{
  clear No_term_occur_to_term.
  intros.
  induction t; simpl; simpl in H.
  + reflexivity.
  + destruct Nat.eq_dec.
    - omega.
    - pose proof Lassn_update_spec La x v.
      destruct H0.
      specialize (H1 x0 n).
      exact H1.
  + apply No_aexp_occur_to_aexp.
    exact H.
  + apply term_occur_zero_add_zero in H; destruct H.
    specialize (IHt1 H).
    specialize (IHt2 H0).
    rewrite IHt1.
    rewrite IHt2.
    reflexivity.
  + apply term_occur_zero_add_zero in H; destruct H.
    specialize (IHt1 H).
    specialize (IHt2 H0).
    rewrite IHt1.
    rewrite IHt2.
    reflexivity.
  + apply term_occur_zero_add_zero in H; destruct H.
    specialize (IHt1 H).
    specialize (IHt2 H0).
    rewrite IHt1.
    rewrite IHt2.
    reflexivity.
}
Qed.

Lemma no_occ_satisfies_not_free: forall st La P x v,
  assn_occur x P = O ->
  ((st, La) |== P <-> (st, Lassn_update La x v) |== P).
Proof.
  intros.
  revert La.
  induction P; simpl; simpl in H; intros.
  + apply term_occur_zero_add_zero in H; destruct H.
    pose proof No_term_occur_to_term st La x v t1 H.
    pose proof No_term_occur_to_term st La x v t2 H0.
    rewrite <- H1.
    rewrite <- H2.
    reflexivity.
  + apply term_occur_zero_add_zero in H; destruct H.
    pose proof No_term_occur_to_term st La x v t1 H.
    pose proof No_term_occur_to_term st La x v t2 H0.
    rewrite <- H1.
    rewrite <- H2.
    reflexivity.
  + apply term_occur_zero_add_zero in H; destruct H.
    pose proof No_term_occur_to_term st La x v t1 H.
    pose proof No_term_occur_to_term st La x v t2 H0.
    rewrite <- H1.
    rewrite <- H2.
    reflexivity.
  + induction b; simpl; simpl in H.
    - reflexivity.
    - reflexivity.
    - apply aexp_occur_zero_add_zero in H; destruct H.
      pose proof No_aexp_occur_to_aexp st La x v a1 H.
      pose proof No_aexp_occur_to_aexp st La x v a2 H0.
      rewrite <- H1.
      rewrite <- H2.
      reflexivity.
    - apply aexp_occur_zero_add_zero in H; destruct H.
      pose proof No_aexp_occur_to_aexp st La x v a1 H.
      pose proof No_aexp_occur_to_aexp st La x v a2 H0.
      rewrite <- H1.
      rewrite <- H2.
      reflexivity.
    - specialize (IHb H).
      rewrite IHb.
      reflexivity.
    - apply bexp_occur_zero_add_zero in H; destruct H.
      specialize (IHb1 H).
      specialize (IHb2 H0).
      rewrite IHb1.
      rewrite IHb2.
      reflexivity.
  + apply assn_occur_zero_add_zero in H; destruct H.
    specialize (IHP1 H La).
    specialize (IHP2 H0 La).
    rewrite IHP1.
    rewrite IHP2.
    reflexivity.
  + apply assn_occur_zero_add_zero in H; destruct H.
    specialize (IHP1 H La).
    specialize (IHP2 H0 La).
    rewrite IHP1.
    rewrite IHP2.
    reflexivity.
  + apply assn_occur_zero_add_zero in H; destruct H.
    specialize (IHP1 H La).
    specialize (IHP2 H0 La).
    rewrite IHP1.
    rewrite IHP2.
    reflexivity.
  + specialize (IHP H La).
    rewrite IHP.
    reflexivity.
  + destruct Nat.eq_dec.
    - omega.
    - specialize (IHP H).
      unfold Interp_Lupdate; simpl.
      split; intros;
      destruct H0 as [v0 ?];
      exists v0.
      * pose proof Lassn_update_update_diff st La x x0 v v0 n.
        pose proof satisfies_Interp_Equiv (st, Lassn_update (Lassn_update La x v) x0 v0) (st, Lassn_update (Lassn_update La x0 v0) x v) P H1.
        rewrite H2.
        clear H1 H2.
        specialize (IHP (Lassn_update La x0 v0)).
        rewrite <- IHP.
        exact H0.
      * pose proof Lassn_update_update_diff st La x x0 v v0 n.
        pose proof satisfies_Interp_Equiv (st, Lassn_update (Lassn_update La x v) x0 v0) (st, Lassn_update (Lassn_update La x0 v0) x v) P H1.
        rewrite H2 in H0.
        clear H1 H2.
        specialize (IHP (Lassn_update La x0 v0)).
        rewrite IHP.
        exact H0.
  + destruct Nat.eq_dec.
    - discriminate.
    - specialize (IHP H).
      unfold Interp_Lupdate; simpl.
      split; intros.
      * specialize (H0 v0).
        pose proof Lassn_update_update_diff st La x x0 v v0 n.
        pose proof satisfies_Interp_Equiv (st, Lassn_update (Lassn_update La x v) x0 v0) (st, Lassn_update (Lassn_update La x0 v0) x v) P H1.
        rewrite H2.
        clear H1 H2.
        specialize (IHP (Lassn_update La x0 v0)).
        rewrite <- IHP.
        exact H0.
      * specialize (H0 v0).
        pose proof Lassn_update_update_diff st La x x0 v v0 n.
        pose proof satisfies_Interp_Equiv (st, Lassn_update (Lassn_update La x v) x0 v0) (st, Lassn_update (Lassn_update La x0 v0) x v) P H1.
        rewrite H2 in H0.
        clear H1 H2.
        specialize (IHP (Lassn_update La x0 v0)).
        rewrite IHP.
        exact H0.
Qed.

Lemma Assn_rename_assertion_iff : forall st La P E v x,
(st, Lassn_update La x v) |== P <->
(st, Lassn_update La (new_var P E) v) |== assn_rename x (new_var P E) P.
Proof.
  intros.
  remember (new_var P E) as y.
  pose proof Assn_new_var_to_occur _ _ _ Heqy.
  destruct H.
  clear Heqy H0 E.
  revert La x y v H.
  induction P; intros; simpl; simpl in H.
  + apply term_occur_zero_add_zero in H; destruct H.
    pose proof No_term_occur_to_term_rename st La x y v t1 H.
    pose proof No_term_occur_to_term_rename st La x y v t2 H0.
    rewrite <- H1.
    rewrite <- H2.
    reflexivity.
  + apply term_occur_zero_add_zero in H; destruct H.
    pose proof No_term_occur_to_term_rename st La x y v t1 H.
    pose proof No_term_occur_to_term_rename st La x y v t2 H0.
    rewrite <- H1.
    rewrite <- H2.
    reflexivity.
  + apply term_occur_zero_add_zero in H; destruct H.
    pose proof No_term_occur_to_term_rename st La x y v t1 H.
    pose proof No_term_occur_to_term_rename st La x y v t2 H0.
    rewrite <- H1.
    rewrite <- H2.
    reflexivity.
  + induction b; simpl in H; simpl.
    - reflexivity.
    - reflexivity.
    - apply aexp_occur_zero_add_zero in H; destruct H.
      pose proof No_aexp_occur_to_aexp_rename st La x y v a1 H.
      pose proof No_aexp_occur_to_aexp_rename st La x y v a2 H0.
      rewrite <- H1.
      rewrite <- H2.
      reflexivity.
    - apply aexp_occur_zero_add_zero in H; destruct H.
      pose proof No_aexp_occur_to_aexp_rename st La x y v a1 H.
      pose proof No_aexp_occur_to_aexp_rename st La x y v a2 H0.
      rewrite <- H1.
      rewrite <- H2.
      reflexivity.
    - specialize (IHb H).
      rewrite IHb.
      reflexivity.
    - apply bexp_occur_zero_add_zero in H; destruct H.
      pose proof IHb1 H.
      pose proof IHb2 H0.
      rewrite <- H1.
      rewrite <- H2.
      reflexivity.
  + apply assn_occur_zero_add_zero in H; destruct H.
    pose proof IHP1 La x y v H.
    pose proof IHP2 La x y v H0.
    rewrite <- H1.
    rewrite <- H2.
    reflexivity.
  + apply assn_occur_zero_add_zero in H; destruct H.
    pose proof IHP1 La x y v H.
    pose proof IHP2 La x y v H0.
    rewrite <- H1.
    rewrite <- H2.
    reflexivity.
  + apply assn_occur_zero_add_zero in H; destruct H.
    pose proof IHP1 La x y v H.
    pose proof IHP2 La x y v H0.
    rewrite <- H1.
    rewrite <- H2.
    reflexivity.
  + pose proof IHP La x y v H.
    rewrite <- H0.
    reflexivity.
  + destruct Nat.eq_dec in H.
    - discriminate.
    - destruct Nat.eq_dec.
      * simpl.
        subst.
        split; intros;
        destruct H0 as [v0 ?];
        exists v0.
        ++ unfold Interp_Lupdate; simpl.
           unfold Interp_Lupdate in H0; simpl in H0.
           pose proof Lassn_update_update_same st La x v v0.
           pose proof satisfies_Interp_Equiv (st, Lassn_update (Lassn_update La x v) x v0) (st, Lassn_update La x v0) P H1.
           rewrite H2 in H0.
           clear H1 H2.
           pose proof Lassn_update_update_diff st La y x v v0 n.
           pose proof satisfies_Interp_Equiv (st, Lassn_update (Lassn_update La y v) x v0) (st, Lassn_update (Lassn_update La x v0) y v) P H1.
           apply H2.
           clear H1 H2.
           pose proof no_occ_satisfies_not_free st (Lassn_update La x v0) P y v H.
           rewrite <- H1.
           exact H0.
        ++ pose proof Lassn_update_update_same st La x v v0.
           unfold Interp_Lupdate; simpl.
           unfold Interp_Lupdate in H0; simpl in H0.
           pose proof satisfies_Interp_Equiv (st, Lassn_update (Lassn_update La x v) x v0) (st, Lassn_update La x v0) P H1.
           rewrite H2.
           clear H1 H2.
           pose proof Lassn_update_update_diff st La y x v v0 n.
           pose proof satisfies_Interp_Equiv (st, Lassn_update (Lassn_update La y v) x v0) (st, Lassn_update (Lassn_update La x v0) y v) P H1.
           apply H2 in H0.
           clear H1 H2.
           pose proof no_occ_satisfies_not_free st (Lassn_update La x v0) P y v H.
           rewrite H1.
           exact H0.
      * simpl.
        unfold Interp_Lupdate; simpl.
        split; intros;
        destruct H0 as [v0 ?];
        exists v0.
        ++ pose proof IHP (Lassn_update La x v0) x0 y v H.
           pose proof Lassn_update_update_diff st La x0 x v v0 n0.
           pose proof satisfies_Interp_Equiv (st, Lassn_update (Lassn_update La x0 v) x v0) (st, Lassn_update (Lassn_update La x v0) x0 v) P H2.
           rewrite H3 in H0.
           rewrite H1 in H0.
           clear H1 H2 H3.
           pose proof Lassn_update_update_diff st La y x v v0 n.
           pose proof satisfies_Interp_Equiv (st, Lassn_update (Lassn_update La y v) x v0) (st, Lassn_update (Lassn_update La x v0) y v) (assn_rename x0 y P) H1.
           rewrite H2.
           exact H0.
        ++ pose proof IHP (Lassn_update La x v0) x0 y v H.
           pose proof Lassn_update_update_diff st La x0 x v v0 n0.
           pose proof satisfies_Interp_Equiv (st, Lassn_update (Lassn_update La x0 v) x v0) (st, Lassn_update (Lassn_update La x v0) x0 v) P H2.
           rewrite H3.
           rewrite H1.
           clear H1 H2 H3.
           pose proof Lassn_update_update_diff st La y x v v0 n.
           pose proof satisfies_Interp_Equiv (st, Lassn_update (Lassn_update La y v) x v0) (st, Lassn_update (Lassn_update La x v0) y v) (assn_rename x0 y P) H1.
           rewrite H2 in H0.
           exact H0.
  + destruct Nat.eq_dec in H.
    - discriminate.
    - destruct Nat.eq_dec.
      * simpl.
        subst.
        split; intros;
        specialize (H0 v0).
        ++ pose proof Lassn_update_update_same st La x v v0.
           unfold Interp_Lupdate; simpl.
           pose proof satisfies_Interp_Equiv (st, Lassn_update (Lassn_update La x v) x v0) (st, Lassn_update La x v0) P H1.
           rewrite H2 in H0.
           clear H1 H2.
           pose proof Lassn_update_update_diff st La y x v v0 n.
           pose proof satisfies_Interp_Equiv (st, Lassn_update (Lassn_update La y v) x v0) (st, Lassn_update (Lassn_update La x v0) y v) P H1.
           apply H2.
           clear H1 H2.
           pose proof no_occ_satisfies_not_free st (Lassn_update La x v0) P y v H.
           rewrite <- H1.
           exact H0.
        ++ pose proof Lassn_update_update_same st La x v v0.
           unfold Interp_Lupdate; simpl.
           unfold Interp_Lupdate in H0; simpl in H0.
           pose proof satisfies_Interp_Equiv (st, Lassn_update (Lassn_update La x v) x v0) (st, Lassn_update La x v0) P H1.
           rewrite H2.
           clear H1 H2.
           pose proof Lassn_update_update_diff st La y x v v0 n.
           pose proof satisfies_Interp_Equiv (st, Lassn_update (Lassn_update La y v) x v0) (st, Lassn_update (Lassn_update La x v0) y v) P H1.
           apply H2 in H0.
           clear H1 H2.
           pose proof no_occ_satisfies_not_free st (Lassn_update La x v0) P y v H.
           rewrite H1.
           exact H0.
      * simpl.
        unfold Interp_Lupdate; simpl.
        split; intros;
        specialize (H0 v0).
        ++ pose proof IHP (Lassn_update La x v0) x0 y v H.
           pose proof Lassn_update_update_diff st La x0 x v v0 n0.
           pose proof satisfies_Interp_Equiv (st, Lassn_update (Lassn_update La x0 v) x v0) (st, Lassn_update (Lassn_update La x v0) x0 v) P H2.
           rewrite H3 in H0.
           rewrite H1 in H0.
           clear H1 H2 H3.
           pose proof Lassn_update_update_diff st La y x v v0 n.
           pose proof satisfies_Interp_Equiv (st, Lassn_update (Lassn_update La y v) x v0) (st, Lassn_update (Lassn_update La x v0) y v) (assn_rename x0 y P) H1.
           rewrite H2.
           exact H0.
        ++ pose proof IHP (Lassn_update La x v0) x0 y v H.
           pose proof Lassn_update_update_diff st La x0 x v v0 n0.
           pose proof satisfies_Interp_Equiv (st, Lassn_update (Lassn_update La x0 v) x v0) (st, Lassn_update (Lassn_update La x v0) x0 v) P H2.
           rewrite H3.
           rewrite H1.
           clear H1 H2 H3.
           pose proof Lassn_update_update_diff st La y x v v0 n.
           pose proof satisfies_Interp_Equiv (st, Lassn_update (Lassn_update La y v) x v0) (st, Lassn_update (Lassn_update La x v0) y v) (assn_rename x0 y P) H1.
           rewrite H2 in H0.
           exact H0.
Qed.


Lemma Term_denote_term_sub: forall st1 st2 La X E t,
  st2 X = aexp'_denote (st1, La) E ->
  (forall Y : var, X <> Y -> st1 Y = st2 Y) ->
  term_denote (st1, La) (term_sub X E t) = term_denote (st2, La) t
with Aexp_denote_aexp_sub: forall st1 st2 La X E a,
  st2 X = aexp'_denote (st1, La) E ->
  (forall Y : var, X <> Y -> st1 Y = st2 Y) ->
  aexp'_denote (st1, La) (aexp_sub X E a) = aexp'_denote (st2, La) a.
Proof.
{
  clear Term_denote_term_sub.
  intros.
  induction t; simpl.
  + reflexivity.
  + reflexivity.
  + pose proof Aexp_denote_aexp_sub st1 st2 La X E a H H0.
    exact H1.
  + rewrite IHt1.
    rewrite IHt2.
    reflexivity.
  + rewrite IHt1.
    rewrite IHt2.
    reflexivity.
  + rewrite IHt1.
    rewrite IHt2.
    reflexivity.
}
{
  clear Aexp_denote_aexp_sub.
  intros.
  induction a; simpl.
  + pose proof Term_denote_term_sub st1 st2 La X E t H H0.
    exact H1.
  + destruct Nat.eq_dec.
    - rewrite <- H.
      rewrite e.
      reflexivity.
    - firstorder.
  + rewrite IHa1.
    rewrite IHa2.
    reflexivity.
  + rewrite IHa1.
    rewrite IHa2.
    reflexivity.
  + rewrite IHa1.
    rewrite IHa2.
    reflexivity.
}
Qed.


End Lemmas_of_Assertion_Sub_Spec_Lemma_Module.