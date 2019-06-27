Require Import PL.Imp.
Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Relations.Relation_Definitions.
Import Assertion_D.

Definition concat'(d1 d2 d3:state->exit_kind->state->Prop):
state->exit_kind->state->Prop:=
fun st1 ek st2=>
 exists (st3:state) (ek':exit_kind),  d1 st1 ek' st3/\
  ((ek'=EK_Break /\ d3 st3 ek st2)\/ 
  (ek'<>EK_Break /\ exists st4, d2 st3 EK_Normal st4/\ 
  d3 st4 ek st2)).
  
Fixpoint ceval_Normal(c:com)(s:cstack): state->exit_kind->state->Prop:=
  match s with
  |nil=> ceval c
  |cons (b,c1,c2) s'=> concat'(ceval c)(ceval (CWhile b c1))(ceval_Normal c2 s')
  end.
Definition concat_loop(b:bexp)(d1 d2 d3:state->exit_kind->state->Prop):
state->exit_kind->state->Prop:=
fun st1 ek st2=>
 (beval b st1 /\ concat' d1 d2 d3 st1 ek st2)\/
 (~beval b st1/\ d3 st1 ek st2).

Definition ceval_LoopCond(b:bexp)(s:cstack):state->exit_kind->state->Prop:=
  match s with
  |nil=>ceval CSkip
  |cons(b',c1,c2) s'=>concat_loop b (ceval c1)  (ceval (CWhile b' c1)) (ceval_Normal c2 s')
  end.


Fixpoint ceval'(c:com'):state->exit_kind->state->Prop:=
  match c with
  |CNormal s c => ceval_Normal c s
  |CLoopCond s b=> ceval_LoopCond b s
  end.
  
Lemma aeval_preserve: forall st a1 a2,
  astep st a1 a2 ->
  aeval a1 st  = aeval a2 st.
Proof.
  intros.
  induction H.
  + simpl.
    reflexivity.
  + simpl.
    rewrite IHastep.
    reflexivity.
  + simpl.
    rewrite IHastep.
    reflexivity.
  + simpl.
    reflexivity.
  + simpl.
    rewrite IHastep.
    reflexivity.
  + simpl.
    rewrite IHastep.
    reflexivity.
  + simpl.
    reflexivity.
  + simpl.
    rewrite IHastep.
    reflexivity.
  + simpl.
    rewrite IHastep.
    reflexivity.
  + simpl.
    reflexivity.
Qed.


Lemma beval_preserve: forall st b1 b2,
  bstep st b1 b2 ->
  (beval b1 st  <-> beval b2 st).
Proof.
  intros.
  induction H.
  + apply aeval_preserve in H.
    simpl.
    rewrite H.
    tauto.
  + apply aeval_preserve in H0.
    simpl.
    rewrite H0.
    tauto.
  + simpl.
    tauto.
  + simpl.
    tauto.
  + apply aeval_preserve in H.
    simpl.
    rewrite H.
    tauto.
  + apply aeval_preserve in H0.
    simpl.
    rewrite H0.
    tauto.
  + simpl.
    tauto.
  + simpl.
    omega.
  + simpl.
    tauto.
  + simpl.
    tauto.
  + simpl.
    tauto.
  + simpl.
    tauto.
  + simpl.
    tauto.
  + simpl.
    tauto.
Qed.


Lemma Break_Condition:forall c st,
start_with_break c->
ceval c st EK_Break st.
Proof.
  intros. 
  induction H.
  +  simpl.
      unfold break_sem.
      split.
      -  reflexivity.
      -  reflexivity.
  +  simpl.
      unfold seq_sem.
      right.
      split.
      -  tauto.
      -  discriminate.
Qed.

Theorem Cont_Condition:forall c st,
start_with_cont c->
ceval c st EK_Cont st.
Proof.
  intros. 
  induction H.
  +  simpl.
      unfold break_sem.
      split.
      -  reflexivity.
      -  reflexivity.
  +  simpl.
      unfold seq_sem.
      right.
      split.
      -  tauto.
      -  discriminate.
Qed.

Lemma ceval_Normal_CSAssStep:  forall st s X a a' ,
      astep st a a' ->
        forall st' ek, ceval' (CNormal s (CAss X a'))  st ek st' -> ceval'  (CNormal s (CAss X a))  st ek st'.
Proof.
      intros.
      apply aeval_preserve in H.
      subst.
      induction s.
      +  simpl.
         simpl in H0.
         unfold asgn_sem.
         unfold asgn_sem in H0.
         rewrite H.
         tauto.
      +  destruct a0 as [p c2].
         destruct p as [b c1].
         simpl.
         simpl in  H0.
         unfold concat' in H0.
         unfold concat'.
         destruct H0 as [st4 [ek' [? ?]]].
         unfold asgn_sem in H0.
         destruct H0 as [? [? ?]].
         destruct H1.
         -  destruct H1 as [? ?].
             subst.
             discriminate.
         -  destruct H1 as [? [st5 [? ?]]].
            exists st4.
            exists ek'.
            split.
            *  unfold asgn_sem.
               rewrite H.
                tauto.
            *  right.
                split.
                tauto.
                exists st5.
                tauto.
Qed.

Lemma ceval_Normal_CSAss: 
     forall st1 st2 s X ,
      (forall Y, X <> Y -> st1 Y = st2 Y) ->
     forall st3 ek, ceval' (CNormal s CSkip) st2 ek st3->ceval' (CNormal s (CAss X (st2 X))) st1 ek st3.
Proof.
  intros.
   induction s.
   +   simpl.
         simpl in H0.
         unfold skip_sem in H0.
         destruct H0.
         unfold asgn_sem.
         subst.
         unfold aeval.
         split.
         { reflexivity. }
         split.
         {  reflexivity.  }
         { tauto. }
     + destruct a as [[b c1] c2].
         simpl.
         simpl in  H0.
         unfold concat' in H0.
         unfold concat'.
         destruct H0 as [st5 [ek' [? ?]]].
         unfold skip_sem in H0.
         destruct H1.
         -  destruct H1 as [? ?].
             destruct H0 as [? ?].
             subst.
             discriminate.
         -  destruct H1 as [? [st4 [? ?]]].
             destruct H0.
             exists st5.
             exists ek'.
             subst.
            split.
            *  unfold asgn_sem.
               simpl.
               split.
                {  tauto. }
                split.
                {  reflexivity. }
                tauto. 
            *  right.
               split.
               tauto.
               exists st4.
               tauto.
Qed.

Lemma ceval_Normal_Seq:
forall c s ek st st',  ceval' (CNormal s c) st ek st'->
ceval' (CNormal s (Skip;; c)) st ek st'.
Proof.
  intros.
  induction s.
  +  simpl.
       simpl in H.
       unfold seq_sem,skip_sem.
       left.
       exists st.
       split.
       split.
       -  reflexivity.
       -  reflexivity.
        - tauto.
   +  destruct a as [[b c1'] c2'].
        simpl.
        simpl in  H.
        unfold concat' in H.
        unfold concat'.
        destruct H as [st4 [ek' [? ?]]].
        destruct H0.
         -  destruct H0 as [? ?].
             exists st4.
             exists ek'.
             split.
             * unfold seq_sem,skip_sem.
                left.
                exists st.
                split.
                split.
                { reflexivity. }
                { reflexivity. }
                { tauto. }
            *  left.
                tauto.
        -  destruct H0 as [? [st5 [? ?]]].
            exists st4.
            exists ek'.
            split.
            *  unfold seq_sem,skip_sem.
                left.
                exists st.
                split.
                split.
                {  reflexivity. }
                { reflexivity. }
                { tauto.  }
            *  right.
               split.
               tauto.
               exists st5.
               tauto.
Qed.


Lemma Loop_Condition:
forall b st1 st2 st3 c ek, 
beval b st1->
ek<> EK_Break->
loop_sem b (ceval c) st2 EK_Normal st3->ceval c st1 ek st2->loop_sem b (ceval c) st1 EK_Normal st3.
Proof.
  intros.
  assert(ek=EK_Normal \/ ek=EK_Cont).
  {  induction ek;tauto. }
  unfold loop_sem.
  unfold loop_sem in H1.
  destruct H3.
  +  destruct H1 as [n [? ?]].
      exists (S n).
      simpl.
      split.
      split.
      -  left.
        exists st2.
        subst.
        tauto.
     -  tauto.
     -  reflexivity.
  +  destruct H1 as [n [? ?]].
       exists (S n).
       simpl.
       split.
       split.
       -  right.
          right.
          subst.
          exists st2.
          tauto.
        - tauto.
        - tauto.
Qed.


Theorem  ceval'_preserve: forall c1 c2 st1 st2,
cstep (c1, st1) (c2, st2) ->
  forall st3 ek, ceval' c2  st2 ek st3 -> ceval'  c1 st1 ek st3.
Proof.
  intros.
  revert H0.
  remember (c1, st1) as cst1 eqn:H0.
  remember (c2, st2) as cst2 eqn:H1.
  revert c1 c2 st1 st2 st3 H0 H1.
  induction H; simpl; intros.
  +  injection H0 as ? ?.
      injection H1 as ? ?.
      subst.
      pose proof (ceval_Normal_CSAssStep _ _ _ _ _ H _ _ H2).
      tauto.
  +  injection H1 as ? ?.
      injection H2 as ? ?.
      subst.
      pose proof (ceval_Normal_CSAss _ _ _ _   H0 _ _ H3).
      tauto.
  +  injection H0 as ? ?.
       injection H1 as ? ?.
       subst.
       induction s.
       -   simpl in H2.
           simpl.
           unfold seq_sem in H2.
           unfold seq_sem.
           assert ((CNormal nil c1, st1) =(CNormal nil c1, st1)). { reflexivity. }
            assert  ( (CNormal nil c1', st2) =(CNormal nil c1', st2) ).  { reflexivity. }
           destruct H2.
           *  destruct H2 as [st4 [? ?]].
               pose proof (classic (ek=EK_Normal)).
               left.
               exists st4.
               specialize (IHcstep _ _ _ _ st4 H0 H1).
               simpl in IHcstep.
               destruct H4.
               {  subst.
                   specialize (IHcstep H2).
                   tauto. }
               {  split.
                   admit.
                   tauto. }
           *  destruct H2.
               right.
               specialize (IHcstep _ _ _ _ st3 H0 H1).
               simpl in IHcstep.
               specialize (IHcstep H2).
               tauto.
      -    destruct a as [p c4].
           destruct p as [b c3].
           simpl.
           simpl in  H2.
           unfold concat' in H2.
           unfold concat'.
           destruct H2 as [st4 [ek' [? ?]]].
           unfold seq_sem in H0.
           admit.
  +  injection H0 as ? ?.
       injection H1 as ? ?.
       subst.
       pose proof (ceval_Normal_Seq _ _ _ _ _ H2).
       tauto.
  +   injection H0 as ? ?.
        injection H1 as ? ?.
        subst.
        simpl.
        simpl in H2.
        induction s.
        -   unfold if_sem.
            pose proof (beval_preserve _ _ _ H ).
            destruct H0.
            pose proof (classic (beval b' st2)).
            destruct H3.
            *  simpl.
                unfold if_sem.
                left.
                specialize(H1 H3).
                simpl in H2.
               unfold if_sem in H2.
               tauto.
            *  simpl.
                simpl in H2.
                unfold if_sem.
                unfold if_sem in H2.
                assert(~ beval b' st2).
                { tauto. }
                tauto.
        -   destruct a as [p c4].
            destruct p as [b0 c3].
            pose proof (beval_preserve _ _ _ H ).
            destruct H0 as [? ?].
            simpl.
            simpl in  H2.
            unfold concat' in H2.
            unfold concat'.
            destruct H2 as [st4 [ek' [? ?]]].
            unfold if_sem in H2.
            destruct H2.
            destruct H3.
         *  destruct H2 as [? ?].
             exists st4.
             exists ek'.
             split.
             { unfold if_sem.
                pose proof (H1 H4).
                tauto.  }
             left.
             tauto.
         *  destruct H3 as [? [st5 [? ?]]].
             destruct H2 as [? ?].
             exists st4.
             exists ek'.
             split.
             { unfold if_sem.
                pose proof (H1 H6).
                tauto.  }
             right.
             split.
             { tauto. }
             { exists st5.
               tauto.  }
         *  destruct H3.
             {
             destruct H3.
             destruct H2.
             exists st4.
             exists ek'.
             split.
             {  unfold if_sem.
                 assert(~beval b st2).
                 {  tauto. }
                 tauto. }
             left.
             tauto.
            }
            {  destruct H3 as [? [st5 [? ?]]].
                destruct H2.
                exists st4.
                exists ek'.
                split.
                {  unfold if_sem.
                    assert(~beval b st2).
                 {  tauto. }
                 tauto. }
                right.
                split.
                tauto.
                exists st5.
                tauto.
                }
  +    injection H0 as ? ?.
         injection H1 as ? ?.
         subst.
         simpl.
         simpl in H2.
         induction s.
         -  simpl.
            unfold if_sem.
            left.
            split.
           {tauto. }
           { simpl.
              tauto. }
        -  destruct a as [p c5].
           destruct p as [b0 c4].
           simpl.
           simpl in H2.
           unfold concat'.
           unfold concat' in H2.
           destruct H2 as [st4 [ek' [? ?]]].
           destruct H0.
           *  exists st4.
               exists ek'.
              split.
              {  unfold if_sem.
                 left.
                 simpl.
                 tauto.
              }
              tauto.
          *   exists st4.
               exists ek'.
              split.
              {  unfold if_sem.
                 left.
                 simpl.
                 tauto.
              }
             right.
             split.
             tauto.
             destruct H0 as [? [st5 ?]].
             exists st5.
             tauto.
  + injection H0 as ? ?.
    injection H1 as ? ?.
    subst.
    simpl.
    simpl in H2.
    induction s.
    -   simpl.
        unfold if_sem.
        right.
        split.
        {  tauto. }
        {  simpl. 
            tauto. }
     -     destruct a as [p c5].
           destruct p as [b0 c4].
           simpl.
           simpl in H2.
           unfold concat'.
           unfold concat' in H2.
           destruct H2 as [st4 [ek' [? ?]]].
           destruct H0.
           *  exists st4.
               exists ek'.
              split.
              {  unfold if_sem.
                 right.
                 simpl.
                 tauto.
              }
              tauto.
          *   exists st4.
               exists ek'.
              split.
              {  unfold if_sem.
                 right.
                 simpl.
                 tauto.
              }
             right.
             split.
             tauto.
             destruct H0 as [? [st5 ?]].
             exists st5.
             tauto.
  +  injection H0 as ? ?.
      injection H1 as ? ?.
      subst.
      simpl.
      simpl in H2.
      unfold ceval_LoopCond in H2.
      unfold concat_loop in H2.
      destruct H2.
      { destruct H0.
         induction H.
         +  induction s.
             -  simpl.
                simpl in H1.
                unfold concat' in H1.
                destruct H1 as [st4 [ek' [? ?]]].
                destruct H1.
                *  unfold skip_sem in H1.
                   unfold loop_sem.
                   exists (S O).
                   simpl.
                   destruct H1 as [? [? ?]].
                   subst.
                   tauto.
              *   assert (ek'=EK_Normal \/ ek'=EK_Cont).
                 { induction ek';tauto. }
                 destruct H1 as [? [st5 [? ?]]].
                 destruct H2.
                 ++  subst.
                        unfold skip_sem in H4.
                        destruct H4.
                        unfold loop_sem.
                        unfold loop_sem in H3.
                        destruct H3 as [n [? ?]].
                        exists (S n).
                        subst.
                        simpl.
                        split.
                        split.
                        left.
                        exists st4.
                        tauto.
                        tauto.
                        tauto.
                  ++ unfold loop_sem.
                        unfold loop_sem in H3.
                        destruct H3 as [n [? ?]].
                        exists (S n).
                        simpl.
                        unfold skip_sem in H4.
                        destruct H4.
                        subst.
                        split.
                        split.
                        right.
                        right.
                        exists st4.
                        tauto.
                        tauto.
                        reflexivity.
             -   destruct a as [[b' c1] c2].
                 simpl.
                 simpl in H1.
                 unfold concat' at 1 in H1.
                 destruct H1 as [st4 [ek' [? ?]]].
                 destruct H1.
                 *  destruct H1.
                    unfold concat',skip_sem in H2.
                    destruct H2 as [st5 [ek'' [[? ?] ?]]].
                    destruct H4.
                    ++  destruct H4.
                           subst.
                           discriminate.
                    ++  destruct H4 as [? [st1 [? ?]]].
                           unfold concat'.
                           subst.
                           exists st5.
                           exists EK_Normal.
                           split. 
                           {
                           unfold loop_sem.
                           exists (S O).
                           simpl.
                           tauto.
                           }
                      right.
                      split.
                      discriminate.
                      exists st1.
                      tauto.
                *  destruct H1 as [? [st1 [? ?]]].
                    unfold concat',skip_sem in H3.
                    destruct H3 as [st5 [ek'' [[? ?] ?]]].
                    destruct H5.
                    ++  destruct H5.
                           subst.
                           discriminate.
                    ++  subst.
                           destruct H5 as [? [st1 [? ?]]].
                           unfold concat'.
                           unfold loop_sem in H4.
                           destruct H4 as [n [? ?]].
                           clear H3 H6.
                           exists st5.
                           exists EK_Normal.
                           split.
                           {  pose proof (Loop_Condition _ _ _ _ _ _ H0 H1  H2 H).
                          tauto.
                          }
                          right.
                          split.
                          discriminate.
                          exists st1.
                          unfold loop_sem.
                          split.
                          exists n.
                          tauto.
                          tauto.
         +  unfold concat' in H1.
             destruct H1 as [st1 [ek' [? ?]]].
             admit.
                   }
      destruct H0.
      induction H.
      -  simpl.
      induction s.
      *  simpl.
         simpl in H1.
         unfold skip_sem in H1.
         unfold loop_sem.
         exists O.
         simpl.
         tauto.
      *  destruct a as [[st' c1 ]c2].
         simpl.
         simpl in H1.
         unfold concat',skip_sem in H1.
         unfold concat'.
         unfold loop_sem at 1.
         destruct H1 as [st4 [ek' [? ?]]].
         destruct H1.
         {  destruct H.
             destruct H1.
             subst.
             discriminate.  }
         {  destruct H.
             subst.
             destruct H1 as [? [st2 [? ?]]].
             exists st4.
             exists EK_Normal.
             split.
             {  exists O.
                simpl.
                tauto. }
             {  right.
                split.
                tauto.
                exists st2.
                tauto.
                }
             }
      -  admit.
  + injection H0 as ? ?.
      injection H1 as ? ?.
      subst.
      simpl.
      simpl in H2.
      pose proof (beval_preserve _ _ _  H).
      unfold ceval_LoopCond.
      simpl.
      pose proof (classic (beval b'' st2)).
      unfold ceval_LoopCond in H2.
      unfold concat_loop in H2.
       unfold concat_loop.
      destruct H1.
      -  assert(beval b' st2).
         { tauto. }
         destruct H2.
         *  destruct H2.
            left.
            split.
            tauto.
            simpl in H4.
            tauto.
          *  tauto.
      -  assert (~beval b' st2).
        {  tauto. }
        tauto.
  +   injection H0 as ? ?.
     injection H1 as ? ?.
     subst.
     simpl.
     simpl in H2.
     unfold concat_loop.
     simpl.
     tauto.
  + injection H0 as ? ?.
     injection H1 as ? ?.
     subst.
     simpl.
     unfold concat_loop.
     simpl.
     tauto.
  +  injection H0 as ? ?.
       injection H1 as ? ?.
       subst.
       simpl.
      unfold concat',skip_sem.
      exists st2.
      exists EK_Normal.
      split.
      split.
      reflexivity.
      reflexivity.
      right.
      unfold ceval_LoopCond in H2.
      unfold concat_loop in H2.
      destruct H2.
      -  destruct H as [? ?].
         split.
         discriminate.
         unfold concat' in H0.
         destruct H0 as [st4 [ek' [? ?]]].
         destruct H1.
         *  destruct H1.
            exists st4.
            unfold loop_sem.
            split.
            exists (S O).
            simpl.
            subst.
            tauto.
            tauto.
        *  destruct H1 as [? [st5 [? ?]]].
            exists st5.
            unfold loop_sem.
            assert(ek'=EK_Normal \/ ek'=EK_Cont).
            { induction ek';tauto. }
            split.
            destruct H4.
            { simpl in H2.
              unfold loop_sem in H2.
              destruct H2 as [n [? ?]].
              exists (S n).
              simpl.
              split.
              split.
              left.
              exists st4.
              subst.
              tauto.
              tauto.
              tauto.
              }
            { simpl in H2.
              unfold loop_sem in H2.
              destruct H2 as [n [? ?]].
              exists (S n).
              simpl.
              split.
              split.
              right.
              right.
              exists st4.
              subst.
              tauto.
              tauto.
              tauto.
            }
         tauto.
      -  simpl.
         destruct H as [? ?].
         split.
         discriminate.
         exists st2.
        unfold loop_sem.
        split.
        exists O.
        simpl.
        split.
        split.
        { reflexivity. }
        { tauto. }
        { reflexivity. }
        { tauto. }
  +   injection H0 as ? ?.
       injection H1 as ? ?.
       subst.
       induction s.
      -   simpl.
          simpl in H2.
          unfold concat'.
          exists st2.
          exists EK_Break.
          split.
          *  apply Break_Condition.
              tauto.
          *  left.
              split.
              reflexivity.
              tauto.
       -   destruct a as [p c5].
           destruct p as [b0 c4].
           simpl.
           simpl in H2.
           unfold concat' at 1.
           exists st2.
           exists EK_Break.
           split.
           *  apply Break_Condition.
               tauto.
           *  left.
               split.
               { reflexivity. }
               {  tauto. }
  +  injection H1 as ? ?.
      injection H0 as ? ?.
      subst.
      unfold ceval_LoopCond in H2.
      simpl.
      unfold concat_loop in H2.
      destruct H2.
      -  destruct H0.
         unfold concat'.
         unfold concat' in H1.
         destruct H1 as [st4 [ek' [? ?]]].
         destruct H2.
         *  destruct H2.
             subst.
             exists st2.
             exists EK_Cont.
             pose proof (Cont_Condition _ st2 H).
             split.
             tauto.
             right.
             split.
            discriminate.
             exists st4.
             unfold loop_sem.
             split.
             exists (S O).
             simpl.
             simpl in H1.
             split.
             tauto.
             reflexivity.
             tauto.
         *  destruct H2 as [? [st5 [? ?]]].
              pose proof (Cont_Condition _ st2 H).
              exists st2.
              exists EK_Cont.
              split.
              tauto.
              right.
              split.
              discriminate.
              exists st5.
              simpl in H3.
              assert(ek'=EK_Normal\/ ek'=EK_Cont).
              { induction ek';tauto. }
              split.
              unfold loop_sem in H3.
              destruct H3 as [n [? ?]].
              exists (S n).
              destruct H6.
              {  simpl.
                  split.
                  split.
                  left.
                  subst.
                  exists st4.
                  tauto.
                  tauto.
                  reflexivity.  }
              {  simpl.
                  split.
                  split.
                  right.
                  right.
                  subst.
                  exists st4.
                  tauto.
                  tauto.
                  reflexivity.
                }
                tauto.
       -  unfold concat'.
          destruct H0.
          exists st2.
          pose proof (Cont_Condition _ st2 H).
          exists EK_Cont.
          split.
          tauto.
          right.
          split.
          discriminate.
          exists st2.
          split.
          unfold loop_sem.
          exists O.
          simpl.
          split.
          split.
          reflexivity.
          tauto.
          reflexivity.
          tauto.
  Admitted.

Theorem semantic_equiv_normal2: forall (c:com')  st1 st2,
multi_cstep (c ,st1) (CNormal nil CSkip ,st2)->(ceval' c st1 EK_Normal st2) .
Proof.
  intros.
  remember (CNormal nil Skip) as c' eqn:H0.
  revert H0.  induction_1n H.  simpl; intros; subst.
  + simpl.
    unfold skip_sem.
    split.
    -  reflexivity.
    -  reflexivity.
  + pose proof ceval'_preserve _ _ _ _ H st2.
     intros.
     pose proof (IH H2).
     specialize (H1 EK_Normal H3).
     tauto.
Qed.

Theorem semantic_equiv_break2: forall (c:com')  st1 st2,
(exists c', multi_cstep (c ,st1) (CNormal nil c' ,st2)/\start_with_break c')->(ceval' c st1 EK_Break  st2) .
Proof.
  intros.
  destruct H as [c' [?  ?]].
  remember (CNormal nil c') as c1 eqn:H1.
  revert H1.  induction_1n H.  simpl; intros; subst.
  + simpl.
     pose proof (Break_Condition _ st1 H0).
     tauto.
  +  pose proof ceval'_preserve _ _ _ _ H st2.
      intros.
      pose proof (IH H3).
     specialize (H2 EK_Break H4).
     tauto.
Qed.

Theorem semantic_equiv_cont2: forall (c:com')  st1 st2,
(exists c', multi_cstep (c ,st1) (CNormal nil c' ,st2)/\start_with_cont c')->(ceval' c st1 EK_Cont  st2) .
Proof.
  intros.
  destruct H as [c' [?  ?]].
  remember (CNormal nil c') as c1 eqn:H1.
  revert H1.  induction_1n H.  simpl; intros; subst.
  + simpl.
     pose proof (Cont_Condition _ st1 H0).
     tauto.
  +  pose proof ceval'_preserve _ _ _ _ H st2.
      intros.
      pose proof (IH H3).
     specialize (H2 EK_Cont H4).
     tauto.
Qed.