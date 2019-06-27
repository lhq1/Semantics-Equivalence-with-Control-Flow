# Semantic Equivalence for Programs with Break and Continue

Hongqing Liu

Weidong Wang

Shenghao Nie

Zicheng Pan



## Compile Order

1. Imp.v
2. Lemmas_of_Assertion_Sub_Spec_Lemma.v
3. Assertion_Sub_Spec_Lemma.v
4. Hoare_Soundness_with_Break_and_Continue.v
5. Sematics_Equiv1.v
6. Sematics_Equiv2.v



## Semantic Equivalence

### Proof Step:

1. denotation -> small step (Sematics_Equiv1.v):

   * line 9-810, some useful lemmas.

   * line 813-1011, main proof process (induction 7 coms and 3 exit_kinds).

2. small step -> denotation (Sematics_Equiv2.v):
   * line 6-36, some new definitions.
   * line 38-340,some useful lemmas.
   * line 343-989,the main process of ceval’_preserve (induction 14 cstep, some branches are proved as lemma).
   * line 991-1041, the proof of our goals.



## Hoare Soundness

### Proof Step:

1. Hoare Sequence

2. Hoare Skip

3. Hoare If

4. Hoare While

5. Hoare Asgn Bwd

6. Hoare Consequence

7. Hoare Break

8. Hoare Continue

 These proofs have been included in the file "Hoare_Soundness_with_Break_and_Continue.v".

### Lemma Required:

Assertion_sub_spec, which is used in the proof of Hoare_Asgn_Bwd_Sound.  **(Unfinished)**

Firstly, prove the lemma below, which has been finished.

```
Lemma Assertion_sub_spec_1 : forall st La (P: Assertion) (E: aexp'),
  (st, La) |== P <-> (st, La) |== (rename_all E P).
```

Secondly, prove the lemma below, which has not been finished.

```
Lemma Assertion_sub_spec_2 : forall st1 st2 La (P: Assertion) (X: var) (E: aexp'),
  st2 X = aexp'_denote (st1, La) E ->
  (forall Y : var, X <> Y -> st1 Y = st2 Y) ->
  (st1, La) |== naive_sub X E (rename_all E P) <-> (st2, La) |== (rename_all E P).
```

Use the transitivity of equivalence relationship to finish the proof.
