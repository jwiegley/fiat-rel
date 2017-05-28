Require Import coqrel.LogicalRelations.
Require Import Fiat.ADT Fiat.ADTNotation.
Require Import Coq.Sets.Ensembles.
Require Import Coq.Program.Program.
Require Import Fiat.ADTRefinement.
Require Import Fiat.ADTRefinement.BuildADTRefinements.

Definition comp_rel (X X' : Type) (AbsR : rel X X') : rel (Comp X) (Comp X') :=
  fun cX cX' => (forall x,  cX  x  -> exists x', AbsR x x' /\ cX' x') /\
                (forall x', cX' x' -> exists x,  AbsR x x' /\ cX  x).

Theorem refine_rel (X X' : Type)
        (AbsR : rel X X') f f' g g'
  (functional : forall x y z, AbsR x y -> AbsR x z -> y = z) :
  Related f f' (comp_rel AbsR) ->
  Related g g' (comp_rel AbsR) ->
  refine f g -> refine f' g'.
Proof.
  repeat intro.
  destruct H0.
  destruct (H3 v H2) as [? [? ?]].
  destruct H.
  specialize (H1 x H5).
  destruct (H x H1) as [? [? ?]].
  pose proof (functional _ _ _ H4 H7); subst.
  apply H8.
Qed.

Section Refine.

Variable A : Type.

Definition spec : ADT _ := Def ADT {
  rep := Ensemble A,

  Def Constructor0 "new" : rep :=
    ret (Empty_set _),,

  Def Method1 "insert" (r : rep) (x : A) : rep * unit :=
    b <- { b | decides b (In A r x) };
    If b
    Then ret (r, tt)
    Else ret (Add _ r x, tt),

  Def Method1 "delete" (r : rep) (x : A) : rep * unit :=
    ret (Subtract _ r x, tt)

}%ADTParsing.

Variable A_eq_dec : forall x y : A, {x = y} + {x <> y}.

Definition EnsembleAsList_AbsR : rel (Ensemble A) (list A) :=
  fun r_o r_n =>
    forall x, In _ r_o x <-> List.existsb (A_eq_dec x) r_n.

Class RelatedTheory {A B : Type} (x : A) (AbsR : A -> B -> Prop) := {
  translation : B;
  relationship : Related x translation AbsR
}.

Arguments relationship {_ _ _ _ _} /.

Program Instance RelatedTheory_AbsR {A B : Type} (x : A) (y : B)
        (AbsR : A -> B -> Prop) : Related x y AbsR ->
  RelatedTheory x AbsR := {
  translation := y
}.

Program Instance RelatedTheory_decides_In {es : Ensemble A} (d : A) :
  RelatedTheory es EnsembleAsList_AbsR ->
  RelatedTheory { b : bool | decides b (In A es d) } refine := {
  translation := ret (List.existsb (A_eq_dec d) translation)
}.
Next Obligation.
  unfold Related.
  apply refine_pick; intros.
  inversion H0; subst; clear H0.
  destruct H; simpl.
  specialize (relationship0 d).
  unfold decides, If_Then_Else.
  destruct (List.existsb _ _); intuition.
Qed.

Program Instance RelatedTheory_Add_cons {xs : list A} :
  Related es xs EnsembleAsList_AbsR ->
  RelatedTheory (Add A es x) EnsembleAsList_AbsR := {
  translation := cons x xs
}.
Next Obligation.
  intros.
  constructor; intros.
    specialize (H x0).
    inversion H0; subst.
      simpl; intuition.
    simpl.
    inversion H1; subst.
    apply Bool.orb_true_iff; left.
    destruct (A_eq_dec x0 x0); intuition.
  simpl in H0.
  apply Bool.orb_true_iff in H0.
  destruct H0.
    destruct (A_eq_dec x0 x); intuition; subst.
    right; constructor.
  left.
  apply H, H0.
Qed.

Program Instance RelatedTheory_Subtract_uncons {xs : list A} :
  Related es xs EnsembleAsList_AbsR ->
  RelatedTheory (Subtract A es x) EnsembleAsList_AbsR := {
  translation := List.remove A_eq_dec x xs
}.
Next Obligation.
  intros.
  constructor; intros.
    specialize (H x0).
    inversion H0; subst; clear H0.
    intuition.
    apply List.existsb_exists.
    apply List.existsb_exists in H.
    destruct H, H.
    exists x1.
    destruct (A_eq_dec x0 x1); intuition; subst.
    assert (x <> x1).
      unfold not; intros.
      contradiction H2; subst.
      constructor.
Admitted.

Corollary rewrite_rel `{AbsR : rel X Y} {x : X} {y : Y} :
  AbsR x y -> Related x y AbsR.
Proof. intro H; apply H. Qed.

Ltac translate :=
  try match goal with
  | [ H : ?R _ _ |- refine (_ <- ?X; _) _ ] =>
    apply rewrite_rel in H;
    rewrite (@relationship _ _ X _ _); simpl;
    try simplify with monad laws; translate
  end.

Lemma If_Then_Else_fst : forall p A B (a b : A * B),
  fst (If p Then a Else b) = If p Then (fst a) Else (fst b).
Proof. intros; destruct p; trivial. Qed.

Lemma If_Then_Else_snd : forall p A B (a b : A * B),
  snd (If p Then a Else b) = If p Then (snd a) Else (snd b).
Proof. intros; destruct p; trivial. Qed.

Theorem impl : FullySharpened spec.
Proof.
  start sharpening ADT.
  hone representation using EnsembleAsList_AbsR;

  (* See if our known theories can resolve things for us. *)
  try simplify with monad laws; simpl;
  try translate.

  (* constructor: new *)
  {
    (* NOTE: Although [finish honing] might solve this goal directly, it
      would generate a new subgoal at the end (from the call to
      [finish_SharpeningADT_WithoutDelegation]), requiring us to prove that
      [Empty_set] is equivalent to an empty list. Thus, the objective in
      these proofs is not just to complete the subgoals, but to reduce the
      goal to its simplest possible form, expressed purely in terms of our
      concrete representation (in this case, lists). *)

    refine pick val nil.
      finish honing.
    split; intros;
    inversion H0.
  }

  {
    rewrite refine_If_Then_Else_ret;
    simplify with monad laws; simpl.
    rewrite If_Then_Else_fst; simpl.
    apply rewrite_rel in H0.
    rewrite (@relationship _ _ {b : bool | decides b (In A r_o d)} _ _).
    unfold Related in H1.
    rewrite H1.
    unfold translation; simpl.
    simpl in X.
    remember {b : bool | decides b (In A r_o d)} as p.

  finish_SharpeningADT_WithoutDelegation.
Defined.

End Refine.