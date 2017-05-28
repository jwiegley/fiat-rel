Require Import coqrel.LogicalRelations.
Require Import Fiat.ADT Fiat.ADTNotation.
Require Import Coq.Sets.Ensembles.
Require Import Coq.Program.Program.
Require Import Fiat.ADTRefinement.
Require Import Fiat.ADTRefinement.BuildADTRefinements.

Lemma If_Then_Else_fst : forall p A B (a b : A * B),
  fst (If p Then a Else b) = If p Then (fst a) Else (fst b).
Proof. intros; destruct p; trivial. Qed.

Lemma If_Then_Else_snd : forall p A B (a b : A * B),
  snd (If p Then a Else b) = If p Then (snd a) Else (snd b).
Proof. intros; destruct p; trivial. Qed.

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

Notation "translation[ H ]" := (@translation _ _ _ _ H)
  (at level 9, format "translation[ H ]").
Notation "relationship[ H ]" := (@relationship _ _ _ _ H)
  (at level 9, format "relationship[ H ]").

Corollary rewrite_rel `{AbsR : rel X Y} {x : X} {y : Y} :
  AbsR x y -> Related x y AbsR.
Proof. intro H; apply H. Qed.

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

Program Instance RelatedTheory_Empty_set :
  RelatedTheory (Empty_set A) EnsembleAsList_AbsR := {
  translation := []
}.
Next Obligation. intro x; split; inversion 1. Qed.

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

Program Instance RelatedTheory_If_Then_Else
        (b : bool) (t e : Ensemble A)
        (Ht : RelatedTheory t EnsembleAsList_AbsR)
        (He : RelatedTheory e EnsembleAsList_AbsR) :
  RelatedTheory (If b Then t Else e) EnsembleAsList_AbsR := {
  translation := if b then translation[Ht]
                      else translation[He]
}.
Next Obligation.
  intro x; split; intros;
  destruct Ht, He; simpl in *;
  unfold Related in *; subst;
  destruct b; simpl in *;
  try apply relationship0;
  try apply relationship1;
  assumption.
Qed.

Ltac translate :=
  match goal with
  | [ |- refine (ret _) _ ] => solve [ finish honing ]
  | [ H : Related _ _ _ |- refine { x : _ | ?R ?X x } _ ] =>
    refine pick val (@translation _ _ X R _); [|try apply relationship];
    simpl; try simplify with monad laws; translate
  | [ H : Related _ _ _ |- refine (_ <- { x : _ | ?R ?X x }; _) _ ] =>
    refine pick val (@translation _ _ X R _); [|try apply relationship];
    simpl; try simplify with monad laws; translate
  | [ H : Related _ _ _ |- refine (_ <- ?X; _) _ ] =>
    rewrite (@relationship _ _ X _ _); simpl;
    simpl; try simplify with monad laws; translate
  | [ |- refine { x : _ | ?R ?X x } _ ] =>
    refine pick val (@translation _ _ X R _); [|try apply relationship];
    simpl; try simplify with monad laws; translate
  | [ H : Related _ _ _ |- _ ] => idtac
  | [ H : ?R _ _ |- _ ] => apply rewrite_rel in H; translate
  end; simpl.

Theorem impl : FullySharpened spec.
Proof.
  start sharpening ADT.
  hone representation using EnsembleAsList_AbsR;

  (* See if our known theories can resolve things for us. *)
  try simplify with monad laws; try translate.

  {
    rewrite refine_If_Then_Else_ret;
    simplify with monad laws; simpl.
    rewrite If_Then_Else_fst; simpl.
    translate.
    rewrite If_Then_Else_snd; simpl.
    replace (If List.existsb (A_eq_dec d) r_n Then () Else ()) with ()
      by (destruct (List.existsb _ _); auto).
    finish honing.
  }

  finish_SharpeningADT_WithoutDelegation.
Defined.

End Refine.
