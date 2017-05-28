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
