Require Import Reals.
Require Import K7Graph. 

Section AbstractStrategy.

Variable probability : 
    Vertex -> Vertex -> Edge -> Edge -> R.

Hypothesis zero_if_alice_invalid:
    forall a b e f,
        part_of a e = false  ->
        probability a b e f = 0%R.

Hypothesis zero_if_bob_invalid:
    forall a b e f,
        part_of b f = false  ->
        probability a b e f = 0%R.

Hypothesis zero_if_incompatible:
    forall a b e f,
        edge_equal e f = false ->
        disjoint e f = false ->
        probability a b e f = 0%R.

        (*now we create a theorem that looks at losing cases-- that is why we assume the selected outputs lose the game.*)
Theorem losing_probability_zero :
  forall a b e f,
    wins a b e f = false ->
    probability a b e f = 0%R.
Proof.
  intros a b e f Hlose. (*choose any vertices and edges and call the assumption that they lose Hlose*)
  unfold wins in Hlose. (*replace the name wins with its actual formula*)

  destruct (part_of a e) eqn:HA. (*case analysis on whether Alice's edge is valid*)

  - (* Alice's edge is valid *)
    destruct (part_of b f) eqn:HB.

    + (* Bob's edge is valid *)
      destruct (edge_equal e f) eqn:HE.

      * (* Edges are identical, so this cannot be losing *)
      (*the two lines above identify the identical case as winning so it does not belong in this branch*)
        simpl in Hlose.
        discriminate.

      * (* Edges are different *)
        destruct (disjoint e f) eqn:HD.

        -- (* Different but disjoint: winning, so cannot be losing *)
        (*these lines above identify the disjoint case as winning so it does not belong in this branch*)
           simpl in Hlose. (*simpl evaluates the bollean order for all cases above*)
           discriminate.

        -- (* Different and intersecting: probability zero *)
        (*these lines above identify the intersecting case as having zero probability so it does belong in this branch*)
           apply zero_if_incompatible. (*use above zero_if_incompatible to verfiy probability of 0*)
           ++ exact HE. (*proves edges are different*)
           ++ exact HD. (*proves edges are not disjoint*)

    + (* Bob's edge is invalid *)
      apply zero_if_bob_invalid.
      exact HB.

  - (* Alice's edge is invalid *)
    apply zero_if_alice_invalid.
    exact HA.
Qed.

End AbstractStrategy.