Require Import K7Graph.

Require Import QuantumLib.Matrix.

Require Import QuantumLib.VectorStates.

Require Import QuantumLib.Quantum.

Require Import QuantumLib.Eigenvectors.

Require Import QuantumLib.Measurement.

Require Import K7Strategy.

Require Import QuantumLib.CauchySchwarz.


Local Open Scope R_scope.
Local Open Scope C_scope.
Local Open Scope nat_scope.

Definition omega : C :=
  ((-1 / 2)%R, (sqrt 3 / 2)%R).

Definition omega2 : C :=
  ((-1 / 2)%R, (- sqrt 3 / 2)%R).

Example omega_sum_zero :
(*prove 1+w+w^2=0*)
  (C1 + omega + omega2)%C = C0.
Proof.
  unfold omega, omega2.
  lca.
Qed.

(*Prove that omega is the conjugate of omega2 and vice versa*)
Example omega_conjugate :
  omega^* = omega2.
Proof.
  unfold omega, omega2, Cconj.
  lca.
Qed.

Example omega2_conjugate :
  omega2^* = omega.
Proof.
  unfold omega, omega2, Cconj.
  lca.
Qed.

(*defines real number 1/2 which RtoC converts to complex because QuantumLib vectors must contain complex entities*)
Definition half : C :=
    RtoC (1 / 2)%R.

    (*vectors assigned to edges- collumn matrix where every entry is a complex number*)
Definition vector6
    (a0 a1 a2 a3 a4 a5 : C) : Vector 6 :=
  fun row col =>
    match row, col with
    | 0, 0 => a0
    | 1, 0 => a1
    | 2, 0 => a2
    | 3, 0 => a3
    | 4, 0 => a4
    | 5, 0 => a5
    | _, _ => C0
    end.

Definition v1: Vector 6 := e_i 0.
Definition v2: Vector 6 := e_i 1.
Definition v3: Vector 6 := e_i 2.
Definition v4: Vector 6 := e_i 3.
Definition v5: Vector 6 := e_i 4.
Definition v6: Vector 6 := e_i 5.

Definition v7: Vector 6 :=
    vector6 C0 C0 half half half half. 

(*shortcut to define w/2 and w^2/2-- will be used to define future edge vectors*)
Definition half_omega : C :=
  (half * omega)%C.

Definition half_omega2 : C :=
  (half * omega2)%C.

(*define other edge vectors*)
Definition v8 : Vector 6 :=
  vector6 C0 half C0 half half_omega half_omega2.

Definition v9 : Vector 6 :=
  vector6 C0 half half C0 half_omega2 half_omega.

Definition v10 : Vector 6 :=
  vector6 C0 half half_omega half_omega2 C0 half.

Definition v11 : Vector 6 :=
  vector6 C0 half half_omega2 half_omega half C0.

Definition v12 : Vector 6 :=
  vector6 half C0 C0 half half_omega2 half_omega.

Definition v13 : Vector 6 :=
  vector6 half C0 half C0 half_omega half_omega2.

Definition v14 : Vector 6 :=
  vector6 half C0 half_omega2 half_omega C0 half.

Definition v15 : Vector 6 :=
  vector6 half C0 half_omega half_omega2 half C0.

Definition v16 : Vector 6 :=
  vector6 half half C0 C0 half half.

Definition v17 : Vector 6 :=
  vector6 half_omega half_omega2 C0 half C0 half.

Definition v18 : Vector 6 :=
  vector6 half_omega2 half_omega C0 half half C0.

Definition v19 : Vector 6 :=
  vector6 half_omega2 half_omega half C0 C0 half.

Definition v20 : Vector 6 :=
  vector6 half_omega half_omega2 half C0 half C0.

Definition v21 : Vector 6 :=
  vector6 half half half half C0 C0.

  (*match each edge vector to an edge*)
  Definition edge_vector (e : Edge) : Vector 6 :=
    match ordered_endpoints e with
    | (V0, V1) => v1
    | (V0, V2) => v2
    | (V0, V3) => v3
    | (V0, V4) => v4
    | (V0, V5) => v5
    | (V0, V6) => v6
    | (V1, V2) => v7
    | (V1, V3) => v8
    | (V1, V4) => v9
    | (V1, V5) => v10
    | (V1, V6) => v11
    | (V2, V3) => v12
    | (V2, V4) => v13
    | (V2, V5) => v14
    | (V2, V6) => v15
    | (V3, V4) => v16
    | (V3, V5) => v17
    | (V3, V6) => v18
    | (V4, V5) => v19
    | (V4, V6) => v20
    | (V5, V6) => v21
    | _ => Zero
    end.

  (*verification of edge_vector*)
Example edge12_vector_is_v7 :
  edge_vector E12 = v7.
Proof.
  reflexivity.
Qed.

Example reversed_E12_vector_is_v7 :
  edge_vector (V2, V1) = v7.
Proof.
  reflexivity.
Qed.

(* complex conjugate of a vector *)
Definition vector_conj {n} (v : Vector n) : Vector n :=
  fun i j => (v i j)^*.


(* unnormalized maximally entangled state
   |00> + |11> + ... + |55> *)
Definition phi6_unscaled : Vector 36 :=
  Mplus
    (basis_vector 6 0 ⊗ basis_vector 6 0)
    (Mplus
      (basis_vector 6 1 ⊗ basis_vector 6 1)
      (Mplus
        (basis_vector 6 2 ⊗ basis_vector 6 2)
        (Mplus
          (basis_vector 6 3 ⊗ basis_vector 6 3)
          (Mplus
            (basis_vector 6 4 ⊗ basis_vector 6 4)
            (basis_vector 6 5 ⊗ basis_vector 6 5))))).


(* normalized shared state by dividing by 1/sqrt6*)
Definition phi6 : Vector 36 :=
  scale (RtoC (1 / sqrt 6)%R) phi6_unscaled.

  (* joint Alice/Bob measurement vector for edges e and f *)
Definition joint_measurement_vector
    (e f : Edge) : Vector 36 :=
  vector_conj (edge_vector e) ⊗ edge_vector f.


(* probability of jointly obtaining edges e and f
   from the shared state |Phi_6> *)
Definition quantum_edge_probability
    (e f : Edge) : R :=
  probability_of_outcome
    (joint_measurement_vector e f)
    phi6.

(*proof that v7 is normalized*)
Example v7_normalized :
  inner_product v7 v7 = C1.
Proof.
  unfold inner_product, Mmult, adjoint, v7, vector6, half.
  simpl.
  lca.
Qed.

(*prove that w has magnitude 1*)
Example omega_unit_length :
  (omega^* * omega)%C = C1.
Proof.
  unfold omega, Cconj, Cmult.
  apply c_proj_eq.

  - simpl.
    assert (Hs : (sqrt 3 * sqrt 3)%R = 3%R).
    {
      apply sqrt_def.
      lra.
    }
    nra.

  - simpl.
    ring.
Qed.

(*Generalize the normalization proof-- first proving that norms of 1/2, w/2 and w^2/2 are 1/4*)
Lemma half_norm :
  (half^* * half)%C = RtoC (1 / 4)%R.
Proof.
  unfold half.
  lca.
Qed.

Lemma half_omega_norm :
    (half_omega^* * half_omega)%C = RtoC (1 / 4)%R.
Proof.
    unfold half_omega, half, omega, RtoC, Cconj, Cmult.
    apply c_proj_eq.

    - simpl. 
      assert (Hs : (sqrt 3 * sqrt 3)%R = 3%R).
      {
        apply sqrt_def.
        lra.
      }
      nra.

    - simpl. 
      ring. 
Qed.

Lemma half_omega2_norm :
    (half_omega2^* * half_omega2)%C = RtoC (1 / 4)%R.
Proof.
    unfold half_omega2, half, omega2, RtoC, Cconj, Cmult.
    apply c_proj_eq. (*c_proj_eq is a QuantumLib defined function that proves equality of complex numbers *)

    -simpl.
     assert (Hs : (sqrt 3 * sqrt 3)%R = 3%R).
     {
       apply sqrt_def. (*apply sqrt_def because lra can only understand linear variables*)
       lra.
     }
     nra.

     - simpl.
     ring. (*ring solves polynomials after simplification*)
Qed.

(*Using those lemmas to prove normalization of v8*)
Example v8_normalized :
  inner_product v8 v8 = C1.
Proof.
    unfold inner_product, Mmult, adjoint, v8, vector6.
    simpl.
    repeat rewrite half_norm.
    repeat rewrite half_omega_norm.
    repeat rewrite half_omega2_norm.
    lca.
Qed.

(*package that entire proof*)
Ltac prove_normalized v := (*Ltac creates a function for you*)
  unfold inner_product, Mmult, adjoint, v, vector6;
  simpl;
  repeat rewrite half_norm;
  repeat rewrite half_omega_norm;
  repeat rewrite half_omega2_norm;
  lca.

(*prove normalization of all edge vectors*)
Example v9_normalized :
  inner_product v9 v9 = C1.
Proof.
  prove_normalized v9.
Qed.

Example v10_normalized :
  inner_product v10 v10 = C1.
Proof.
  prove_normalized v10.
Qed.

Example v11_normalized :
  inner_product v11 v11 = C1.
Proof.
  prove_normalized v11.
Qed.

Example v12_normalized :
  inner_product v12 v12 = C1.
Proof.
  prove_normalized v12.
Qed.

Example v13_normalized :
  inner_product v13 v13 = C1.
Proof.
  prove_normalized v13.
Qed.

Example v14_normalized :
  inner_product v14 v14 = C1.
Proof.
  prove_normalized v14.
Qed.

Example v15_normalized :
  inner_product v15 v15 = C1.
Proof.
  prove_normalized v15.
Qed.

Example v16_normalized :
  inner_product v16 v16 = C1.
Proof.
  prove_normalized v16.
Qed.

Example v17_normalized :
  inner_product v17 v17 = C1.
Proof.
  prove_normalized v17.
Qed.

Example v18_normalized :
  inner_product v18 v18 = C1.
Proof.
  prove_normalized v18.
Qed.

Example v19_normalized :
  inner_product v19 v19 = C1.
Proof.
  prove_normalized v19.
Qed.

Example v20_normalized :
  inner_product v20 v20 = C1.
Proof.
  prove_normalized v20.
Qed.

Example v21_normalized :
  inner_product v21 v21 = C1.
Proof.
  prove_normalized v21.
Qed.

(*package the orthogonality proof*)
Ltac prove_orthogonal v w :=
    unfold inner_product, Mmult, adjoint, v, w, e_i, vector6,
        half, half_omega2,
        half_omega, omega, omega2;
    simpl;
    apply c_proj_eq; (*we need c_proj_eq here as products of sqrts that lca cannot resolve might be present-- that is why we need the semicolons after simpl because although lca splits the solving of complex and real parts, c_proj_eq must be told to do that through ;*)
    simpl;
    try ring; (*try: if it works, great! if it doesn't, move on*)
    try (assert (Hs : (sqrt 3 * sqrt 3)%R = 3%R); [apply sqrt_def; lra | nra]).

(*defining basis matrix*)
Definition basis6
    (c0 c1 c2 c3 c4 c5 : Vector 6) : Matrix 6 6 :=
    fun row col =>
        match col with
        | 0 => c0 row 0
        | 1 => c1 row 0
        | 2 => c2 row 0
        | 3 => c3 row 0
        | 4 => c4 row 0
        | 5 => c5 row 0
        | _ => C0
        end.

        (*building specific bases*)
Definition B0: Matrix 6 6 :=
    basis6 v1 v2 v3 v4 v5 v6.

Definition B1 : Matrix 6 6 :=
  basis6 v1 v7 v8 v9 v10 v11.

Definition B2 : Matrix 6 6 :=
  basis6 v2 v7 v12 v13 v14 v15.

Definition B3 : Matrix 6 6 :=
  basis6 v3 v8 v12 v16 v17 v18.

Definition B4 : Matrix 6 6 :=
  basis6 v4 v9 v13 v16 v19 v20.

Definition B5 : Matrix 6 6 :=
  basis6 v5 v10 v14 v17 v19 v21.

Definition B6 : Matrix 6 6 :=
  basis6 v6 v11 v15 v18 v20 v21.

(*matches register measurment in each of the measurement basis*)
Definition decode_outcome (v : Vertex) (k : nat) : option Edge :=
  match v, k with
  | V0, 0 => Some (V0, V1)
  | V0, 1 => Some (V0, V2)
  | V0, 2 => Some (V0, V3)
  | V0, 3 => Some (V0, V4)
  | V0, 4 => Some (V0, V5)
  | V0, 5 => Some (V0, V6)

  | V1, 0 => Some (V0, V1)
  | V1, 1 => Some (V1, V2)
  | V1, 2 => Some (V1, V3)
  | V1, 3 => Some (V1, V4)
  | V1, 4 => Some (V1, V5)
  | V1, 5 => Some (V1, V6)

  | V2, 0 => Some (V0, V2)
  | V2, 1 => Some (V1, V2)
  | V2, 2 => Some (V2, V3)
  | V2, 3 => Some (V2, V4)
  | V2, 4 => Some (V2, V5)
  | V2, 5 => Some (V2, V6)

  | V3, 0 => Some (V0, V3)
  | V3, 1 => Some (V1, V3)
  | V3, 2 => Some (V2, V3)
  | V3, 3 => Some (V3, V4)
  | V3, 4 => Some (V3, V5)
  | V3, 5 => Some (V3, V6)

  | V4, 0 => Some (V0, V4)
  | V4, 1 => Some (V1, V4)
  | V4, 2 => Some (V2, V4)
  | V4, 3 => Some (V3, V4)
  | V4, 4 => Some (V4, V5)
  | V4, 5 => Some (V4, V6)

  | V5, 0 => Some (V0, V5)
  | V5, 1 => Some (V1, V5)
  | V5, 2 => Some (V2, V5)
  | V5, 3 => Some (V3, V5)
  | V5, 4 => Some (V4, V5)
  | V5, 5 => Some (V5, V6)

  | V6, 0 => Some (V0, V6)
  | V6, 1 => Some (V1, V6)
  | V6, 2 => Some (V2, V6)
  | V6, 3 => Some (V3, V6)
  | V6, 4 => Some (V4, V6)
  | V6, 5 => Some (V5, V6)

  | _, _ => None
  end.

(* verification of decode_outcome*)
Example decode_V2_1 :
  decode_outcome V2 1 = Some (V1, V2).
Proof.
  reflexivity.
Qed.

Example decode_invalid_outcome :
  decode_outcome V2 6 = None.
Proof.
  reflexivity.
Qed.

(*Match input vertex to basis*)
Definition vertex_basis (v : Vertex) : Matrix 6 6 :=
  match v with
  | V0 => B0
  | V1 => B1
  | V2 => B2
  | V3 => B3
  | V4 => B4
  | V5 => B5
  | V6 => B6
  end.

Example V2_outcome1_matches_v7 :
  get_col (vertex_basis V2) 1 = v7.
Proof.
  unfold get_col, vertex_basis, B2, basis6.

  apply functional_extensionality.
  intro x.

  apply functional_extensionality.
  intro y.

  destruct y.
  - reflexivity.
  - unfold v7, vector6.
    simpl.
    destruct x as [| [| [| [| [| [| x]]]]]];
    reflexivity.
Qed.


(* Alice uses the conjugate basis, so her basis change is B^T *)
Definition alice_basis_change (a : Vertex) : Matrix 6 6 :=
  transpose (vertex_basis a).


(* Bob uses the original basis, so his basis change is B^\dagger *)
Definition bob_basis_change (b : Vertex) : Matrix 6 6 :=
  adjoint (vertex_basis b).


(* combine Alice and Bob's basis changes *)
Definition joint_basis_change
    (a b : Vertex) : Matrix 36 36 :=
  kron
    (alice_basis_change a)
    (bob_basis_change b).


(* apply both basis changes to phi6 *)
Definition post_basis_state
    (a b : Vertex) : Vector 36 :=
  Mmult
    (joint_basis_change a b)
    phi6.


(* computational-basis outcome j for Alice and k for Bob *)
Definition raw_outcome_vector
    (j k : nat) : Vector 36 :=
  basis_vector 6 j ⊗ basis_vector 6 k. (*need to tensor as we tensored the measurment basis before*)

(* probability of measuring outcomes j and k *)
Definition raw_outcome_probability
    (a b : Vertex) (j k : nat) : R :=
  probability_of_outcome
    (raw_outcome_vector j k)
    (post_basis_state a b).

(* move the basis change to the raw outcome so we can identify its edge vectors *)
Lemma raw_outcome_probability_moved :
  forall a b j k,
  raw_outcome_probability a b j k =
  probability_of_outcome
    (Mmult
      (adjoint (joint_basis_change a b))
      (raw_outcome_vector j k))
    phi6.
Proof.
  intros a b j k.
  unfold raw_outcome_probability,
         probability_of_outcome,
         post_basis_state.

  rewrite inner_product_adjoint_r.
  reflexivity.
Qed.

(* simplify the adjoint of the combined basis change *)
Lemma joint_basis_change_adjoint :
  forall a b,
    adjoint (joint_basis_change a b) =
    kron
      (adjoint (alice_basis_change a))
      (vertex_basis b).
Proof.
  intros a b.
  unfold joint_basis_change.

  transitivity
    (kron
      (adjoint (alice_basis_change a))
      (adjoint (bob_basis_change b))).

  - apply kron_adjoint.

  - unfold bob_basis_change.
    rewrite adjoint_involutive.
    reflexivity.
Qed.

(* split the moved outcome into Alice's part and Bob's part *)
Lemma moved_raw_outcome_factors :
  forall a b j k,
    Mmult
      (adjoint (joint_basis_change a b))
      (raw_outcome_vector j k)
    =
    kron
      (Mmult
        (adjoint (alice_basis_change a))
        (basis_vector 6 j))
      (Mmult
        (vertex_basis b)
        (basis_vector 6 k)).
Proof.
  intros a b j k.
  rewrite joint_basis_change_adjoint.
  unfold raw_outcome_vector.

  apply (kron_mixed_product'
    6 6 6 1
    6 6 6 1
    36 36 1).

  all: reflexivity.
Qed.

(* check whether raw measurement outcomes win the game *)
Definition raw_wins
    (a b : Vertex) (j k : nat) : bool :=
  match decode_outcome a j, decode_outcome b k with
  | Some e, Some f => wins a b e f
  | _, _ => false
  end.

(*proves whenever outcome k at vertex v decodes to edge e, column k of that vertex’s measurement basis is exactly the vector assigned to edge e*)
Lemma decode_outcome_matches_basis :
  forall v k e,
    decode_outcome v k = Some e ->
    forall row,
      vertex_basis v row k = edge_vector e row 0.
Proof.
  intros v k e Hdecode row.

  destruct v;
  destruct k as [| [| [| [| [| [| k]]]]]];
  simpl in Hdecode |-;
  try discriminate.

  all: inversion Hdecode; subst; reflexivity.
Qed.

  (*prove B0 as identity & unitary*)
Lemma B0_is_identity :
  B0 = I 6.
Proof.
  unfold B0, basis6, v1, v2, v3, v4, v5, v6, e_i, I.

  apply functional_extensionality.
  intro row.

  apply functional_extensionality.
  intro col.

    (*seperates row and collumn into seven possibilties*)
  destruct row as [| [| [| [| [| [| row]]]]]];
  destruct col as [| [| [| [| [| [| col]]]]]];
  simpl;
  try reflexivity.

  (*limits rows and columns to stay inside the 6x6 matrix*)
  bdestruct (S (S (S (S (S (S row))))) <? 6).
  - lia.
  - rewrite andb_false_r.
    reflexivity.
Qed.

Example B0_unitary :
  WF_Unitary B0.
Proof.
  rewrite B0_is_identity.
  apply id_unitary.
Qed.

(*Prove B1 as unitary-- B1 is not identity so we need to prove it by showing its six collumns are normalized and mutually perpendicular*)
Example v1_v7_orthogonal :
  inner_product v1 v7 = C0.
Proof.
  prove_orthogonal v1 v7.
Qed.

Example v1_v8_orthogonal :
  inner_product v1 v8 = C0.
Proof.
  prove_orthogonal v1 v8.
Qed.

Example v1_v9_orthogonal :
  inner_product v1 v9 = C0.
Proof.
  prove_orthogonal v1 v9.
Qed.

Example v1_v10_orthogonal :
  inner_product v1 v10 = C0.
Proof.
  prove_orthogonal v1 v10.
Qed.

Example v1_v11_orthogonal :
  inner_product v1 v11 = C0.
Proof.
  prove_orthogonal v1 v11.
Qed.

Example v7_v8_orthogonal :
  inner_product v7 v8 = C0.
Proof.
  prove_orthogonal v7 v8.
Qed.

Example v7_v9_orthogonal :
  inner_product v7 v9 = C0.
Proof.
  prove_orthogonal v7 v9.
Qed.

Example v7_v10_orthogonal :
  inner_product v7 v10 = C0.
Proof.
  prove_orthogonal v7 v10.
Qed.

Example v7_v11_orthogonal :
  inner_product v7 v11 = C0.
Proof.
  prove_orthogonal v7 v11.
Qed.

Example v8_v9_orthogonal :
  inner_product v8 v9 = C0.
Proof.
  prove_orthogonal v8 v9.
Qed.

Example v8_v10_orthogonal :
  inner_product v8 v10 = C0.
Proof.
  prove_orthogonal v8 v10.
Qed.

Example v8_v11_orthogonal :
  inner_product v8 v11 = C0.
Proof.
  prove_orthogonal v8 v11.
Qed.

Example v9_v10_orthogonal :
  inner_product v9 v10 = C0.
Proof.
  prove_orthogonal v9 v10.
Qed.

Example v9_v11_orthogonal :
  inner_product v9 v11 = C0.
Proof.
  prove_orthogonal v9 v11.
Qed.

Example v10_v11_orthogonal :
  inner_product v10 v11 = C0.
Proof.
  prove_orthogonal v10 v11.
Qed.

Lemma B1_WF :
  WF_Matrix B1.
Proof.
  unfold B1, basis6,
    v1, v7, v8, v9, v10, v11.
  show_wf.
Qed.

(*lemma proves that if the inner product of a vector with itself is 1, then the norm of the vector is 1*)
Lemma inner_product_one_implies_norm_one
    {n : nat} (v : Vector n) :
  inner_product v v = C1 ->
  norm v = 1%R.
Proof.
  intro H.
  unfold norm.
  rewrite H.
  simpl.
  apply sqrt_1.
Qed.

(*Prove columns of B1 are normalized*)
Example v1_normalized :
  inner_product v1 v1 = C1.
Proof.
  unfold inner_product, Mmult, adjoint, v1, e_i.
  simpl.
  lca.
Qed.

Lemma B1_columns_normalized :
  forall i, i < 6 ->
  norm (get_col B1 i) = 1%R.
Proof.
  intros i Hi.

  destruct i as [| [| [| [| [| [| i]]]]]];
  try lia.

  - apply inner_product_one_implies_norm_one.
    change (inner_product v1 v1 = C1).
    exact v1_normalized.

  - apply inner_product_one_implies_norm_one.
    change (inner_product v7 v7 = C1).
    exact v7_normalized.

  - apply inner_product_one_implies_norm_one.
    change (inner_product v8 v8 = C1).
    exact v8_normalized.

  - apply inner_product_one_implies_norm_one.
    change (inner_product v9 v9 = C1).
    exact v9_normalized.

  - apply inner_product_one_implies_norm_one.
    change (inner_product v10 v10 = C1).
    exact v10_normalized.

  - apply inner_product_one_implies_norm_one.
    change (inner_product v11 v11 = C1).
    exact v11_normalized.
Qed.

(*Prove B1 to be an orthonormal matrix*)
Lemma B1_orthogonal :
  orthogonal B1.
Proof.
  unfold orthogonal.
  intros i j Hij.

  destruct i as [| [| [| [| [| [| i]]]]]];
  destruct j as [| [| [| [| [| [| j]]]]]];
  try congruence;

  unfold get_col, B1, basis6,
    inner_product, Mmult, adjoint,
    v1, v7, v8, v9, v10, v11,
    e_i, vector6,
    half, half_omega, half_omega2,
    omega, omega2;

  simpl;
  try reflexivity;

  try (
    apply c_proj_eq;
    simpl;
    try ring;
    try (
      assert (Hs : (sqrt 3 * sqrt 3)%R = 3%R);
      [apply sqrt_def; lra | nra]
    )
  ).
Qed.

(*combine all 3 lemmas-- WF(behaves like 6x6); orthogonal; columns_normalized*)
Lemma B1_orthonormal :
  WF_Orthonormal B1.
Proof.
  unfold WF_Orthonormal, orthonormal.

  split.
  - exact B1_WF.

  - split.
    + exact B1_orthogonal.
    + exact B1_columns_normalized.
Qed.

(*Conclude B1 is unitary*)
Example B1_unitary :
  WF_Unitary B1.
Proof.
  apply (proj2 (unit_is_orthonormal B1)).
  exact B1_orthonormal.
Qed.

(*normalization of remaning vectors*)
Ltac prove_standard_normalized v :=
  unfold inner_product, Mmult, adjoint, v, e_i;
  simpl;
  lca.

Example v2_normalized :
  inner_product v2 v2 = C1.
Proof.
  prove_standard_normalized v2.
Qed.

Example v3_normalized :
  inner_product v3 v3 = C1.
Proof.
  prove_standard_normalized v3.
Qed.

Example v4_normalized :
  inner_product v4 v4 = C1.
Proof.
  prove_standard_normalized v4.
Qed.

Example v5_normalized :
  inner_product v5 v5 = C1.
Proof.
  prove_standard_normalized v5.
Qed.

Example v6_normalized :
  inner_product v6 v6 = C1.
Proof.
  prove_standard_normalized v6.
Qed.

(*package the normality proof*)
Ltac prove_six_columns_normalized
    c0 c1 c2 c3 c4 c5
    H0 H1 H2 H3 H4 H5 :=
  intros i Hi;

  destruct i as [| [| [| [| [| [| i]]]]]];
  try lia;

  [ apply inner_product_one_implies_norm_one;
    change (inner_product c0 c0 = C1);
    exact H0

  | apply inner_product_one_implies_norm_one;
    change (inner_product c1 c1 = C1);
    exact H1

  | apply inner_product_one_implies_norm_one;
    change (inner_product c2 c2 = C1);
    exact H2

  | apply inner_product_one_implies_norm_one;
    change (inner_product c3 c3 = C1);
    exact H3

  | apply inner_product_one_implies_norm_one;
    change (inner_product c4 c4 = C1);
    exact H4

  | apply inner_product_one_implies_norm_one;
    change (inner_product c5 c5 = C1);
    exact H5
  ].

  Lemma B2_WF :
  WF_Matrix B2.
Proof.
  unfold B2, basis6,
    v2, v7, v12, v13, v14, v15.
  show_wf.
Qed.

Lemma B2_columns_normalized :
  forall i, i < 6 ->
  norm (get_col B2 i) = 1%R.
Proof.
  prove_six_columns_normalized
    v2 v7 v12 v13 v14 v15
    v2_normalized
    v7_normalized
    v12_normalized
    v13_normalized
    v14_normalized
    v15_normalized.
Qed.

(*package the orthonormality proof*)
Ltac prove_basis_orthogonal B c0 c1 c2 c3 c4 c5 :=
  unfold orthogonal;
  intros i j Hij;

  destruct i as [| [| [| [| [| [| i]]]]]];
  destruct j as [| [| [| [| [| [| j]]]]]];
  try congruence;

  unfold get_col, B, basis6,
    inner_product, Mmult, adjoint,
    c0, c1, c2, c3, c4, c5,
    e_i, vector6,
    half, half_omega, half_omega2,
    omega, omega2;

  simpl;
  try reflexivity;

  try (
    apply c_proj_eq;
    simpl;
    try ring;
    try (
      assert (Hs : (sqrt 3 * sqrt 3)%R = 3%R);
      [apply sqrt_def; lra | nra]
    )
  ).

(*apply on B2*)
Lemma B2_orthogonal :
  orthogonal B2.
Proof.
  prove_basis_orthogonal
    B2 v2 v7 v12 v13 v14 v15.
Qed.

Lemma B2_orthonormal :
  WF_Orthonormal B2.
Proof.
  unfold WF_Orthonormal, orthonormal.

  split.
  - exact B2_WF.

  - split.
    + exact B2_orthogonal.
    + exact B2_columns_normalized.
Qed.

Example B2_unitary :
  WF_Unitary B2.
Proof.
  apply (proj2 (unit_is_orthonormal B2)).
  exact B2_orthonormal.
Qed.

(*package for unitary matrix*)
Lemma unitary_from_column_properties (B : Square 6) :
  WF_Matrix B ->
  orthogonal B ->
  (forall i, i < 6 -> norm (get_col B i) = 1%R) ->
  WF_Unitary B.
Proof.
  intros HWF Horthogonal Hnormalized.

  apply (proj2 (unit_is_orthonormal B)).
  unfold WF_Orthonormal, orthonormal.

  split.
  - exact HWF.

  - split.
    + exact Horthogonal.
    + exact Hnormalized.
Qed.

Example B3_unitary :
  WF_Unitary B3.
Proof.
  apply unitary_from_column_properties.

  - unfold B3, basis6,
      v3, v8, v12, v16, v17, v18.
    show_wf.

  - prove_basis_orthogonal
      B3 v3 v8 v12 v16 v17 v18.

  - prove_six_columns_normalized
      v3 v8 v12 v16 v17 v18
      v3_normalized
      v8_normalized
      v12_normalized
      v16_normalized
      v17_normalized
      v18_normalized.
Qed.

Example B4_unitary :
  WF_Unitary B4.
Proof.
  apply unitary_from_column_properties.

  - unfold B4, basis6,
      v4, v9, v13, v16, v19, v20.
    show_wf.

  - prove_basis_orthogonal
      B4 v4 v9 v13 v16 v19 v20.

  - prove_six_columns_normalized
      v4 v9 v13 v16 v19 v20
      v4_normalized
      v9_normalized
      v13_normalized
      v16_normalized
      v19_normalized
      v20_normalized.
Qed.

Example B5_unitary :
  WF_Unitary B5.
Proof.
  apply unitary_from_column_properties.

  - unfold B5, basis6,
      v5, v10, v14, v17, v19, v21.
    show_wf.

  - prove_basis_orthogonal
      B5 v5 v10 v14 v17 v19 v21.

  - prove_six_columns_normalized
      v5 v10 v14 v17 v19 v21
      v5_normalized
      v10_normalized
      v14_normalized
      v17_normalized
      v19_normalized
      v21_normalized.
Qed.

Example B6_unitary :
  WF_Unitary B6.
Proof.
  apply unitary_from_column_properties.

  - unfold B6, basis6,
      v6, v11, v15, v18, v20, v21.
    show_wf.

  - prove_basis_orthogonal
      B6 v6 v11 v15 v18 v20 v21.

  - prove_six_columns_normalized
      v6 v11 v15 v18 v20 v21
      v6_normalized
      v11_normalized
      v15_normalized
      v18_normalized
      v20_normalized
      v21_normalized.
Qed.

(* every vertex basis is a well-formed matrix *)
Lemma vertex_basis_WF :
  forall v,
    WF_Matrix (vertex_basis v).
Proof.
  intro v.
  destruct v; simpl.
  - exact (proj1 B0_unitary).
  - exact (proj1 B1_unitary).
  - exact (proj1 B2_unitary).
  - exact (proj1 B3_unitary).
  - exact (proj1 B4_unitary).
  - exact (proj1 B5_unitary).
  - exact (proj1 B6_unitary).
Qed.

(* Bob's outcome picks out the vector of his decoded edge *)
Lemma bob_outcome_matches_edge :
  forall b k e row,
    decode_outcome b k = Some e ->
    (Mmult (vertex_basis b) (basis_vector 6 k)) row 0 =
    edge_vector e row 0.
Proof.
  intros b k e row Hdecode.

  rewrite matrix_times_basis_eq
    by apply vertex_basis_WF.

  exact (decode_outcome_matches_basis b k e Hdecode row).
Qed.

(* Alice's outcome picks out the conjugate of her decoded edge vector *)
Lemma alice_outcome_matches_edge :
  forall a j e row,
    decode_outcome a j = Some e ->
    (Mmult
      (adjoint (alice_basis_change a))
      (basis_vector 6 j)) row 0 =
    (edge_vector e row 0)^*.
Proof.
  intros a j e row Hdecode.

  rewrite matrix_times_basis_eq
    by (unfold alice_basis_change;
        apply WF_adjoint;
        apply WF_transpose;
        apply vertex_basis_WF).

  unfold alice_basis_change, adjoint, transpose.
  simpl.

  rewrite (decode_outcome_matches_basis a j e Hdecode row).
  reflexivity.
Qed.

(* match the combined outcome with Alice's and Bob's decoded edge vectors *)
Lemma moved_outcome_matches_edges_entry :
  forall a b j k e f row,
    decode_outcome a j = Some e ->
    decode_outcome b k = Some f ->
    (Mmult
      (adjoint (joint_basis_change a b))
      (raw_outcome_vector j k)) row 0 =
    joint_measurement_vector e f row 0.
Proof.
  intros a b j k e f row Ha Hb.

  rewrite moved_raw_outcome_factors.
  unfold joint_measurement_vector, vector_conj, kron.

  replace (0 / 1)%nat with 0%nat by reflexivity.
  replace (0 mod 1)%nat with 0%nat by reflexivity.

  rewrite (alice_outcome_matches_edge
    a j e (row / 6) Ha).
  rewrite (bob_outcome_matches_edge
    b k f (row mod 6) Hb).

  reflexivity.
Qed.

(* check that both joint vectors match at every valid entry *)
Lemma moved_outcome_matches_edges_equiv :
  forall a b j k e f,
    decode_outcome a j = Some e ->
    decode_outcome b k = Some f ->
    mat_equiv
      (Mmult
        (adjoint (joint_basis_change a b))
        (raw_outcome_vector j k))
      (joint_measurement_vector e f).
Proof.
  intros a b j k e f Ha Hb row col Hrow Hcol.

  assert (col = 0) by lia.
  subst col.

  apply (moved_outcome_matches_edges_entry
    a b j k e f row Ha Hb).
Qed.

(*checks edge orthogonality*)
Ltac solve_edge_orthogonality :=
  unfold inner_product, Mmult, adjoint,
    v1, v2, v3, v4, v5, v6, v7,
    v8, v9, v10, v11, v12, v13, v14,
    v15, v16, v17, v18, v19, v20, v21,
    e_i, vector6,
    half, half_omega, half_omega2,
    omega, omega2;
  simpl;
  try reflexivity;
  try (
    apply c_proj_eq;
    simpl;
    try ring;
    try (
      assert (Hs : (sqrt 3 * sqrt 3)%R = 3%R);
      [apply sqrt_def; lra | nra]
    )
  ).

  (*cheks orthogonality on intersecting but different vectors*)
Theorem incompatible_edges_orthogonal :
  forall e f,
  edge_equal e f = false ->
  disjoint e f = false ->
  inner_product (edge_vector e) (edge_vector f) = C0.
Proof.
  intros e f Hdifferent Hintersecting.

  destruct e as [e1 e2];
  destruct f as [f1 f2];

  destruct e1;
  destruct e2;
  destruct f1;
  destruct f2;
  simpl in Hdifferent, Hintersecting |-;
  try discriminate.

  all: solve_edge_orthogonality.
Qed.

(*probability of output edges e and f given input vertices a and b*)
Definition ideal_probability
    (a b : Vertex) (e f : Edge) : R :=
  if andb (part_of a e) (part_of b f)
  then
    ((1 / 6) *
      probability_of_outcome (*defined by Quantum_Lib.measurement*)
        (edge_vector e) (edge_vector f))%R
  else 0%R.

(*Probability of 0 lemmas*)
Lemma ideal_probability_zero_if_alice_invalid :
  forall a b e f,
  part_of a e = false ->
  ideal_probability a b e f = 0%R.
Proof.
  intros a b e f Hinvalid.
  unfold ideal_probability.
  rewrite Hinvalid.
  reflexivity.
Qed.

Lemma ideal_probability_zero_if_bob_invalid :
  forall a b e f,
  part_of b f = false ->
  ideal_probability a b e f = 0%R.
Proof.
  intros a b e f Hinvalid.
  unfold ideal_probability.
  rewrite Hinvalid.
  rewrite andb_false_r.
  reflexivity.
Qed.

Lemma ideal_probability_zero_if_incompatible :
  forall a b e f,
  edge_equal e f = false ->
  disjoint e f = false ->
  ideal_probability a b e f = 0%R.
Proof.
  intros a b e f Hdifferent Hintersecting.
  unfold ideal_probability.

  destruct
    (andb (part_of a e) (part_of b f))
    eqn:Hvalid.

  - unfold probability_of_outcome.
    rewrite
      (incompatible_edges_orthogonal
        e f Hdifferent Hintersecting).
    rewrite Cmod_0.
    ring.

  - reflexivity.
Qed.

Theorem ideal_strategy_losing_probability_zero :
  forall a b e f,
  wins a b e f = false ->
  ideal_probability a b e f = 0%R.
Proof.
  intros a b e f Hlose. (*intros means choose arbritary values for a,b,e,f and ssume the output loses*)

  (*exact means the proofs contained by it prove the current goal*)
  exact (
    losing_probability_zero
      ideal_probability
      ideal_probability_zero_if_alice_invalid
      ideal_probability_zero_if_bob_invalid
      ideal_probability_zero_if_incompatible
      a b e f Hlose
  ).
Qed.

(* vectors that agree at every valid entry have the same inner product *)
Lemma inner_product_mat_equiv_l :
  forall {n} (u u' v : Vector n),
    mat_equiv u u' ->
    inner_product u v = inner_product u' v.
Proof.
  intros n u u' v H.
  unfold inner_product, Mmult, adjoint.

  apply big_sum_eq_bounded.
  intros i Hi.

  rewrite (H i 0 Hi ltac:(lia)).
  reflexivity.
Qed.

(* show that the raw measurement probability matches the decoded edge probability *)
Lemma raw_probability_matches_decoded_edges :
  forall a b j k e f,
    decode_outcome a j = Some e ->
    decode_outcome b k = Some f ->
    raw_outcome_probability a b j k =
    quantum_edge_probability e f.
Proof.
  intros a b j k e f Ha Hb.

  rewrite raw_outcome_probability_moved.
  unfold quantum_edge_probability, probability_of_outcome.

  assert (Hinner :
    inner_product
      (Mmult
        (adjoint (joint_basis_change a b))
        (raw_outcome_vector j k))
      phi6 =
    inner_product (joint_measurement_vector e f) phi6).
  {
    apply inner_product_mat_equiv_l.
    apply moved_outcome_matches_edges_equiv; assumption.
  }

  rewrite Hinner.
  reflexivity.
Qed.

    (* measuring basis outcome i selects entry i of the vector *)
Lemma inner_product_basis_entry :
  forall (w : Vector 6) i,
    i < 6 ->
    inner_product w (basis_vector 6 i) = (w i 0)^*.
Proof.
  intros w i Hi.
  destruct i as [|[|[|[|[|[|i]]]]]]; try lia;
    unfold inner_product, Mmult, adjoint, basis_vector;
    simpl; lca.
Qed.


(* add the 6 terms of phi6 to get the inner product of u and v *)
Lemma phi6_unscaled_amplitude :
  forall (u v : Vector 6),
    inner_product (vector_conj u ⊗ v) phi6_unscaled =
    (inner_product u v)^*.
Proof.
  intros u v.
  unfold phi6_unscaled.
  repeat rewrite inner_product_plus_r.
  unfold inner_product, Mmult, adjoint, vector_conj, kron, basis_vector.
  simpl.
  lca.
Qed.

(* include the 1/sqrt6 factor from phi6 *)
Lemma phi6_amplitude :
  forall (u v : Vector 6),
    inner_product (vector_conj u ⊗ v) phi6 =
    (RtoC (1 / sqrt 6)%R * (inner_product u v)^*)%C.
Proof.
  intros u v.
  unfold phi6.
  rewrite inner_product_scale_r.
  rewrite phi6_unscaled_amplitude.
  reflexivity.
Qed.

(* use orthogonality to show different intersecting edges have probability 0 *)
Lemma quantum_edge_probability_zero_if_incompatible :
  forall e f,
    edge_equal e f = false ->
    disjoint e f = false ->
    quantum_edge_probability e f = 0%R.
Proof.
  intros e f Hdifferent Hintersecting.
  unfold quantum_edge_probability, probability_of_outcome,
         joint_measurement_vector.
  rewrite phi6_amplitude.
  rewrite (incompatible_edges_orthogonal
             e f Hdifferent Hintersecting).
  replace (C0^*) with C0 by lca.
  rewrite Cmult_0_r, Cmod_0.
  ring.
Qed.

(* use our quantum probability for valid edge answers, and 0 otherwise *)
Definition circuit_edge_probability
    (a b : Vertex) (e f : Edge) : R :=
  if andb (part_of a e) (part_of b f)
  then quantum_edge_probability e f
  else 0%R.

(* an invalid Alice edge gets probability 0 *)
Lemma circuit_probability_zero_if_alice_invalid :
  forall a b e f,
    part_of a e = false ->
    circuit_edge_probability a b e f = 0%R.
Proof.
  intros a b e f Hinvalid.
  unfold circuit_edge_probability.
  rewrite Hinvalid.
  reflexivity.
Qed.

(* same proof for Bob *)
Lemma circuit_probability_zero_if_bob_invalid :
  forall a b e f,
    part_of b f = false ->
    circuit_edge_probability a b e f = 0%R.
Proof.
  intros a b e f Hinvalid.
  unfold circuit_edge_probability.
  rewrite Hinvalid, andb_false_r.
  reflexivity.
Qed.

(* incompatible edges have 0 probability using our earlier orthogonality proof *)
Lemma circuit_probability_zero_if_incompatible :
  forall a b e f,
    edge_equal e f = false ->
    disjoint e f = false ->
    circuit_edge_probability a b e f = 0%R.
Proof.
  intros a b e f Hdifferent Hintersecting.
  unfold circuit_edge_probability.
  destruct (andb (part_of a e) (part_of b f)).
  - apply quantum_edge_probability_zero_if_incompatible;
      assumption.
  - reflexivity.
Qed.

(* combine the previous lemmas to prove that losing edge outputs have 0 probability *)
Theorem circuit_edge_losing_probability_zero :
  forall a b e f,
    wins a b e f = false ->
    circuit_edge_probability a b e f = 0%R.
Proof.
  intros a b e f Hlose.
  exact (losing_probability_zero
    circuit_edge_probability
    circuit_probability_zero_if_alice_invalid
    circuit_probability_zero_if_bob_invalid
    circuit_probability_zero_if_incompatible
    a b e f Hlose).
Qed.

(* prove that the decoder always returns an edge containing the input vertex *)
Lemma decoded_edge_incident :
  forall v k e,
    decode_outcome v k = Some e ->
    part_of v e = true.
Proof.
  intros v k e Hdecode.
  destruct v;
  destruct k as [|[|[|[|[|[|k]]]]]];
  simpl in Hdecode |-;
  try discriminate.
  all: inversion Hdecode; subst; reflexivity.
Qed.

(* connect the raw measurement probability to the probability of the decoded edges *)
Lemma raw_probability_matches_game_edges :
  forall a b j k e f,
    decode_outcome a j = Some e ->
    decode_outcome b k = Some f ->
    raw_outcome_probability a b j k =
    circuit_edge_probability a b e f.
Proof.
  intros a b j k e f Ha Hb.
  rewrite (raw_probability_matches_decoded_edges a b j k e f Ha Hb).
  unfold circuit_edge_probability.
  rewrite (decoded_edge_incident a j e Ha).
  rewrite (decoded_edge_incident b k f Hb).
  reflexivity.
Qed.

(* prove that raw outcomes which decode to losing edges have 0 probability *)
Theorem decoded_raw_losing_probability_zero :
  forall a b j k e f,
    decode_outcome a j = Some e ->
    decode_outcome b k = Some f ->
    raw_wins a b j k = false ->
    raw_outcome_probability a b j k = 0%R.
Proof.
  intros a b j k e f Ha Hb Hlose.
  unfold raw_wins in Hlose.
  rewrite Ha, Hb in Hlose.
  rewrite (raw_probability_matches_game_edges a b j k e f Ha Hb).
  apply circuit_edge_losing_probability_zero.
  exact Hlose.
Qed.

(* every valid measurement outcome from 0 to 5 can be decoded into an edge *)
Lemma decode_valid_outcome :
  forall v k,
    k < 6 ->
    exists e, decode_outcome v k = Some e.
Proof.
  intros v k Hk.
  destruct v;
  destruct k as [|[|[|[|[|[|k]]]]]];
  try lia;
  eexists; reflexivity.
Qed.

(* final theorem: any losing pair of valid raw measurement outcomes has 0 probability *)
Theorem raw_strategy_losing_probability_zero :
  forall a b j k,
    j < 6 -> k < 6 ->
    raw_wins a b j k = false ->
    raw_outcome_probability a b j k = 0%R.
Proof.
  intros a b j k Hj Hk Hlose.
  destruct (decode_valid_outcome a j Hj) as [e Ha].
  destruct (decode_valid_outcome b k Hk) as [f Hb].
  eapply decoded_raw_losing_probability_zero; eauto.
Qed.

