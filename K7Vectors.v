Require Import K7Graph.

Require Import QuantumLib.Matrix.

Require Import QuantumLib.Quantum.

Require Import QuantumLib.Eigenvectors.

Require Import QuantumLib.Measurement.

Require Import K7Strategy.


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
  match e with
  | E01 => v1
  | E02 => v2
  | E03 => v3
  | E04 => v4
  | E05 => v5
  | E06 => v6
  | E12 => v7
  | E13 => v8
  | E14 => v9
  | E15 => v10
  | E16 => v11
  | E23 => v12
  | E24 => v13
  | E25 => v14
  | E26 => v15
  | E34 => v16
  | E35 => v17
  | E36 => v18
  | E45 => v19
  | E46 => v20
  | E56 => v21
  end.

  (*verification of edge_vector*)
Example edge12_vector_is_v7 :
  edge_vector E12 = v7.
Proof.
  reflexivity.
Qed.

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

  destruct e;
  destruct f;
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