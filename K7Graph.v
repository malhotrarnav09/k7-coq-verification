(*define vertices*)
Inductive Vertex : Type :=
    | V0
    | V1
    | V2
    | V3
    | V4
    | V5
    | V6.

(*define edges*)
Inductive Edge : Type :=
| E01 | E02 | E03 | E04 | E05 | E06
| E12 | E13 | E14 | E15 | E16
| E23 | E24 | E25 | E26
| E34 | E35 | E36
| E45 | E46
| E56.

(*match edges names to vertex pairs*)
Definition endpoints (e : Edge) : (Vertex * Vertex)%type :=
  match e with
  | E01 => (V0, V1)
  | E02 => (V0, V2)
  | E03 => (V0, V3)
  | E04 => (V0, V4)
  | E05 => (V0, V5)
  | E06 => (V0, V6)
  | E12 => (V1, V2)
  | E13 => (V1, V3)
  | E14 => (V1, V4)
  | E15 => (V1, V5)
  | E16 => (V1, V6)
  | E23 => (V2, V3)
  | E24 => (V2, V4)
  | E25 => (V2, V5)
  | E26 => (V2, V6)
  | E34 => (V3, V4)
  | E35 => (V3, V5)
  | E36 => (V3, V6)
  | E45 => (V4, V5)
  | E46 => (V4, V6)
  | E56 => (V5, V6)
  end.

(*verification for endpoints function*)
Example endpoints_E35 :
  endpoints E35 = (V3, V5).
Proof.
  reflexivity.
Qed.

(*checks if 2 vertices are equal*)
Definition vertex_equal (a b : Vertex) : bool :=
  match a, b with
  | V0, V0 => true
  | V1, V1 => true
  | V2, V2 => true
  | V3, V3 => true
  | V4, V4 => true
  | V5, V5 => true
  | V6, V6 => true
  | _, _ => false
  end.

(*verification for vertex_equal function*)
Example vertex_same :
  vertex_equal V4 V4 = true.
Proof.
  reflexivity.
Qed.

Example vertex_different :
  vertex_equal V4 V6 = false.
Proof.
  reflexivity.
Qed.

(*checks if a vertex is part of an edge*)
Definition part_of (v : Vertex) (e : Edge) : bool :=
  let '(x, y) := endpoints e in
  orb (vertex_equal v x) (vertex_equal v y). (*orb is bollean version of or*)

(*verification for part_of function*)
Example part_of_E35 :
  part_of V3 E35 = true.
Proof.
  reflexivity.
Qed.

Example not_part_of_E35 :
  part_of V1 E35 = false.
Proof.
  reflexivity.
Qed.

(*checks if two edges are equal*)
Definition edge_equal (e f : Edge) : bool :=
  let '(a, b) := endpoints e in (*in defines a temporary assignment*)
  let '(c, d) := endpoints f in
  andb (vertex_equal a c) (vertex_equal b d). (*andb is boolean version of and*)

(*verification for edge_equal function*)
Example same_edge :
  edge_equal E35 E35 = true.
Proof.
  reflexivity.
Qed.

Example different_edges :
  edge_equal E35 E36 = false.
Proof.
  reflexivity.
Qed.

(*checks if two edges are disjoint*)
Definition disjoint (e f : Edge) : bool :=
    let '(a,b) := endpoints e in
    let '(c,d) := endpoints f in
    negb
        (orb (vertex_equal a c)
        (orb (vertex_equal a d)
            (orb (vertex_equal b c)
                (vertex_equal b d)))). (*orb can only take in two parameters so we need to nest it*)

(*verification for disjoint function*)
Example disjoint_edges_test :
  disjoint E01 E23 = true.
Proof.
  reflexivity.
Qed.

Example shared_vertex_test :
  disjoint E01 E12 = false.
Proof.
  reflexivity.
Qed.

Example identical_edges_not_disjoint :
  disjoint E35 E35 = false.
Proof.
  reflexivity.
Qed.

(*function that defines game is won when alice and bob's edges are identical or disjoint*)
Definition wins
  (alice_vertex bob_vertex : Vertex)
  (alice_edge bob_edge : Edge) : bool :=
  andb
    (part_of alice_vertex alice_edge)
    (andb
      (part_of bob_vertex bob_edge)
      (orb
        (edge_equal alice_edge bob_edge)
        (disjoint alice_edge bob_edge))).

  (*verification for wins function*)
  (* Same edge: win. *)
Example win_same_edge :
  wins V0 V1 E01 E01 = true.
Proof.
  reflexivity.
Qed.

(* Different, disjoint edges: win. *)
Example win_disjoint_edges :
  wins V0 V2 E01 E23 = true.
Proof.
  reflexivity.
Qed.

(* Different edges sharing a vertex: lose. *)
Example lose_intersecting_edges :
  wins V0 V1 E01 E12 = false.
Proof.
  reflexivity.
Qed.

(* Alice returns an edge not touching her assigned vertex: lose. *)
Example lose_invalid_alice_answer :
  wins V0 V3 E12 E34 = false.
Proof.
  reflexivity.
Qed.