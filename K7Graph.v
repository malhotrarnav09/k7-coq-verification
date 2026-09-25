(*define vertices*)
Inductive Vertex : Type :=
    | V0
    | V1
    | V2
    | V3
    | V4
    | V5
    | V6.

(*edge is a pair of vertices*)
Definition Edge : Type := (Vertex * Vertex)%type.

(*21 edges of K7*)
Definition E01 : Edge := (V0, V1).
Definition E02 : Edge := (V0, V2).
Definition E03 : Edge := (V0, V3).
Definition E04 : Edge := (V0, V4).
Definition E05 : Edge := (V0, V5).
Definition E06 : Edge := (V0, V6).

Definition E12 : Edge := (V1, V2).
Definition E13 : Edge := (V1, V3).
Definition E14 : Edge := (V1, V4).
Definition E15 : Edge := (V1, V5).
Definition E16 : Edge := (V1, V6).

Definition E23 : Edge := (V2, V3).
Definition E24 : Edge := (V2, V4).
Definition E25 : Edge := (V2, V5).
Definition E26 : Edge := (V2, V6).

Definition E34 : Edge := (V3, V4).
Definition E35 : Edge := (V3, V5).
Definition E36 : Edge := (V3, V6).

Definition E45 : Edge := (V4, V5).
Definition E46 : Edge := (V4, V6).

Definition E56 : Edge := (V5, V6).

Definition endpoints (e : Edge) : (Vertex * Vertex)%type := e.

(*Give each vertex a number so endpoints can be put in a standard order*)
Definition vertex_index (v : Vertex) : nat :=
  match v with
  | V0 => 0
  | V1 => 1
  | V2 => 2
  | V3 => 3
  | V4 => 4
  | V5 => 5
  | V6 => 6
  end.

(* Put the lower-numbered endpoint first. *)
Definition ordered_endpoints (e : Edge) : (Vertex * Vertex)%type :=
  let '(a, b) := endpoints e in
  if Nat.leb (vertex_index a) (vertex_index b)
  then (a, b)
  else (b, a).

Example ordered_endpoints_test :
  ordered_endpoints (V5, V3) = (V3, V5).
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

(*K7 has no edges from any vertex to itself*)
Definition valid_edge (e:Edge) : bool :=
  let '(x,y) :=endpoints e in 
  negb (vertex_equal x y).

(*checks if a vertex is part of an edge*)
Definition part_of (v : Vertex) (e : Edge) : bool :=
  let '(x, y) := endpoints e in 
  andb
  (valid_edge e)
  (orb (vertex_equal v x) (vertex_equal v y)). (*orb is bollean version of or*)

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
  orb
    (andb (vertex_equal a c) (vertex_equal b d)) (*andb is boolean version of and*)
    (andb (vertex_equal a d) (vertex_equal b c)). (*4 conditions as edges no longer have direction*)

    (*verification for valid_edge function*)
Example loop_is_not_valid :
  valid_edge (V3, V3) = false.
Proof.
  reflexivity.
Qed.

(*verification for unordered edges*)
Example reversed_edge_is_equal :
  edge_equal E35 (V5, V3) = true.
Proof.
  reflexivity.
Qed.


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