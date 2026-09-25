
# Coq Verification of the K7 Quantum Strategy

This repository contains my Coq formalization of the quantum strategy for the K7 perfect-matching game. I wrote it while learning Coq and QuantumLib.

The formalization covers the graph and its 21 edge vectors, the seven measurement bases, the shared entangled state, Alice and Bob's basis-change operations, raw measurement outcomes, and the decoder that converts those outcomes into graph edges. The main theorem proves that every losing pair of valid raw outcomes has probability exactly zero in the ideal six-dimensional strategy.

## 1. The game

K7 is the complete graph on seven vertices, `V0` through `V6`. Every pair of *distinct* vertices has an edge, so the graph has 21 edges. Each vertex belongs to six edges.

A referee gives Alice an input vertex and Bob an input vertex. They may agree on a strategy beforehand, but they cannot communicate after receiving their inputs. Each must answer with an edge that contains their assigned vertex.

### Example: Alice gets V2 and Bob gets V3

Alice can return any of these six edges:

- `(V0,V2)`
- `(V1,V2)`
- `(V2,V3)`
- `(V2,V4)`
- `(V2,V5)`
- `(V2,V6)`

Bob must choose one of the six edges containing `V3`.

They **win** if both responses are valid and their edges are either **the same edge** or **disjoint** (share no vertex).

| Alice's answer | Bob's answer | Result | Reason |
|---|---|---|---|
| `(V2,V3)` | `(V2,V3)` | Win | The edges are identical and both answers are valid. |
| `(V0,V2)` | `(V1,V3)` | Win | The edges have no vertex in common. |
| `(V0,V2)` | `(V0,V3)` | Lose | The edges differ but intersect at `V0`. |
| `(V0,V1)` | `(V1,V3)` | Lose | Alice's edge does not contain her input, `V2`. |

An answer such as `(V2,V2)` is not a valid graph edge because its endpoints are not distinct.

The rules also cover equal inputs. If both players receive `V2`, every valid answer from either player contains `V2`. Two *different* valid answers would intersect at `V2`, so in that case they can win only by returning the same edge.

`K7Graph.v` defines the graph predicates and the `wins` function implementing these conditions.

## 2. Undirected edges in Coq

An edge is represented by a pair of vertices. Since K7 is undirected, `(V1,V2)` and `(V2,V1)` refer to the same graph edge. `ordered_endpoints` puts both orientations into the same canonical order before comparing edges or assigning vectors. For example, both orientations of the edge between `V1` and `V2` map to `v7`.

The graph code also defines the checks for valid edges, whether a vertex belongs to an edge, edge equality, and disjointness. These are the exact predicates used by the later game and probability proofs.

## 3. The 21 edge vectors and seven bases

Every graph edge is assigned one vector in six-dimensional complex space. The 21 vectors, `v1` through `v21`, are defined using exact complex numbers, including `1/2`, `omega/2`, and `omega2/2`. Here `omega = -1/2 + i*sqrt(3)/2`, and `omega2` is its complex conjugate. No floating-point approximations are needed.

Coq proves that every edge vector is normalized: its inner product with itself is `1`.

The six vectors attached to each vertex are used as the columns of that vertex's measurement-basis matrix:

| Input vertex | Basis matrix | Columns |
|---|---|---|
| `V0` | `B0` | `v1, v2, v3, v4, v5, v6` |
| `V1` | `B1` | `v1, v7, v8, v9, v10, v11` |
| `V2` | `B2` | `v2, v7, v12, v13, v14, v15` |
| `V3` | `B3` | `v3, v8, v12, v16, v17, v18` |
| `V4` | `B4` | `v4, v9, v13, v16, v19, v20` |
| `V5` | `B5` | `v5, v10, v14, v17, v19, v21` |
| `V6` | `B6` | `v6, v11, v15, v18, v20, v21` |

For each basis, the proof establishes that its columns are normalized and mutually orthogonal. The lemmas `B0_unitary` through `B6_unitary` establish that the seven basis matrices are unitary. `vertex_basis` selects the appropriate matrix from the input vertex.

There is a second important geometric result:

```coq
Theorem incompatible_edges_orthogonal :
  forall e f,
    edge_equal e f = false ->
    disjoint e f = false ->
    inner_product (edge_vector e) (edge_vector f) = C0.
```

In other words, two **different, intersecting edges** have orthogonal vectors. These are the incompatible edge pairs that would lose the game when both answers are otherwise valid. The remaining proof shows why this vector identity makes their *actual quantum measurement probability* zero.

## 4. The shared entangled state

Alice and Bob start with the six-dimensional maximally entangled state:

```text
Phi6 = (|0,0> + |1,1> + |2,2> + |3,3> + |4,4> + |5,5>) / sqrt(6)
```

`phi6_unscaled` explicitly defines the six terms, and `phi6` multiplies their sum by `1/sqrt(6)`. Alice's local space has dimension 6 and Bob's has dimension 6, so the joint state is represented as a 36-dimensional vector.

## 5. Alice's and Bob's measurement operations

Each input vertex determines a measurement basis. Alice uses the **conjugate basis**, and Bob uses the **original basis**. Because each basis vector is stored as a matrix column, their basis-change operations are:

```text
Alice: transpose(B_a)
Bob:   adjoint(B_b)
Joint: transpose(B_a) tensor adjoint(B_b)
```

Here `B_a` and `B_b` are the basis matrices selected by Alice's and Bob's input vertices. The tensor product is necessary because the two matrices act on separate six-dimensional systems.

`alice_basis_change`, `bob_basis_change`, and `joint_basis_change` define these operations. `post_basis_state` applies their combined operation to `phi6`. Thus the state being measured is built explicitly from the initial entangled state and the two players' measurement choices.

## 6. Raw measurement outcomes and decoding

After the basis changes, both players measure in the computational basis. Alice obtains a number `j` and Bob obtains a number `k`, each from `0` through `5` in this six-dimensional model.

`raw_outcome_vector j k` represents the joint computational outcome `|j> tensor |k>`. `raw_outcome_probability a b j k` uses QuantumLib's Born-rule function to calculate the probability of that outcome in `post_basis_state a b`.

The game requires edges, not numbers, so `decode_outcome` converts each player's input vertex and raw outcome into an edge. For example, the columns of `B2` give the following decoding:

| Raw outcome at `V2` | Decoded edge |
|---|---|
| `0` | `(V0,V2)` |
| `1` | `(V1,V2)` |
| `2` | `(V2,V3)` |
| `3` | `(V2,V4)` |
| `4` | `(V2,V5)` |
| `5` | `(V2,V6)` |

The same graph edge can have different raw numbers in different vertex bases. For instance, `V0` with outcome `1` and `V2` with outcome `0` both decode to `(V0,V2)`. This is why the game checks **decoded edges**, not whether the raw numbers match.

`decode_outcome_matches_basis` proves that a decoded edge's vector is exactly the corresponding basis column. `decoded_edge_incident` proves that every successfully decoded edge contains the player's input vertex. `decode_valid_outcome` proves that every raw outcome from `0` to `5` can be decoded.

## 7. Linking the circuit measurement to the decoded edge vectors

This is the main bridge between the explicit quantum operations and the graph strategy.

The raw-outcome amplitude starts by comparing the computational outcome `|j,k>` with the shared state *after* the combined basis change. `raw_outcome_probability_moved` uses an inner-product identity to move the basis-change operation onto the outcome instead. This does **not** change the probability; it rewrites the same amplitude into a form that exposes the measurement vectors.

`joint_basis_change_adjoint` and `moved_raw_outcome_factors` split the transformed joint outcome into Alice's and Bob's separate parts. The proofs `alice_outcome_matches_edge` and `bob_outcome_matches_edge` show that these parts equal, respectively:

```text
Alice: complex_conjugate(edge_vector e)
Bob:   edge_vector f
```

The entry-by-entry proof `moved_outcome_matches_edges_entry` and the matrix-equivalence proof `moved_outcome_matches_edges_equiv` combine these results. The theorem `raw_probability_matches_decoded_edges` then establishes:

```text
If Alice's raw outcome decodes to e and Bob's decodes to f, then

raw_outcome_probability(a, b, j, k) = quantum_edge_probability(e, f).
```

This equality is what makes the later zero-probability result a statement about the **defined state and measurement operations**, not just a probability formula assigned to graph edges.

## 8. Deriving the probability from Phi6

`phi6_unscaled_amplitude` expands the six terms of the shared state. `phi6_amplitude` includes the `1/sqrt(6)` normalization. Together they prove the amplitude identity:

```text
amplitude(e, f) = conjugate(inner_product(u_e, u_f)) / sqrt(6)
```

Taking its squared magnitude gives the familiar mathematical expression:

```text
probability(e, f) = |inner_product(u_e, u_f)|^2 / 6
```

The amplitude identity is proved in Coq. The final zero-probability argument uses that identity directly; it does not require a separate Coq theorem simplifying the entire probability to the expression above.

If edges `e` and `f` are different and intersect, `incompatible_edges_orthogonal` says their inner product is zero. The amplitude is then zero, and the Born-rule probability is zero as well. This is formalized by `quantum_edge_probability_zero_if_incompatible`.

## 9. Connecting the quantum result to the game

`circuit_edge_probability` assigns the quantum-derived probability to valid pairs of output edges and zero to invalid pairs. Its supporting lemmas establish zero probability for an invalid Alice edge, an invalid Bob edge, and two different intersecting edges.

The general theorem in `K7Strategy.v`, `losing_probability_zero`, combines those three facts to show that losing edge responses have probability zero. `raw_probability_matches_game_edges` connects that game-level result back to the actual raw measurement probability.

The final theorem is:

```coq
Theorem raw_strategy_losing_probability_zero :
  forall a b j k,
    j < 6 -> k < 6 ->
    raw_wins a b j k = false ->
    raw_outcome_probability a b j k = 0%R.
```

In words: for **any** input vertices and any valid six-dimensional raw outcomes, if decoding those outcomes would lose the K7 game, the probability of obtaining them is exactly zero.

The full proof chain is:

```text
input vertices
    -> select the two measurement bases
    -> prepare Phi6 and apply the basis changes
    -> measure raw outcomes j and k
    -> decode them into edges e and f
    -> identify any losing edge pair
    -> use edge orthogonality and the derived amplitude
    -> prove its Born-rule probability is zero
```

The older `ideal_probability` and `ideal_strategy_losing_probability_zero` remain in the file. The new final theorem goes further by establishing the link to the explicitly defined shared state, measurements, and decoder.

## 10. Files

- `K7Graph.v` defines vertices, undirected edges, canonical ordering, and the winning condition.
- `K7Strategy.v` proves the general game-level zero-probability theorem.
- `K7Vectors.v` defines the edge vectors, unitary bases, shared state, measurement operations, decoder, circuit-derived probabilities, and final quantum-strategy theorem.

## 11. Verification

The revised `K7Vectors.v` compiled successfully in the local Coq project. The final theorem was also checked using:

```coq
Print Assumptions raw_strategy_losing_probability_zero.
```
