

# Coq Verification of the K7 Quantum Strategy

This repository contains my Coq formalization of the quantum strategy for the K7 perfect-matching game. I wrote it while learning Coq and QuantumLib.

The project formalizes the graph, the 21 complex edge vectors, and the seven measurement bases. It also explicitly defines the shared entangled state, Alice and Bob's measurement-basis changes, their raw measurement outcomes, and the decoder that turns those outcomes into graph edges.

The main theorem proves that every losing pair of valid raw measurement outcomes has probability exactly zero under the ideal six-dimensional quantum strategy.

## 1. The K7 perfect-matching game

K7 is the complete graph on seven vertices:

`V0, V1, V2, V3, V4, V5, V6`

Every pair of distinct vertices is connected by an edge. There are therefore 21 edges in total, and every vertex belongs to exactly six edges.

### Rules

A referee gives Alice one vertex and Bob another vertex. The players may agree on a strategy before the game begins, but they cannot communicate after receiving their inputs.

Each player must answer with an edge that contains their assigned vertex.

They win if both answers are valid and their chosen edges are either:

- **The same edge**, or
- **Disjoint edges**, meaning the edges do not share any vertex.

They lose if either player gives an invalid answer, or if their edges are different but intersect.

### Example: Alice receives V2 and Bob receives V3

Alice must choose one of the six edges incident to `V2`:

- `(V0,V2)`
- `(V1,V2)`
- `(V2,V3)`
- `(V2,V4)`
- `(V2,V5)`
- `(V2,V6)`

Bob must choose one of the six edges incident to `V3`.

Here are four possible outcomes:

| Alice's answer | Bob's answer | Result | Explanation |
|---|---|---|---|
| `(V2,V3)` | `(V2,V3)` | Win | The edges are identical, and both players answered with an edge containing their input vertex. |
| `(V0,V2)` | `(V1,V3)` | Win | The edges share no vertices, so they are disjoint. |
| `(V0,V2)` | `(V0,V3)` | Lose | Both answers are valid, but the two different edges intersect at `V0`. |
| `(V0,V1)` | `(V1,V3)` | Lose | Alice's answer does not contain her assigned vertex, `V2`. |

An answer such as `(V2,V2)` is also invalid because K7 has edges only between distinct vertices.

### What if Alice and Bob receive the same vertex?

Suppose both players receive `V2`.

Every valid answer from either player must contain `V2`. If they choose different edges, those edges necessarily intersect at `V2`, so they lose.

Therefore, when the players receive the same vertex, they must return the same edge to win.

The game rules are formalized in `K7Graph.v`, including the `wins` function that determines whether a pair of answers wins.

## 2. Representing undirected edges

In Coq, an edge is represented as a pair of vertices.

K7 is an undirected graph, so `(V1,V2)` and `(V2,V1)` must represent the same edge.

The function `ordered_endpoints` puts both orientations into a canonical order. This ensures that reversing an edge does not affect its identity or its assigned quantum vector.

For example:

```coq
edge_vector (V1,V2) = v7
edge_vector (V2,V1) = v7
```

The graph formalization also includes predicates for checking valid edges, whether a vertex belongs to an edge, whether two edges are equal, and whether two edges are disjoint.

These are used in both the general game proof and the quantum-strategy proof.

## 3. The 21 complex edge vectors

The quantum strategy assigns one vector in six-dimensional complex space to each of K7's 21 edges.

These vectors are defined in `K7Vectors.v` as `v1` through `v21`.

The vectors use exact complex numbers, including:

```text
1/2
omega/2
omega2/2
```

where:

```text
omega  = -1/2 + i*sqrt(3)/2
omega2 = -1/2 - i*sqrt(3)/2
```

The definitions use exact arithmetic rather than floating-point approximations.

### Normalization

Every edge vector is proved to be normalized. In other words, the inner product of each vector with itself equals 1.

```text
inner_product(u_e, u_e) = 1
```

The Coq development proves the necessary complex-number identities and then establishes normalization for all 21 vectors.

## 4. The seven measurement bases

Every vertex has six incident edges. The six vectors assigned to those edges form that vertex's measurement basis.

Each measurement basis is represented by a 6-by-6 matrix whose columns are the corresponding edge vectors.

| Vertex | Basis | Columns |
|---|---|---|
| V0 | B0 | v1, v2, v3, v4, v5, v6 |
| V1 | B1 | v1, v7, v8, v9, v10, v11 |
| V2 | B2 | v2, v7, v12, v13, v14, v15 |
| V3 | B3 | v3, v8, v12, v16, v17, v18 |
| V4 | B4 | v4, v9, v13, v16, v19, v20 |
| V5 | B5 | v5, v10, v14, v17, v19, v21 |
| V6 | B6 | v6, v11, v15, v18, v20, v21 |

For example, the basis `B2` consists of the six vectors associated with the edges incident to `V2`.

### Proving unitarity

For each measurement basis, the Coq proofs establish that its columns are normalized and mutually orthogonal.

This means the columns form an orthonormal basis. Consequently, the corresponding basis matrix is unitary.

For a basis matrix `B`, the relevant condition is:

```text
adjoint(B) * B = I
```

The proofs `B0_unitary` through `B6_unitary` establish unitarity for all seven bases.

The function `vertex_basis` selects the correct measurement-basis matrix for a given input vertex.

## 5. Orthogonality of incompatible edges

The central geometric property of the strategy is that two different, intersecting edges have orthogonal vectors.

This is formalized by:

```coq
Theorem incompatible_edges_orthogonal :
  forall e f,
    edge_equal e f = false ->
    disjoint e f = false ->
    inner_product (edge_vector e)
                  (edge_vector f) = C0.
```

For example, `(V0,V2)` and `(V0,V3)` are different edges that intersect at `V0`. Their assigned vectors therefore have inner product zero.

These are exactly the incompatible pairs that cause Alice and Bob to lose when both players otherwise give valid edge answers.

However, proving this geometric property alone does not establish that the actual quantum measurement process assigns probability zero to these outcomes.

The next part of the formalization connects the geometry to the shared quantum state, measurement operations, and Born rule.

## 6. The shared entangled state

Alice and Bob share the six-dimensional maximally entangled state:

```text
Phi6 = (|0,0> + |1,1> + |2,2> +
        |3,3> + |4,4> + |5,5>) / sqrt(6)
```

The definition `phi6_unscaled` explicitly constructs the sum of the six computational-basis tensor products.

The definition `phi6` then applies the normalization factor `1/sqrt(6)`.

Alice's local system has dimension 6, and Bob's local system also has dimension 6. Their combined quantum state therefore belongs to a 36-dimensional space.

This explicitly defined state is the starting point for the later quantum probability calculations.

## 7. Alice and Bob's measurement operations

The measurement basis each player uses depends on the vertex received from the referee.

Alice measures in the conjugate basis associated with her input vertex, while Bob measures in the original basis associated with his input vertex.

Because the basis vectors are stored as matrix columns, the corresponding basis-change operations are:

```text
Alice: transpose(B_a)

Bob:   adjoint(B_b)

Joint: transpose(B_a) tensor adjoint(B_b)
```

Here `B_a` and `B_b` are the basis matrices selected by Alice's and Bob's respective input vertices.

The tensor product combines the two operations because Alice's matrix acts on her own six-dimensional system and Bob's matrix acts on his separate six-dimensional system.

The definitions `alice_basis_change`, `bob_basis_change`, and `joint_basis_change` represent these operations in Coq.

The combined basis change is applied to the shared entangled state by `post_basis_state`.

Therefore, the state that Alice and Bob measure is constructed explicitly from their input-dependent basis changes and their shared entangled state.

## 8. Raw measurement outcomes and decoding

After applying their basis changes, Alice and Bob measure in the computational basis.

Alice receives a raw outcome `j`, and Bob receives a raw outcome `k`. In the six-dimensional model, valid outcomes range from 0 through 5.

The joint computational-basis outcome is:

```text
|j> tensor |k>
```

This is represented in Coq by `raw_outcome_vector`.

The definition `raw_outcome_probability` uses QuantumLib's `probability_of_outcome` to calculate the probability of obtaining the joint outcome from `post_basis_state`.

### Why a decoder is necessary

The quantum measurement returns numbers, but the K7 game requires players to return graph edges.

The function `decode_outcome` converts an input vertex and a raw measurement outcome into the corresponding incident edge.

For example:

```coq
decode_outcome V2 1 = Some (V1,V2).
```

The decoding for vertex `V2` is:

| Raw outcome | Decoded edge |
|---|---|
| 0 | (V0,V2) |
| 1 | (V1,V2) |
| 2 | (V2,V3) |
| 3 | (V2,V4) |
| 4 | (V2,V5) |
| 5 | (V2,V6) |

Importantly, the same edge can correspond to different raw measurement outcomes depending on the player's input vertex.

For example:

```coq
decode_outcome V0 1 = Some (V0,V2).

decode_outcome V2 0 = Some (V0,V2).
```

Both players have selected the same graph edge, even though their raw outcomes are different.

Therefore, the K7 winning condition must compare the decoded edges rather than simply compare the raw measurement numbers.

### Verifying the decoder

The theorem `decode_outcome_matches_basis` proves that every successfully decoded edge corresponds to exactly the correct column of the player's measurement-basis matrix.

The lemma `decoded_edge_incident` proves that every successfully decoded edge contains the player's input vertex.

The lemma `decode_valid_outcome` establishes that every valid raw outcome from 0 to 5 can be decoded into an edge.

Together, these results connect the numerical quantum measurement outcomes to the graph's required answers.

## 9. Connecting the quantum measurement to the edge vectors

This is the central connection between the explicit quantum operations and the graph strategy.

The original raw measurement amplitude compares the computational-basis outcome `|j,k>` with the shared state after the combined basis change.

The proof `raw_outcome_probability_moved` rewrites the same amplitude using the adjoint of the combined basis-change matrix.

Instead of applying the basis change to the state and then comparing it with the raw outcome, we can equivalently apply the adjoint of the basis change to the raw outcome and compare the resulting vector with the original shared state.

This rewrite is useful because it exposes the measurement-basis vectors associated with the raw outcomes.

### Separating Alice's and Bob's vectors

The proofs `joint_basis_change_adjoint` and `moved_raw_outcome_factors` simplify the adjoint of the combined operation and separate the transformed outcome into Alice's and Bob's individual vectors.

The proof `alice_outcome_matches_edge` shows that Alice's part corresponds to the complex conjugate of her decoded edge vector.

The proof `bob_outcome_matches_edge` shows that Bob's part corresponds to his ordinary decoded edge vector.

Thus the joint transformed outcome agrees, at every valid entry, with:

```text
complex_conjugate(edge_vector e) tensor edge_vector f
```

The lemmas `moved_outcome_matches_edges_entry` and `moved_outcome_matches_edges_equiv` establish this relationship entry by entry and then as matrix equivalence.

### Proving the probability connection

The theorem `raw_probability_matches_decoded_edges` combines these results.

If Alice's raw outcome `j` decodes to edge `e` and Bob's raw outcome `k` decodes to edge `f`, then:

```text
raw_outcome_probability(a, b, j, k)
    =
quantum_edge_probability(e, f)
```

This establishes that the probability calculated from the explicit shared state and measurement operations agrees with the probability associated with the decoded edge vectors.

The zero-probability proof can therefore reason about the actual defined quantum measurement process rather than starting with an independently assigned edge-probability formula.

## 10. Deriving the amplitude from the shared state

The next step derives the measurement amplitude directly from the shared entangled state.

The proof `phi6_unscaled_amplitude` expands the six terms of the unnormalized shared state.

The proof `phi6_amplitude` then includes the normalization factor `1/sqrt(6)`.

Together, they establish:

```text
amplitude(e, f)
    =
conjugate(inner_product(u_e, u_f)) / sqrt(6)
```

The complex conjugate comes from Alice's conjugated measurement vectors and the inner-product convention used by QuantumLib.

The Born rule calculates probability by squaring the magnitude of the amplitude.

Consequently, the corresponding mathematical probability is:

```text
probability(e, f)
    =
|inner_product(u_e, u_f)|^2 / 6
```

The Coq development proves the amplitude identity directly. The final zero-probability proof uses that identity without needing a separate theorem simplifying the complete probability expression.

### Why incompatible edges have probability zero

If two different edges intersect, the earlier orthogonality theorem establishes:

```text
inner_product(u_e, u_f) = 0
```

The derived amplitude is therefore also zero.

Applying the Born rule gives:

```text
probability(e, f) = |0|^2 = 0
```

This result is formalized by `quantum_edge_probability_zero_if_incompatible`.

The proof connects a losing graph configuration to a zero quantum amplitude and, consequently, to zero measurement probability.

## 11. Structure of the Coq proofs

The formalization is divided into several stages. Each stage establishes a property needed by the next one.

| Coq proof | What it establishes |
|---|---|
| `B0_unitary` through `B6_unitary` | All seven measurement-basis matrices are unitary. |
| `incompatible_edges_orthogonal` | Different, intersecting edges have orthogonal vectors. |
| `decode_outcome_matches_basis` | A decoded edge corresponds to the correct measurement-basis column. |
| `raw_outcome_probability_moved` | Rewrites the actual measurement probability to expose the measurement vectors. |
| `joint_basis_change_adjoint` | Simplifies the adjoint of the combined basis-change matrix. |
| `moved_raw_outcome_factors` | Separates the transformed joint outcome into Alice's and Bob's individual vectors. |
| `alice_outcome_matches_edge` | Alice's transformed outcome corresponds to her conjugated edge vector. |
| `bob_outcome_matches_edge` | Bob's transformed outcome corresponds to his ordinary edge vector. |
| `moved_outcome_matches_edges_equiv` | Combines Alice's and Bob's results into the joint decoded-edge measurement vector. |
| `raw_probability_matches_decoded_edges` | Connects the probability calculated from the explicit quantum operations to the decoded edge-vector probability. |
| `phi6_unscaled_amplitude` | Derives the measurement amplitude from the six terms of the unnormalized shared state. |
| `phi6_amplitude` | Includes the normalization factor and establishes the amplitude for the normalized shared state. |
| `quantum_edge_probability_zero_if_incompatible` | Uses the amplitude identity and edge orthogonality to prove zero probability for incompatible edge pairs. |
| `decoded_edge_incident` | Proves that successfully decoded edges contain the player's input vertex. |
| `raw_probability_matches_game_edges` | Connects the raw quantum measurement probability to the probability used by the game-level proof. |
| `raw_strategy_losing_probability_zero` | Proves that every losing pair of valid raw measurement outcomes has probability zero. |

The most important part of the proof is the connection between the explicitly defined quantum operations and the decoded edge vectors.

The graph-theoretic orthogonality theorem provides the mathematical reason incompatible edges cannot occur together. The measurement and amplitude proofs establish why this property also holds for the probability calculated from the quantum state and measurement operations.

## 12. Connecting the quantum result to the game's rules

The definition `circuit_edge_probability` assigns the quantum-derived probability to valid pairs of output edges and zero to invalid pairs.

Its supporting lemmas establish three zero-probability properties:

1. An invalid Alice edge has probability zero.
2. An invalid Bob edge has probability zero.
3. Two different, intersecting edges have probability zero.

The general theorem `losing_probability_zero` in `K7Strategy.v` establishes that any probability function satisfying these three conditions assigns zero probability to every losing game output.

The theorem `circuit_edge_losing_probability_zero` applies this general result to the quantum-derived edge probability.

The theorem `raw_probability_matches_game_edges` then connects the game-level probability back to the raw probability obtained from the shared state and measurement operations.

The final proof therefore combines the explicit quantum construction with the original graph winning condition.

## 13. Final theorem

The main theorem is:

```coq
Theorem raw_strategy_losing_probability_zero :
  forall a b j k,
    j < 6 -> k < 6 ->
    raw_wins a b j k = false ->
    raw_outcome_probability a b j k = 0%R.
```

In words:

For any input vertices `a` and `b`, and any valid six-dimensional raw outcomes `j` and `k`, if decoding those outcomes would cause Alice and Bob to lose the K7 game, then the probability of obtaining that pair of outcomes is exactly zero.

The entire proof follows this chain:

```text
Input vertices a and b
          |
          v
Select the corresponding measurement bases
          |
          v
Start with the shared entangled state Phi6
          |
          v
Apply Alice's and Bob's basis changes
          |
          v
Measure raw outcomes j and k
          |
          v
Decode the outcomes into graph edges e and f
          |
          v
Connect the raw probability to the edge vectors
          |
          v
Use orthogonality for incompatible edge pairs
          |
          v
Derive zero amplitude from the shared state
          |
          v
Obtain zero probability from the Born rule
          |
          v
Every losing pair of valid raw outcomes
has probability zero
```

The original `ideal_probability` definition and `ideal_strategy_losing_probability_zero` theorem are also retained in the project.

The newer theorem establishes the additional connection to the explicitly defined shared state, basis-change operations, computational-basis measurements, and decoder.

## 14. Files

- `K7Graph.v` defines the vertices, undirected edges, canonical edge ordering, and K7 winning and losing conditions.
- `K7Strategy.v` proves the general theorem connecting the three zero-probability properties to every losing game output.
- `K7Vectors.v` defines the 21 complex edge vectors, seven unitary measurement bases, shared entangled state, measurement operations, raw outcomes, decoder, quantum probabilities, and the final quantum-strategy theorem.

## 15. Verification

The revised Coq code compiles successfully in the local project.

The final theorem was also checked using:

```coq
Print Assumptions raw_strategy_losing_probability_zero.
```
