
# Coq Verification of the K7 Quantum Strategy

This repository contains my Coq formalization of the quantum strategy for the K7 perfect-matching game, using QuantumLib.

The project started with formalizing the graph and its 21 complex edge vectors. I then extended it to model the actual quantum strategy: the shared entangled state, the measurement bases chosen by Alice and Bob, their raw measurement outcomes, and the decoder that converts those outcomes into graph edges.

The main result is `raw_strategy_losing_probability_zero`. It proves that every losing pair of valid raw measurement outcomes has probability zero in the ideal six-dimensional quantum strategy.

## 1. The K7 perfect-matching game

K7 is the complete graph on seven vertices:

`V0, V1, V2, V3, V4, V5, V6`

Every pair of distinct vertices is connected by an edge, giving 21 edges in total. Each vertex belongs to six edges.

### Game rules

A referee gives Alice and Bob an input vertex each. The players can agree on a strategy before the game, but they cannot communicate after receiving their inputs.

Each player must return an edge containing their assigned vertex.

The players win if both answers are valid and their chosen edges are either:

1. The same edge.
2. Disjoint edges, meaning they share no vertices.

They lose if either player returns an invalid edge, or if they return two different edges that intersect.

### Example: Alice receives V2 and Bob receives V3

Alice can return any of these six edges:

- `(V0,V2)`
- `(V1,V2)`
- `(V2,V3)`
- `(V2,V4)`
- `(V2,V5)`
- `(V2,V6)`

Bob can return any of the six edges containing `V3`.

Here are some possible outcomes:

| Alice's answer | Bob's answer | Result | Reason |
|---|---|---|---|
| `(V2,V3)` | `(V2,V3)` | Win | The edges are identical, and both answers contain the required input vertices. |
| `(V0,V2)` | `(V1,V3)` | Win | The edges have no vertices in common. |
| `(V0,V2)` | `(V0,V3)` | Lose | Both answers are valid, but the edges are different and intersect at `V0`. |
| `(V0,V1)` | `(V1,V3)` | Lose | Alice's edge does not contain `V2`. |

An edge such as `(V2,V2)` is invalid because K7 has no edges connecting a vertex to itself.

If Alice and Bob receive the same vertex, they must return the same edge to win. For example, if they both receive `V2`, any two different valid answers would intersect at `V2`.

These rules are defined in `K7Graph.v`. The function `wins` checks whether both answers contain the required input vertices and whether the two edges are equal or disjoint.

## 2. Representing the graph in Coq

Vertices are defined using the inductive type `Vertex`, and an edge is represented by a pair of vertices.

Since K7 is undirected, `(V1,V2)` and `(V2,V1)` represent the same edge.

The function `ordered_endpoints` puts the endpoints into a standard order. This is useful when assigning vectors to edges, since reversing an edge should not change its assigned vector.

For example, both `(V1,V2)` and `(V2,V1)` are assigned `v7`.

The graph file also defines:

- `valid_edge`: checks that an edge has two distinct endpoints.
- `part_of`: checks whether an edge contains a given vertex.
- `edge_equal`: checks equality without depending on endpoint order.
- `disjoint`: checks whether two edges share any vertices.
- `wins`: combines these conditions into the game's winning rule.

`K7Graph.v` includes examples checking each of these definitions against individual graph configurations.

## 3. The 21 complex edge vectors

Each edge of K7 is assigned a vector in six-dimensional complex space. The vectors are defined in `K7Vectors.v` as `v1` through `v21`.

The first six vectors are the standard computational-basis vectors. The remaining vectors use entries such as `1/2`, `omega/2`, and `omega2/2`, where:

```text
omega  = -1/2 + i*sqrt(3)/2
omega2 = -1/2 - i*sqrt(3)/2
```

All the values are represented using exact complex and real arithmetic, rather than floating-point approximations.

The first step is to prove that every edge vector is normalized:

```text
inner_product(v, v) = 1
```

I first proved some of the normalization identities separately, including the identities involving `omega` and `omega2`. I then used reusable Coq tactics to prove the remaining vector-normalization results.

## 4. The seven measurement bases

Every vertex has six incident edges. The corresponding six edge vectors form that vertex's measurement basis.

These vectors are stored as the columns of a 6-by-6 matrix.

| Vertex | Basis | Columns |
|---|---|---|
| V0 | B0 | v1, v2, v3, v4, v5, v6 |
| V1 | B1 | v1, v7, v8, v9, v10, v11 |
| V2 | B2 | v2, v7, v12, v13, v14, v15 |
| V3 | B3 | v3, v8, v12, v16, v17, v18 |
| V4 | B4 | v4, v9, v13, v16, v19, v20 |
| V5 | B5 | v5, v10, v14, v17, v19, v21 |
| V6 | B6 | v6, v11, v15, v18, v20, v21 |

The Coq development proves that each basis is unitary.

`B0` is the identity matrix, so its unitarity follows directly from the identity-matrix result in QuantumLib.

For the remaining bases, I prove that the matrices are well-formed, their columns are normalized, and different columns are orthogonal. These properties are combined to establish `B1_unitary` through `B6_unitary`.

The function `vertex_basis` selects the correct measurement basis for a player's input vertex.

### Orthogonality of incompatible edges

Another important property is that the vectors assigned to two different, intersecting edges are orthogonal.

This is proved by `incompatible_edges_orthogonal`:

```coq
Theorem incompatible_edges_orthogonal :
  forall e f,
    edge_equal e f = false ->
    disjoint e f = false ->
    inner_product (edge_vector e)
                  (edge_vector f) = C0.
```

For example, `(V0,V2)` and `(V0,V3)` intersect at `V0`. Their assigned vectors therefore have inner product zero.

These are precisely the kinds of edge pairs that lose the game when both players have otherwise returned valid answers.

The next part of the formalization shows how this orthogonality property leads to zero probability in the actual quantum measurement model.

## 5. The shared entangled state

Alice and Bob begin with the six-dimensional maximally entangled state:

```text
Phi6 = (|0,0> + |1,1> + |2,2> +
        |3,3> + |4,4> + |5,5>) / sqrt(6)
```

`phi6_unscaled` constructs the sum of the six computational-basis tensor products. `phi6` then multiplies this sum by `1/sqrt(6)`.

Alice and Bob each have a six-dimensional system, so their combined state is represented by a 36-dimensional vector.

This is the state used in the measurement and probability calculations.

## 6. Alice and Bob's measurements

Each player uses the measurement basis corresponding to their input vertex.

Alice measures in the conjugate basis, while Bob measures in the original basis.

Since the basis vectors are stored as columns, the corresponding basis-change matrices are:

```text
Alice: transpose(B_a)
Bob:   adjoint(B_b)
```

Here `B_a` and `B_b` are the bases selected by Alice's and Bob's input vertices.

The combined operation is:

```text
transpose(B_a) tensor adjoint(B_b)
```

This tensor product is necessary because each matrix acts on a separate six-dimensional system.

The definitions `alice_basis_change`, `bob_basis_change`, and `joint_basis_change` represent these operations. `post_basis_state` applies the combined operation to the shared state `phi6`.

### Raw measurement outcomes

After applying their basis changes, Alice and Bob measure in the computational basis.

Alice receives a raw outcome `j` and Bob receives `k`. Each valid outcome is an integer from 0 through 5.

`raw_outcome_vector` constructs the joint computational-basis outcome:

```text
|j> tensor |k>
```

`raw_outcome_probability` then uses QuantumLib's `probability_of_outcome` to calculate the probability of obtaining this outcome from `post_basis_state`.

The probability is therefore calculated from the defined shared state and measurement operations.

## 7. Decoding measurement outcomes into edges

The game requires edge answers, but the quantum measurements return numbers.

`decode_outcome` takes a player's input vertex and raw measurement outcome and returns the corresponding incident edge.

For example, the decoding for `V2` is:

| Raw outcome | Decoded edge |
|---|---|
| 0 | (V0,V2) |
| 1 | (V1,V2) |
| 2 | (V2,V3) |
| 3 | (V2,V4) |
| 4 | (V2,V5) |
| 5 | (V2,V6) |

The decoder uses the ordering of the columns in the measurement-basis matrix.

The same edge may correspond to different raw outcomes at different vertices. For instance, outcome `1` at `V0` and outcome `0` at `V2` both decode to `(V0,V2)`.

This is why the players' raw measurement numbers cannot simply be compared to determine whether they win. The numbers must first be converted into graph edges.

The Coq proofs check three properties of the decoder:

- `decode_outcome_matches_basis` proves that a decoded edge corresponds to the correct measurement-basis column.
- `decoded_edge_incident` proves that every successfully decoded edge contains the player's input vertex.
- `decode_valid_outcome` proves that every raw outcome from 0 through 5 can be decoded.

`raw_wins` applies the game's winning condition to the decoded edges.

## 8. Connecting the raw measurements to the edge vectors

This is the main step connecting the explicit quantum measurements to the original edge-vector construction.

The raw measurement amplitude is calculated using the shared state after Alice and Bob have applied their basis changes.

`raw_outcome_probability_moved` uses an inner-product identity to rewrite this amplitude. Instead of applying the basis-change matrix to the state, it applies the adjoint of that matrix to the raw outcome.

Both expressions give the same amplitude, but the second form makes it easier to identify the edge vectors selected by the measurement outcomes.

`joint_basis_change_adjoint` simplifies the adjoint of the combined basis-change matrix.

`moved_raw_outcome_factors` then separates the transformed joint outcome into Alice's and Bob's individual vectors.

Using the decoder and the basis-column identities, I prove that:

```text
Alice's transformed outcome = conjugate(edge_vector e)

Bob's transformed outcome   = edge_vector f
```

Here `e` and `f` are the edges obtained by decoding Alice's and Bob's raw outcomes.

The proofs `moved_outcome_matches_edges_entry` and `moved_outcome_matches_edges_equiv` establish that the transformed joint outcome matches the tensor product of these vectors at every valid entry.

Finally, `raw_probability_matches_decoded_edges` proves:

```text
If j decodes to e and k decodes to f, then

raw_outcome_probability(a,b,j,k)
    =
quantum_edge_probability(e,f)
```

This is the link between the probabilities calculated from the measurement operations and the probabilities associated with the decoded edge vectors.

## 9. Deriving zero probability from the shared state

The next step calculates the edge-vector measurement amplitude directly from `phi6`.

`phi6_unscaled_amplitude` expands the six terms of the unnormalized shared state. `phi6_amplitude` then includes the normalization factor.

The resulting amplitude is:

```text
amplitude(e,f)
    =
conjugate(inner_product(u_e,u_f)) / sqrt(6)
```

Taking the squared magnitude gives the mathematical probability formula:

```text
P(e,f) = |inner_product(u_e,u_f)|^2 / 6
```

The amplitude identity is proved in Coq. The zero-probability proof uses it directly rather than relying on a separate theorem for the simplified probability formula.

If `e` and `f` are different, intersecting edges, `incompatible_edges_orthogonal` proves that their vectors have inner product zero.

The derived amplitude is therefore zero, so the Born-rule probability is also zero.

This is formalized by `quantum_edge_probability_zero_if_incompatible`.

### Applying this result to the game

`circuit_edge_probability` uses the quantum-derived probability for valid pairs of edge answers and assigns zero to invalid pairs.

The supporting lemmas show that this function assigns zero probability when Alice's answer is invalid, Bob's answer is invalid, or the two edges are different and intersect.

`K7Strategy.v` contains the general theorem `losing_probability_zero`, which combines these three properties. Applying it to `circuit_edge_probability` gives `circuit_edge_losing_probability_zero`.

`raw_probability_matches_game_edges` connects the edge-level result back to the probability of the actual raw measurement outcomes.

## 10. Main Coq proofs

Here is how the main results fit together.

| Coq result | Purpose |
|---|---|
| `B0_unitary` through `B6_unitary` | Prove that the seven measurement-basis matrices are unitary. |
| `incompatible_edges_orthogonal` | Prove that different, intersecting edges have orthogonal vectors. |
| `decode_outcome_matches_basis` | Connect decoded edges to the corresponding measurement-basis columns. |
| `raw_outcome_probability_moved` | Rewrite the raw measurement amplitude by moving the basis change onto the outcome. |
| `joint_basis_change_adjoint` | Simplify the adjoint of the combined basis change. |
| `moved_raw_outcome_factors` | Separate the transformed joint outcome into Alice's and Bob's vectors. |
| `alice_outcome_matches_edge` | Match Alice's transformed outcome to her conjugated edge vector. |
| `bob_outcome_matches_edge` | Match Bob's transformed outcome to his edge vector. |
| `moved_outcome_matches_edges_equiv` | Establish equivalence between the transformed outcome and the joint decoded-edge vector. |
| `raw_probability_matches_decoded_edges` | Prove that the raw measurement probability equals the decoded edge-vector probability. |
| `phi6_amplitude` | Derive the normalized measurement amplitude from the shared entangled state. |
| `quantum_edge_probability_zero_if_incompatible` | Use orthogonality and the amplitude identity to prove zero probability for incompatible edges. |
| `circuit_edge_losing_probability_zero` | Apply the general game theorem to the quantum-derived edge probability. |
| `raw_probability_matches_game_edges` | Connect the raw measurement probability to the game-level probability. |
| `raw_strategy_losing_probability_zero` | Prove that every losing pair of valid raw outcomes has probability zero. |

## 11. Final theorem

The main theorem in `K7Vectors.v` is:

```coq
Theorem raw_strategy_losing_probability_zero :
  forall a b j k,
    j < 6 -> k < 6 ->
    raw_wins a b j k = false ->
    raw_outcome_probability a b j k = 0%R.
```

For any input vertices `a` and `b`, and any valid six-dimensional raw outcomes `j` and `k`, if decoding those outcomes would cause Alice and Bob to lose the game, the probability of obtaining that pair of outcomes is exactly zero.

The proof follows the complete strategy:

```text
Input vertices
      |
      v
Choose Alice's and Bob's measurement bases
      |
      v
Apply their basis changes to Phi6
      |
      v
Measure raw outcomes j and k
      |
      v
Decode the outcomes into edges e and f
      |
      v
Connect the raw probability to the edge vectors
      |
      v
Use orthogonality and the derived amplitude
      |
      v
Prove every losing outcome has probability zero
```

The earlier `ideal_probability` and `ideal_strategy_losing_probability_zero` are retained in the file. They establish the result for an edge-overlap probability model.

The newer theorem goes further by deriving the relevant probabilities from the explicitly defined shared state and measurement operations.

The formalization uses ideal six-dimensional quantum systems and their measurement matrices. The final theorem is a result about this mathematical strategy rather than a compiled, gate-level circuit implementation.

## 12. Repository files

- [K7Graph.v](K7Graph.v) defines the graph, undirected edges, validity conditions, and game rules.
- [K7Strategy.v](K7Strategy.v) proves the general game-level zero-probability theorem.
- [K7Vectors.v](K7Vectors.v) contains the complex edge vectors, measurement bases, shared state, decoder, probability calculations, and final quantum-strategy proof.

The project uses QuantumLib for its matrix operations, quantum states, measurement probabilities, and supporting mathematical results.

## 13. Verification

The Coq development was compiled locally using the project's QuantumLib dependency.

The assumptions of the final theorem can be inspected in Coq using:

```coq
Print Assumptions raw_strategy_losing_probability_zero.
```
