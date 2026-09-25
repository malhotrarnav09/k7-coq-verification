
# Coq Verification of the K7 Quantum Strategy

This repository contains my Coq formalization of the quantum strategy for the K7 perfect-matching game. I wrote it while learning Coq and QuantumLib.

The project formalizes the graph, the 21 complex edge vectors, and the seven measurement bases. It also explicitly represents the shared entangled state, Alice and Bob's basis-change matrices, their raw measurement outcomes, and the decoder that converts those outcomes into graph edges.

The main result proves that every losing pair of valid raw measurement outcomes has probability exactly zero under the ideal six-dimensional quantum strategy.

## 1. The K7 perfect-matching game

K7 is the complete graph on seven vertices:

`V0, V1, V2, V3, V4, V5, V6`

Every pair of distinct vertices is connected by an edge, giving 21 edges in total. Each vertex has exactly six incident edges.

### Rules of the game

A referee independently gives Alice and Bob an input vertex. They can agree on a strategy before the game but cannot communicate after receiving their inputs.

Each player must respond with an edge containing their assigned vertex.

For example, suppose Alice receives `V2` and Bob receives `V3`.

Alice's six possible valid answers are:

- `(V0,V2)`
- `(V1,V2)`
- `(V2,V3)`
- `(V2,V4)`
- `(V2,V5)`
- `(V2,V6)`

Bob can similarly return any of the six edges incident to `V3`.

Their two answers must satisfy the game's winning condition.

### Winning condition 1: Equal edges

Suppose Alice and Bob both return `(V2,V3)`.

Both answers contain the required input vertices, and the edges are identical. Therefore, they win.

This illustrates an important feature of the game: even when Alice and Bob receive different vertices, they can return the same edge if that edge joins their two input vertices.

### Winning condition 2: Disjoint edges

Suppose Alice returns `(V0,V2)` and Bob returns `(V1,V3)`.

Alice's answer contains `V2` and Bob's answer contains `V3`. The two edges share no vertex, so they are disjoint.

They therefore win.

### Losing condition 1: Different intersecting edges

Suppose Alice returns `(V0,V2)` and Bob returns `(V0,V3)`.

Both responses contain the correct input vertices. However, the two edges are different and share vertex `V0`.

They therefore lose.

This is the main type of losing output that the edge-vector orthogonality proof is designed to exclude.

### Losing condition 2: Invalid responses

Suppose Alice receives `V2` but returns `(V0,V1)`.

Her edge does not contain `V2`, so her response is invalid, regardless of Bob's answer.

A pair such as `(V2,V2)` is also not an edge of K7, because the graph has edges only between distinct vertices.

### When both players receive the same vertex

The game rules also apply when Alice and Bob receive the same input vertex.

For example, suppose they both receive `V2`. Any valid answer from either player must contain `V2`.

Two different valid answers would therefore intersect at `V2`, making them a losing pair. Consequently, when both players receive the same vertex, their valid answers must be identical to win.

The Coq function `wins` formalizes these winning and losing conditions. The final theorem applies to every pair of input vertices, including equal inputs.

## 2. Representing K7 in Coq

`K7Graph.v` defines the seven vertices and represents edges as pairs of vertices.

Because K7 is undirected, `(V1,V2)` and `(V2,V1)` represent the same edge.

The function `ordered_endpoints` places the endpoints into a canonical order. This allows edge equality and the edge-vector assignment to treat both orientations consistently.

For example, both orientations of the edge connecting `V1` and `V2` correspond to `v7`:

```coq
edge_vector (V1,V2) = v7
edge_vector (V2,V1) = v7
```

The graph formalization also defines the conditions for an edge to contain a vertex, for two edges to be equal, and for two edges to be disjoint.

These definitions are used throughout the probability proofs.

## 3. The 21 complex edge vectors

The quantum strategy assigns a vector in six-dimensional complex space to every edge of K7.

There are 21 such vectors, defined in `K7Vectors.v` as `v1` through `v21`.

The vectors are represented exactly, using entries such as `1/2`, `ω/2`, and `ω²/2`, where

\[
\omega=-\frac12+i\frac{\sqrt3}{2}.
\]

The formalization uses exact complex and real arithmetic rather than floating-point approximations.

### Normalization

Every edge vector is proved to be normalized:

\[
\langle u_e,u_e\rangle=1.
\]

This means each vector has unit length and can be used as a quantum measurement-basis vector.

The proofs include the normalization of the complex quantities involving `ω` and `ω²`, followed by the normalization of all 21 edge vectors.

## 4. The seven measurement bases

Every vertex has six incident edges, and their corresponding vectors form an orthonormal measurement basis.

For example, the basis for `V2` has the columns:

```text
v2, v7, v12, v13, v14, v15
```

These correspond respectively to:

```text
(V0,V2), (V1,V2), (V2,V3),
(V2,V4), (V2,V5), (V2,V6)
```

The seven basis matrices are `B0` through `B6`. Their columns are:

| Basis | Edge vectors |
|---|---|
| B0 | v1, v2, v3, v4, v5, v6 |
| B1 | v1, v7, v8, v9, v10, v11 |
| B2 | v2, v7, v12, v13, v14, v15 |
| B3 | v3, v8, v12, v16, v17, v18 |
| B4 | v4, v9, v13, v16, v19, v20 |
| B5 | v5, v10, v14, v17, v19, v21 |
| B6 | v6, v11, v15, v18, v20, v21 |

The proofs establish that these matrices are unitary:

\[
B_v^\dagger B_v=I_6.
\]

This follows from proving that each matrix is well-formed, that its columns are normalized, and that different columns are mutually orthogonal.

The results `B0_unitary` through `B6_unitary` establish this property for all seven measurement bases.

The function `vertex_basis` selects the basis matrix corresponding to an input vertex.

## 5. Orthogonality of incompatible edges

The main geometric property of the strategy is that two different, intersecting edges have orthogonal vectors.

This is formalized by:

```coq
Theorem incompatible_edges_orthogonal :
  forall e f,
    edge_equal e f = false ->
    disjoint e f = false ->
    inner_product (edge_vector e)
                  (edge_vector f) = C0.
```

For example, `(V0,V2)` and `(V0,V3)` are different but intersect at `V0`. Their assigned vectors are therefore orthogonal.

This is the geometric fact needed to exclude losing pairs in which both players return valid but incompatible edges.

However, orthogonality alone does not establish that the actual quantum measurement process assigns zero probability to those outputs.

The remaining formalization explicitly connects the edge vectors to the shared state, basis-change matrices, computational-basis measurements, and the Born rule.

## 6. The shared maximally entangled state

Alice and Bob share the six-dimensional maximally entangled state

\[
|\Phi_6\rangle=
\frac{1}{\sqrt6}
\sum_{i=0}^{5}|i\rangle_A\otimes|i\rangle_B.
\]

Written out, this is

\[
|\Phi_6\rangle=
\frac{1}{\sqrt6}
\left(
|00\rangle+|11\rangle+|22\rangle+
|33\rangle+|44\rangle+|55\rangle
\right).
\]

Alice and Bob each have a six-dimensional system, so the joint state belongs to a 36-dimensional space.

In Coq, `phi6_unscaled` explicitly defines the sum of the six computational-basis tensor products.

The definition `phi6` applies the normalization factor `1/sqrt 6`.

This gives us an explicitly represented quantum state from which to calculate the probabilities of measurement outcomes.

## 7. Alice and Bob's measurement operations

The measurement basis depends on the vertex each player receives.

If Alice receives vertex `a`, she measures in the conjugate of the basis associated with `a`. If Bob receives vertex `b`, he measures in the original basis associated with `b`.

Because the basis vectors are stored as matrix columns, the corresponding basis-change operations are:

\[
A_a=B_a^T
\]

for Alice and

\[
A_b=B_b^\dagger
\]

for Bob.

They are defined in Coq as `alice_basis_change` and `bob_basis_change`.

The combined operation is the tensor product

\[
U_{a,b}=B_a^T\otimes B_b^\dagger.
\]

This is represented by `joint_basis_change`.

The tensor product is necessary because Alice's matrix acts on her six-dimensional system while Bob's matrix acts on his own six-dimensional system.

The resulting state is

\[
|\psi_{a,b}\rangle
=
(B_a^T\otimes B_b^\dagger)|\Phi_6\rangle.
\]

The definition `post_basis_state` represents this operation explicitly.

## 8. Raw measurement outcomes and the decoder

After applying their basis changes, Alice and Bob measure in the computational basis.

Alice obtains a raw outcome `j` and Bob obtains `k`, each in the range `0` through `5`.

The joint computational-basis outcome is

\[
|j\rangle\otimes|k\rangle.
\]

Coq represents it using `raw_outcome_vector`.

The definition `raw_outcome_probability` uses QuantumLib's `probability_of_outcome` to calculate the probability of obtaining this joint result from `post_basis_state`.

### Converting numbers into edges

The game requires edge answers, not numbers. Each player therefore uses a decoder that takes the input vertex and the raw measurement outcome and returns the corresponding incident edge.

For example:

```coq
decode_outcome V2 1 = Some (V1,V2).
```

The decoder follows the ordering of the columns in each vertex's measurement basis.

For `V2`, the six outcomes correspond to:

| Raw outcome | Decoded edge |
|---|---|
| 0 | (V0,V2) |
| 1 | (V1,V2) |
| 2 | (V2,V3) |
| 3 | (V2,V4) |
| 4 | (V2,V5) |
| 5 | (V2,V6) |

A raw outcome can have a different meaning for a different input vertex.

For example:

```coq
decode_outcome V0 1 = Some (V0,V2)
decode_outcome V2 0 = Some (V0,V2)
```

Here Alice and Bob can produce different raw numbers but still return exactly the same graph edge.

This is why the game's winning condition must be checked after decoding, rather than by simply comparing the two raw measurement numbers.

The decoder also returns `None` for outcomes outside its six valid positions.

### Connecting the decoder to the basis columns

The theorem `decode_outcome_matches_basis` proves that, whenever a raw outcome decodes to an edge, the corresponding column of the vertex's measurement basis is exactly that edge's assigned vector.

The lemma `decoded_edge_incident` proves that every successfully decoded edge contains the player's input vertex.

These results ensure that the decoder agrees with both the quantum measurement bases and the rules of K7.

## 9. Connecting the actual measurement to the edge vectors

The central step in the revised proof is connecting the probability obtained from the basis-change operation to the probability associated with the decoded edge vectors.

The raw measurement amplitude is

\[
\langle j,k|
(B_a^T\otimes B_b^\dagger)
|\Phi_6\rangle.
\]

The proof first uses the inner-product identity

\[
\langle u|Av\rangle
=
\langle A^\dagger u|v\rangle
\]

to move the combined basis-change operation from the shared state to the computational-basis outcome.

This gives

\[
\left\langle
U_{a,b}^\dagger|j,k\rangle
\middle|
\Phi_6
\right\rangle.
\]

The reason for this rewrite is that applying the adjoint to the raw outcome exposes the measurement-basis vectors associated with `j` and `k`.

Using the adjoint and tensor-product identities, Coq then separates the transformed joint outcome into Alice's and Bob's individual vectors.

For Alice, the result is the complex conjugate of her decoded edge vector:

\[
\overline{u_e}.
\]

For Bob, the result is his ordinary decoded edge vector:

\[
u_f.
\]

The combined result is

\[
U_{a,b}^\dagger|j,k\rangle
=
\overline{u_e}\otimes u_f
\]

at the valid vector entries.

The supporting proofs include:

- `raw_outcome_probability_moved`
- `joint_basis_change_adjoint`
- `moved_raw_outcome_factors`
- `alice_outcome_matches_edge`
- `bob_outcome_matches_edge`
- `moved_outcome_matches_edges_entry`
- `moved_outcome_matches_edges_equiv`

Finally, `raw_probability_matches_decoded_edges` proves that, whenever the two raw outcomes decode to edges `e` and `f`,

\[
P_{\mathrm{raw}}(a,b,j,k)
=
P_{\mathrm{edges}}(e,f).
\]

This establishes the connection between the explicit quantum measurement process and the original edge-vector construction.

## 10. Deriving the amplitude from the entangled state

The next step calculates the amplitude of measuring the joint edge-vector state against the explicitly defined entangled state.

The proof expands the six terms of `phi6_unscaled` and establishes

\[
\left\langle
\overline{u}\otimes v
\middle|
\Phi_6
\right\rangle
=
\frac{1}{\sqrt6}
\langle u,v\rangle^*.
\]

Here the complex conjugate comes from the convention used for Alice's measurement vectors and QuantumLib's definition of the inner product.

This is established through `phi6_unscaled_amplitude` and `phi6_amplitude`.

Using the Born rule, the corresponding probability is

\[
P(e,f)
=
\frac16|\langle u_e,u_f\rangle|^2.
\]

The amplitude identity is formally proved. The exact `1/6` probability formula follows mathematically by taking its squared magnitude; the final Coq proof uses the amplitude identity directly rather than requiring a separate theorem for this simplified formula.

## 11. Proving that losing outcomes have zero probability

Suppose the decoded edges `e` and `f` are different and intersect.

The earlier geometric proof gives

\[
\langle u_e,u_f\rangle=0.
\]

Substituting this into the derived amplitude gives

\[
\frac{1}{\sqrt6}
\langle u_e,u_f\rangle^*
=0.
\]

The Born-rule probability is the squared magnitude of this amplitude, so

\[
P(e,f)=0.
\]

The theorem `quantum_edge_probability_zero_if_incompatible` formalizes this result.

### Combining the quantum probability with the game's rules

The definition `circuit_edge_probability` associates the circuit-derived edge probability with valid game answers and assigns zero to invalid edge answers.

Supporting lemmas establish the required zero-probability properties for invalid Alice answers, invalid Bob answers, and different intersecting edges.

These are combined through the general result in `K7Strategy.v` to prove `circuit_edge_losing_probability_zero`.

The theorem `raw_probability_matches_game_edges` then connects these edge-level results back to the raw measurement probabilities.

Because valid raw outcomes always decode to incident edges, the final result applies the game's losing condition directly to the decoded raw outcomes.

## 12. Final theorem

The main theorem of the revised formalization is:

```coq
Theorem raw_strategy_losing_probability_zero :
  forall a b j k,
    j < 6 -> k < 6 ->
    raw_wins a b j k = false ->
    raw_outcome_probability a b j k = 0%R.
```

For any input vertices `a` and `b`, and any valid raw measurement outcomes `j` and `k`, if decoding those outcomes would produce a losing pair of answers, their probability of occurring is exactly zero.

The proof connects the complete mathematical strategy:

```text
Input vertices a and b
          |
          v
Select measurement bases Ba and Bb
          |
          v
Prepare the shared state |Phi6>
          |
          v
Apply Ba^T tensor Bb†
          |
          v
Measure raw outcomes j and k
          |
          v
Decode outcomes into graph edges e and f
          |
          v
Apply the K7 winning condition
          |
          v
Every losing outcome has probability zero
```

The older `ideal_probability` definition and `ideal_strategy_losing_probability_zero` theorem are also retained in the project.

The difference is that the newer result explicitly derives the relevant probabilities from the shared quantum state, the basis-change matrices, and the computational-basis measurements, instead of starting from a manually specified edge-overlap probability.

## 13. General game-level theorem

`K7Strategy.v` contains the more general theorem `losing_probability_zero`.

It states that any probability function satisfying three conditions must assign probability zero to losing game outputs:

1. Invalid Alice edge answers have zero probability.
2. Invalid Bob edge answers have zero probability.
3. Different intersecting edge answers have zero probability.

The concrete quantum proof in `K7Vectors.v` supplies these conditions using the K7 edge vectors and the probabilities derived from the explicitly defined quantum state.

This separates the general game logic from the particular quantum strategy.

## 14. Files

- `K7Graph.v` defines the vertices, undirected edges, canonical edge ordering, and winning and losing conditions of the K7 game.
- `K7Strategy.v` proves the general theorem connecting the three zero-probability properties to every losing game output.
- `K7Vectors.v` defines the 21 complex edge vectors, proves the seven measurement bases are unitary, defines the shared entangled state and measurement operations, connects raw outcomes to decoded edge vectors, derives the amplitude identity, and proves the final zero-probability theorem.

## 15. Verification

All three Coq files compile successfully with the project's configured QuantumLib dependency.

The final theorem was also checked using:

```coq
Print Assumptions raw_strategy_losing_probability_zero.
```

Coq reports three assumptions from its mathematical libraries: two concerning classical real numbers and one concerning functional extensionality.

The project contains no remaining `Admitted`, `admit`, `Axiom`, or `Abort` declarations.
