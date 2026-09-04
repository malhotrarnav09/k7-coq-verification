# Formal Verification of a Quantum Strategy for the K7 Perfect-Matching Game

## The game

`K7` is the complete graph on seven vertices, so every pair of vertices is connected and there are 21 edges total.

In the game, a referee gives one vertex to Alice and one vertex to Bob. They cannot communicate after getting their inputs, and each player has to return an edge touching the vertex they received.

They win if:

- both players return the same edge, or
- they return two disjoint edges.

They lose if:

- either player returns an edge that does not touch their input vertex, or
- they return two different edges that share a vertex.

## Project goal

The quantum strategy is supposed to make every losing pair of answers have probability zero.

Each of the 21 edges is assigned a vector in six-dimensional complex space. For each vertex, the six vectors on the edges touching that vertex form an orthonormal basis. Alice and Bob share a six-dimensional maximally entangled state and use the bases connected to the vertices they receive.

For valid output edges `e` and `f`, the ideal probability is

```text
(1/6) * |<edge_vector e, edge_vector f>|^2.
```

If two different edges intersect, their vectors are perpendicular, so their inner product is zero. That makes the probability of that losing answer zero.

The point of this Coq project was to check that reasoning exactly instead of only testing it numerically in Qiskit. If Coq accepts a theorem, the proof has been checked from the definitions and earlier lemmas.

## Files

- `K7Graph.v` defines the graph and the rules of the game.
- `K7Strategy.v` proves the general logic for why the three kinds of losing outputs must have probability zero.
- `K7Vectors.v` defines the actual K7 vectors and basis matrices and proves that they have the properties the strategy needs.

## What I proved in Coq

Quick version:

- the full `K7` graph, its 21 edges, and the winning/losing rules;
- the exact 21 edge vectors in `C^6`;
- that the edge vectors are normalized;
- that the six edge vectors around each vertex form a unitary measurement basis;
- that two different edges sharing a vertex have orthogonal vectors;
- that invalid outputs and different intersecting-edge outputs get probability zero under `ideal_probability`;
- and finally, that every losing output pair has ideal probability zero.

The rest of this README goes through those pieces in more detail.

## Formalized results

### 1. Exact graph and winning predicate

`K7Graph.v` defines all seven vertices and all 21 edges. It also defines functions for checking:

- whether a vertex belongs to an edge;
- whether two edges are the same;
- whether two edges are disjoint;
- whether a full pair of answers wins the game.

I also included small examples for representative winning and losing cases so the definitions can be sanity-checked.

### 2. General zero-losing-probability theorem

`K7Strategy.v` starts with an arbitrary probability function. It assumes that the function gives probability zero when:

1. Alice returns an invalid edge;
2. Bob returns an invalid edge;
3. Alice and Bob return different intersecting edges.

The theorem `losing_probability_zero` proves that these three cases cover every possible way to lose. So any probability function satisfying those assumptions gives probability zero to every losing output.

### 3. Exact edge vectors

`K7Vectors.v` defines all 21 edge vectors in `C^6`. The construction uses the exact complex number

```text
omega = -1/2 + i*sqrt(3)/2
```

and its conjugate. I used exact expressions instead of floating-point approximations. Each graph edge is connected to its vector through `edge_vector`.

### 4. Normalized vectors

For the edge vectors, the development proves statements of the form

```text
inner_product v v = 1.
```

So the vectors have length one. Part of this required proving exact facts about `omega`, including its magnitude and the identity `(sqrt(3))^2 = 3`.

### 5. Unitary measurement bases

For each vertex, the six vectors on its incident edges are put into a `6 x 6` basis matrix, named `B0` through `B6`.

The proofs show that:

- each matrix is well formed;
- its columns are normalized;
- different columns are orthogonal;
- therefore the basis matrix is unitary.

`B0` is also proved equal to the identity matrix. Together, these results show that all seven vertex collections really are valid quantum measurement bases.

### 6. Graph rules connected to vector geometry

The theorem `incompatible_edges_orthogonal` checks the finite set of edge pairs and proves:

> If two edges are different and share a vertex, their assigned vectors have inner product zero.

This is the main connection between the graph rule for losing and the geometry of the quantum vectors.

### 7. Ideal output probabilities

The function `ideal_probability` gives probability zero to invalid outputs. For valid outputs, it uses the squared magnitude of the edge-vector inner product, multiplied by `1/6` from the shared six-dimensional entangled state.

Separate lemmas show that invalid answers get probability zero and that different intersecting edges also get probability zero.

### 8. Final result

The final theorem is `ideal_strategy_losing_probability_zero`:

```text
wins a b e f = false
    -> ideal_probability a b e f = 0.
```

In plain language:

> For any input vertices and any output edges, if those outputs lose the K7 game, the ideal strategy gives that output pair probability zero.

## Current scope

This project formalizes the exact mathematical structure behind the ideal K7 strategy. It does not yet prove that the executable Qiskit circuit implements that strategy.

It also does not yet:

- prove in Coq that all output probabilities sum to one for every input pair;
- derive `ideal_probability` directly from an explicit shared state and measurement program;
- represent and verify the circuit in SQIR;
- verify a compiled gate decomposition;
- model hardware noise.

