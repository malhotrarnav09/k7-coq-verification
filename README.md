# Coq Verification of the K7 Quantum Strategy

This repository contains my first Coq formalization of the quantum strategy I used for the K7 perfect-matching game. I wrote it while learning Coq and QuantumLib.

## The game

K7 is a graph with seven vertices, with an edge between every pair of vertices. This gives 21 total edges.

A referee gives Alice one vertex and Bob another vertex. They cannot communicate after receiving their vertices. Each player must answer with an edge that contains the vertex they were given.

They win if their two edges are either:

- the same edge, or
- completely disjoint, meaning they do not share a vertex.

They lose if one player gives an invalid edge or if they give two different edges that intersect.

## Goal of the project

The quantum strategy assigns one six-dimensional complex vector to each of the 21 edges. The six edge vectors connected to any one vertex are supposed to form an orthonormal basis.

The main goal of this formalization was to prove that the ideal strategy never produces a losing answer. More precisely, every losing pair of output edges should have probability exactly zero.

## What is proved in Coq

The current files prove the following results:

- The seven vertices, 21 edges, and winning condition of the K7 game are represented in Coq.
- The exact 21 complex edge vectors from the strategy are defined without floating-point approximations.
- Each of the 21 edge vectors is normalized, so its inner product with itself is 1.
- The six vectors associated with each vertex form a unitary basis. This is proved for all seven basis matrices, `B0` through `B6`.
- If two edges are different and intersect, their assigned vectors are orthogonal, so their inner product is 0.
- The ideal output-probability function gives probability 0 when Alice or Bob returns an edge that does not contain their assigned vertex.
- The ideal output-probability function also gives probability 0 when the two output edges are different and intersect.
- The final theorem combines these facts and proves that every losing output has probability 0:

```text
wins a b e f = false
    -> ideal_probability a b e f = 0
```

There is also a more general theorem in `K7Strategy.v`. It proves that any probability function with the three zero-probability properties above must assign probability 0 to every losing output.

## How the probability is defined

For valid edge answers `e` and `f`, the ideal probability is

```text
(1/6) * |<edge_vector e, edge_vector f>|^2
```

The factor `1/6` comes from the shared six-dimensional maximally entangled state. If two different edges intersect, their vectors are orthogonal. Their inner product is therefore 0, so that pair of answers has probability 0.

## Files

- `K7Graph.v` defines K7 and the rules for winning and losing.
- `K7Strategy.v` proves the general theorem about losing outputs having probability 0.
- `K7Vectors.v` contains the edge vectors, basis matrices, probability definition, and the proofs for the concrete K7 strategy.

## What is not proved yet

This is a proof of the ideal mathematical strategy, not yet a verification of my executable Qiskit circuit. In particular, the current files do not yet prove that:

- all output probabilities sum to 1 for every input pair;
- the circuit is represented and verified in SQIR;
- a compiled gate decomposition is verified;
- hardware noise is modeled.
