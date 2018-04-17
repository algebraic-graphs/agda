# The theory of algebraic graphs

[![Build Status](https://travis-ci.org/algebraic-graphs/agda.svg?branch=master)](https://travis-ci.org/algebraic-graphs/agda)

We use Agda to formalise the theory of [algebraic graphs](https://github.com/snowleopard/alga-paper)
and prove a few key theorems.

## Code overview

This repository is fully self-contained and does not depend on any Agda libraries. We use
[this Travis build script](https://github.com/scott-fleischman/agda-travis) for continuous
verification of the proofs. To verify whether your implementation is correct, 
you can invoke the `verify.sh` script.

Below we describe the purpose of all source files contained in the `src` directory.

* Inside the `Algebra` folder, we define the following structures:

  * `Dioid`, a semiring (or rng) where the `+` operation is idempotent.
  * `Bool`, an implementation of a dioid.
  * `ShortestDistance`, another instance.
  * `Graph`, an [algebraic graphs](https://github.com/snowleopard/alga-paper).
  * `LabelledGraph`, an extension of a `Graph`.

  for each of these there are three files:

  * `Structure.agda`, the main implementation.
  * `Structure/Reasoning.agda`, syntactic sugar for writing equational proofs.
  * `Structure/Theorems.agda`, some theorems of the structure.


* `Prelude` defines products, lists and other functionality for describing Haskell APIs.
* `API` defines key functions from the API of the algebraic-graphs library.
* `API/Theorems` proves theorems of the API.
