# The theory of algebraic graphs

[![Build Status](https://travis-ci.org/algebraic-graphs/agda.svg?branch=master)](https://travis-ci.org/algebraic-graphs/agda)

We use Agda to formalise the theory of [algebraic graphs](https://github.com/snowleopard/alga-paper)
and prove a few key theorems.

## Code overview

This repository is fully self-contained and does not depend on any Agda libraries. We use
[this Travis build script](https://github.com/scott-fleischman/agda-travis) for continuous
verification of the proofs.

Below we describe the purpose of all source files contained in the `src` directory.

* `Algebra` defines the equational theory of graphs.
* `Reasoning` provides standard syntax sugar for writing equational proofs.
* `Prelude` defines products, lists and other functionality for describing Haskell APIs.
* `API` defines key functions from the API of the algebraic-graphs library.
* `Algebra/Theorems` proves theorems of the algebra of graphs.
* `API/Theorems` proves theorems of the API.
