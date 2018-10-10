# `ImpureDemo`: importing OCaml functions as non-deterministic ones.

This repository contains a few demonstrations of using
[Impure](https://github.com/boulme/Impure) library located here at
[coq_src/Impure/](coq_src/Impure/) as a
[git-subrepo](https://github.com/ingydotnet/git-subrepo).

The principle of the `Impure` library is to encode the type `A -> B`
of an OCaml function as a type `A -> ?? B` in Coq, where `?? B` is the
type of an axiomatized monad that can be interpreted as `B -> Prop`.
In other word, this encoding abstracts an OCaml function as a function
returning a postcondition on its possible results (ie a relation
between its parameter and its result). Side-effects are simply
ignored. And reasoning on such a function is only possible in partial
correctness.

A major feature of this cooperation between Coq and OCaml typechecker
is to provide very simple
[parametric proofs](http://homepages.inf.ed.ac.uk/wadler/topics/parametricity.html)
about polymorphic OCaml functions.  They correspond here to prove, by
reasoning only on their type, that these functions preserve some
invariants.  As an example, we prove the partial correctness of a
generic memoizing fixpoint operator: see `rec_correct` lemma at the
end of [ImpLoops](coq_src/Impure/ImpLoops.v).  This lemma is applied
in [FibExample](coq_src/FibExample.v) to prove the partial correctness
of a memoized version of the naive Fibonacci function.  However,
currently, the soundness of these parametric proofs is still a
conjecture.

A more significant use case of [Impure](https://github.com/boulme/Impure) is provided by [satans-cert](https://github.com/boulme/satans-cert) -- a certified checker of (Boolean) sat-solver answers.
The ancester of `Impure` is also present in the [Verified Polyhedra Library](https://github.com/VERIMAG-Polyhedra/VPL).

## Credits

[Sylvain Boulmé](mailto:Sylvain.Boulme@univ-grenoble-alpes.fr).

## Installation

### Requirements

1. [ocaml](https://ocaml.org/docs/install.html). Tested with versions >= 4.05 and <= 4.07.0. (But other versions should work too).

2. [ocamlbuild](https://github.com/ocaml/ocamlbuild). Tested with version 0.12.0. (But other versions should work too).

3. [coq](https://coq.inria.fr/). Tested with versions >= 8.7.2 and <= 8.8.2. Here, other versions are likely to not work !

### Compilation

After cloning, just change directory for a building directory (see below), and run `make`.

## Code Overview

[coq_src/](coq_src/) contains the Coq sources. Other directories aims to build examples of binaries.

- [FibExample/](FibExample/) builds an executable from [coq_src/FibExample.v](coq_src/FibExample.v). It illustrates the use of [ImpLoops](coq_src/Impure/ImpLoops.v) in order to certify in Coq the memoized version of a naive recursive definition of Fibonacci's function.

- [CanonNatExample/](CanonNatExample/) builds an executable from [coq_src/CanonNatExample.v](coq_src/CanonNatExample.v). It illustrates the use of [ImpHCons](coq_src/Impure/ImpHCons.v) in order to define in Coq a hconsed Peano's numbers.

- [ImpRefExample/](ImpRefExample/) builds an executable from [coq_src/ImpRefExample.v](coq_src/ImpRefExample.v).
