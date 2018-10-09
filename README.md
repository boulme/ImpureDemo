# `ImpureDemo`: importing OCaml functions as non-deterministic ones.

The principle of the [Impure](https://github.com/boulme/Impure) library is to encode the type `A -> B` of an
OCaml function as a type `A -> ?? B` in Coq, where `?? B` is the type
of an axiomatized monad that can be interpreted as `B -> Prop`.  In
other word, this encoding abstracts an OCaml function as a function
returning a postcondition on its possible results (ie a relation between its
parameter and its result). Side-effects are simply ignored. And
reasoning on such a function is only possible in partial correctness.

This repository contains a few demonstrations of using `Impure` library.
The source of this library is located here at [coq_src/Impure/](coq_src/Impure/) as a [git-subrepo](https://github.com/ingydotnet/git-subrepo).

## Credits

[Sylvain Boulmé](mailto:Sylvain.Boulme@univ-grenoble-alpes.fr).

## Installation

### Requirements

1. [ocaml](https://ocaml.org/docs/install.html). Tested with versions >= 4.05 and <= 4.06.1. (But other versions should work too).

2. [ocamlbuild](https://github.com/ocaml/ocamlbuild). Tested with version 0.12.0. (But other versions should work too).

3. [coq](https://coq.inria.fr/). Tested with versions >= 8.7.2 and <= 8.8.1. Here, other versions are likely to not work !

### Compilation

After cloning, just change directory for a building directory (see below), and run `make`.

## Code Overview

[coq_src/](coq_src/) contains the Coq sources. Other directories aims to build examples of binaries.

- [CanonNatExample/](CanonNatExample/) builds an executable from [coq_src/CanonNatExample.v](coq_src/CanonNatExample.v).

- [FibExample/](FibExample/) builds an executable from [coq_src/FibExample.v](coq_src/FibExample.v).

- [ImpRefExample/](ImpRefExample/) builds an executable from [coq_src/ImpRefExample.v](coq_src/ImpRefExample.v).
