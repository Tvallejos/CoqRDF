# CoqRDF
[![Docker Coq Build](https://github.com/Tvallejos/rdf-model/workflows/Docker%20Coq%20Build/badge.svg?branch=main)](https://github.com/Tvallejos/rdf-model/actions?query=workflow:"Docker%20Coq%20Build")

Development of the RDF model using Coq and the Mathematical Components library.

## Meta

- Author(s):
  - Tomas Vallejos
  - Assia Mahboubi
- Compatible Coq versions: 8.19.1
- Additional dependencies: 
  - the [`Mathematical Components` Library](https://github.com/math-comp/math-comp) version 2.2.0
  
## Description

This library allows mechanized reasoning about the RDF model. 
It defines RDF graphs as duplicate-free sequences of triples; and operations on them, such as, blank node relabeling and RDF isomorphism.

## Installation

We recommend installing the dependencies via [OPAM](https://opam.ocaml.org/doc/Install.html) (using a fresh or up to date version of opam 2), and then build manually:

```sh
git clone https://github.com/Tvallejos/CoqRDF.git
cd CoqRDF
opam switch create CoqRDF 4.12.0
eval $(opam env)
opam pin add coq 8.19.1
opam pin add coq-mathcomp-ssreflect 2.2.0
make
```

