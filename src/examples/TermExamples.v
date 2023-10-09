From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
From RDF Require Import Term.


Check @Iri.
(* Iri   : forall I B L : Type, I -> term I B L *)
Check @Bnode.
(* Bnode : forall I B L : Type, B -> term I B L *)
Check @Lit.
(* Lit   : forall I B L : Type, L -> term I B L *)

Fail Check (@Lit bool nat nat 3) == (@Lit nat nat nat 3).
(* The command has indeed failed with message: *)
(* The term "Lit 3" has type "term nat nat nat" while it is expected to have type *)
(*  "Equality.sort (term_eqType bool_eqType nat_eqType nat_eqType)". *)

Open Scope nat.

Compute (@Iri nat nat nat 1) == (@Bnode nat nat nat 1).

Close Scope nat.


