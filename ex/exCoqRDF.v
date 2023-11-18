From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
From RDF Require Export Rdf Triple Term Util.
From Coq Require Import Strings.String.

Open Scope string_scope.
Open Scope nat_scope.

Section Sets.

  Definition iri_t := string.
  Definition lit_t := (string * string)%type.
  Definition bn_t := nat.

End Sets.

Section Maps.

  Definition mu (b : nat) : nat :=
    match b with
    | 0 => 1
    | _ => b
    end.

End Maps.


Section Prelude.

  (* Transferring eqType infrastructure to the inductives *)
  Lemma str_eqP : Equality.axiom String.eqb. by move=> x y; apply eqb_spec. Qed.

End Prelude.

Canonical strE := Eval hnf in EqType string (EqMixin str_eqP).
Canonical iriE := Eval hnf in EqType iri_t (EqMixin str_eqP).
Canonical litE := Eval hnf in [eqType of lit_t].

Section TermsStr.

  (* Defining some terms and testing relabeling and equality on them. *)
  Definition I  := @Iri iri_t bn_t lit_t.
  Definition L  := @Lit iri_t bn_t lit_t.
  Definition Bn := @Bnode iri_t bn_t lit_t.

  Example relabeling_an_iri :
    (relabeling_term mu (I "isA")) == (I "isA") = true. by []. Qed.

  Example relabeling_a_blank_node :
    (relabeling_term mu (Bn 0)) == (Bn 1) = true. by []. Qed.

  Example relabeling_a_literal :
    (relabeling_term mu (L ("number","1781"))) == (I "1781") = false. by []. Qed.

End TermsStr.
Section TripleStr.

  (* Defining some triples and testing relabeling and equality on them. *)
  Definition mkT := @mkTriple iri_t bn_t lit_t.

  (* type alias *)
  Definition tr_t := triple iri_t bn_t lit_t.

  Definition z_isA_sonata : tr_t. by refine (@mkT (Bn 0) (I "isA") (I "sonata") _ _). Defined.
  Definition o_isA_sonata : tr_t. by refine (@mkT (Bn 1) (I "isA") (I "sonata") _ _). Defined.
  Definition o_year_1781 : tr_t. by refine (@mkT (Bn 1) (I "year") (L ("number","1781")) _ _). Defined.

  Example relabeling_a_triple_eq : relabeling_triple mu z_isA_sonata == o_isA_sonata. by []. Qed.

End TripleStr.
Section GraphStr.
  (* Defining some graphs and testing relabeling and equality on them. *)

  Definition OSonataG := mkRdf [:: o_isA_sonata; o_year_1781].
  Definition OSonataG_perm := mkRdf [:: o_year_1781 ; o_isA_sonata ].
  Definition ZSonataG := mkRdf [:: z_isA_sonata; o_year_1781].
  Definition relabeled_Z := (relabeling_undup mu ZSonataG).

  Example graphs_eq : eqb_rdf OSonataG OSonataG_perm = true. by []. Qed.
  Example graphs_relabel_eq : eqb_rdf relabeled_Z OSonataG = true. by []. Qed.
  Example graphs_prop_neq : ZSonataG == empty_rdf_graph = false. by []. Qed.

End GraphStr.

