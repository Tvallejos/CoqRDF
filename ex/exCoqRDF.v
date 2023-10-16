From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
From RDF Require Export Rdf Triple Term Util.
From Coq Require Import Strings.String.

Section Sets.

  (* Defining some sets for IRIs, blank nodes and literals. *)

  (* Inductive Iex := *)
  (* | isA *)
  (* | Sonata *)
  (* | Year. *)

  Inductive B1ex :=
  | A
  | B
  | C.

  Inductive B2ex :=
  | E
  | F.

  Inductive Lex :=
  | num (n : nat).

End Sets.

Section Maps.

  (* Defining some maps resulting in the same type domain or in another one. *)

  Definition mu (b : nat) : nat :=
    match b with
    | 0 => 1
    | _ => 0
    end.

  Definition nu (b: nat) : B1ex :=
    match b with
    | 0 => A
    | _ => B
    end.

End Maps.


Section Prelude.

  (* Transferring eqType infrastructure to the inductives *)

  (* Definition eqb_i (i1 i2 : Iex) := *)
  (*   match (i1, i2) with *)
  (*   | (isA, isA) | (Sonata,Sonata) | (Year,Year) => true *)
  (*   | (_,_) => false *)
  (*   end. *)

  Definition eqb_b1 (b1 b2 : B1ex) :=
    match (b1, b2) with
    | (A, A) | (B,B) | (C,C) => true
    | (_,_) => false
    end.

  Definition eqb_b2 (b1 b2 : B2ex) :=
    match (b1, b2) with
    | (E, E) | (F,F) => true
    | (_,_) => false
    end.

  Definition eqb_l (l1 l2 : Lex) :=
    match (l1, l2) with
    | ((num n), (num m)) => n == m
    end.

  Lemma str_eqP : Equality.axiom String.eqb. by move=> x y; apply eqb_spec. Qed.
  (* Lemma i_eqP : Equality.axiom eqb_i. by case; case; (try apply Bool.ReflectT=> //); apply Bool.ReflectF. Qed. *)
  Lemma b1_eqP : Equality.axiom eqb_b1. by case; case; (try apply Bool.ReflectT=> //); apply Bool.ReflectF. Qed.
  Lemma b2_eqP : Equality.axiom eqb_b2. by case; case; (try apply Bool.ReflectT=> //); apply Bool.ReflectF. Qed.
  Lemma l_eqP : Equality.axiom eqb_l.
  Proof. move=> [[|n']] [[|m']].
         + by apply Bool.ReflectT.
         + by apply Bool.ReflectF.
         + by apply Bool.ReflectF.
           apply: (iffP idP); first by rewrite /eqb_l=> /eqP ->.
           by move=> ->; rewrite /eqb_l eqxx.
  Qed.


  (* Canonical iE := Eval hnf in EqType Iex (EqMixin i_eqP). *)
  Canonical b1E := Eval hnf in EqType B1ex (EqMixin b1_eqP).
  Canonical b2E := Eval hnf in EqType B2ex (EqMixin b2_eqP).
  Canonical lE := Eval hnf in  EqType Lex (EqMixin l_eqP).
  Canonical strE := Eval hnf in EqType string (EqMixin str_eqP).
  Canonical strE := Eval hnf in EqType string (EqMixin str_eqP).


End Prelude.

Section TermsEx.

  (* Defining some terms and testing relabeling and equality on them. *)

  (* Definition I (i : Iex) {B : Type} := @Iri Iex B Lex i. *)
  (* Definition L (l : Lex) {B : Type} := @Lit Iex B Lex l. *)
  (* Definition Bn {B : Type} := @Bnode Iex B Lex. *)

  (* Definition isA1 := @I isA B1ex. *)
  (* Definition isA2 := @I isA B2ex. *)
  (* Definition sonata1 := @I Sonata B1ex. *)
  (* Definition sonata2 := @I Sonata B2ex. *)
  (* Definition year {B : Type} := @I Year B. *)
  (* Definition b := Bn B. *)
  (* Definition c := Bn C. *)
  (* Definition f := Bn F. *)
  (* Definition n1781 {B : Type} := @L (num 1781) B. *)


  (* Example relabeling_an_iri : (relabeling_term mu isA1) == isA1. by []. Qed. *)

  (* Example relabeling_a_blank_node : (relabeling_term mu b) == c. by []. Qed. *)

  (* Example relabeling_blank_node_type : (relabeling_term nu b) == f. by []. Qed. *)

End TermsEx.
Open Scope string_scope.
Open Scope nat_scope.
Section TermsStr.

  (* Defining some terms and testing relabeling and equality on them. *)
  Definition iri_t := string.
  Definition lit_t := (string * string)%type.
  Definition I (i : iri_t) {B : Type} := @Iri iri_t B lit_t i.
  Definition L (l : lit_t) {B : Type} := @Lit iri_t B lit_t l.
  Definition Bn {B : Type}:= @Bnode iri_t B lit_t.

  Definition isA_nat := (@I "isA" nat).
  Definition isA_b := (@I "isA" B1ex).
  Definition sonata := (@I "sonata" nat).
  Definition sonata_b := (@I "sonata" B1ex).
  Definition year {B : Type} := @I "year" B.
  (* Definition year {B : Type} := @I Year B. *)
  Definition a := Bn A.
  Definition z := Bn 0.
  Definition f := Bn 5.
  Definition n1781 {B : Type} := @L ("number","1781") B.


  Example relabeling_an_iri : (relabeling_term mu (@I "isA" nat)) == (@I "isA" nat). by []. Qed.

  Example relabeling_a_blank_node : (relabeling_term mu (Bn 0)) == (Bn 1). by []. Qed.

  Example relabeling_blank_node_type : (relabeling_term nu (Bn 0)) == (Bn A). by []. Qed.

End TermsStr.
Section TripleStr.

  (* Defining some triples and testing relabeling and equality on them. *)

  Definition mkTriple {B : Type} := @mkTriple iri_t B lit_t.

  (* type aliases *)
  Definition tr_b1 := triple strE nat lit_t.
  Definition tr_b2 := triple strE b1E lit_t.

  Definition z_isA_sonata : tr_b1. by refine (@mkTriple _ z isA_nat sonata _ _). Defined.
  Definition a_isA_sonata : tr_b2. by refine (@mkTriple _ (Bn A) isA_b sonata_b _ _). Defined.
  Definition o_isA_sonata : tr_b1. by refine (@mkTriple _ (Bn 1) isA_nat sonata _ _). Defined.
  Definition a_year_1781 : tr_b2. by refine (@mkTriple _ a year n1781 _ _). Defined.
  Definition o_year_1781 : tr_b1. by refine (@mkTriple _ (Bn 1) year n1781 _ _). Defined.

  Example relabeling_a_triple_eq : relabeling_triple mu z_isA_sonata == o_isA_sonata. by []. Qed.

  Example relabeling_a_triple_neq : relabeling_triple nu z_isA_sonata == a_year_1781 = false. by []. Qed.

End TripleStr.
Section GraphStr.
  (* Defining some graphs and testing relabeling and equality on them. *)

  (* type aliases *)
  Definition RDF_b1 := rdf_graph strE nat_eqType lit_t.
  Definition RDF_b2 := rdf_graph strE b1E lit_t.

  Definition BSonataG : RDF_b1. by refine (@mkRdfGraph _ _ _ [:: b_isA_sonata; b_year_1781] _). Defined.
  Definition relabeled_G : RDF_b2. by refine (@relabeling _ _ _ _ nu BSonataG _). Defined.
  Definition BSonataG_perm : RDF_b1. by refine (@mkRdfGraph _ _ _ [:: b_year_1781 ; b_isA_sonata ] _). Defined.
  Definition FSonataG : RDF_b2. by refine (@mkRdfGraph _ _ _ [:: f_isA_sonata; f_year_1781] _). Defined.

  Example graphs_eq : eqb_rdf BSonataG BSonataG_perm. by []. Qed.
  Example graphs_relabel_eq : eqb_rdf relabeled_G FSonataG. by []. Qed.
  Example graphs_prop_neq : BSonataG == empty_rdf_graph = false. by []. Qed.

End GraphEx.

Section TripleEx.

  (* Defining some triples and testing relabeling and equality on them. *)

  Definition mkTriple {B : Type} := @mkTriple Iex B Lex.

  (* type aliases *)
  Definition tr_b1 := triple iE b1E lE.
  Definition tr_b2 := triple iE b2E lE.

  Definition b_isA_sonata : tr_b1. by refine (@mkTriple _ b isA1 sonata1 _ _). Defined.
  Definition f_isA_sonata : tr_b2. by refine (@mkTriple _ f isA2 sonata2 _ _). Defined.
  Definition c_isA_sonata : tr_b1. by refine (@mkTriple _ c isA1 sonata1 _ _). Defined.
  Definition f_year_1781 : tr_b2. by refine (@mkTriple _ f year n1781 _ _). Defined.
  Definition b_year_1781 : tr_b1. by refine (@mkTriple _ b year n1781 _ _). Defined.

  Example relabeling_a_triple_eq : relabeling_triple mu b_isA_sonata == c_isA_sonata. by []. Qed.

  Example relabeling_a_triple_neq : relabeling_triple nu b_isA_sonata == f_year_1781 = false. by []. Qed.

End TripleEx.
Section GraphEx.
  (* Defining some graphs and testing relabeling and equality on them. *)

  (* type aliases *)
  Definition RDF_b1 := rdf_graph iE b1E lE.
  Definition RDF_b2 := rdf_graph iE b2E lE.

  Definition BSonataG : RDF_b1. by refine (@mkRdfGraph _ _ _ [:: b_isA_sonata; b_year_1781] _). Defined.
  Definition relabeled_G : RDF_b2. by refine (@relabeling _ _ _ _ nu BSonataG _). Defined.
  Definition BSonataG_perm : RDF_b1. by refine (@mkRdfGraph _ _ _ [:: b_year_1781 ; b_isA_sonata ] _). Defined.
  Definition FSonataG : RDF_b2. by refine (@mkRdfGraph _ _ _ [:: f_isA_sonata; f_year_1781] _). Defined.

  Example graphs_eq : eqb_rdf BSonataG BSonataG_perm. by []. Qed.
  Example graphs_relabel_eq : eqb_rdf relabeled_G FSonataG. by []. Qed.
  Example graphs_prop_neq : BSonataG == empty_rdf_graph = false. by []. Qed.

End GraphEx.



