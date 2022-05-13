From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Term.

  (* literals should be of Datatype type, is not important for the moment*)
  Variable I B L: eqType.

  Inductive term : Type :=
  | Iri (id: I) 
  | Lit (l : L) 
  | Bnode (name : B).


  Definition is_lit (t : term ): bool :=
    (match t with
     | Lit _ => true
     | _ => false
     end).

  Definition is_iri (t : term ) : bool :=
    (match t with
     | Iri _ => true
     | _ => false
     end).

  Definition is_bnode (t : term ) : bool :=
    (match t with
     | Bnode _ => true
     | _ => false
     end).

  Definition eqb_term (t1 t2 : term) : bool :=
    (match t1, t2 with
     | (Iri id1), (Iri id2) => id1 == id2
     | (Lit l1),(Lit l2) => l1 == l2
     | (Bnode b1),(Bnode b2) => b1 == b2
     | _,_ => false
     end).

  Definition is_in_ib (t : term) : bool :=
    is_iri t || is_bnode t.

  Definition is_in_i (t : term) : bool :=
    is_iri t.

  Definition is_in_ibl (t : term) : bool :=
    is_iri t || is_bnode t || is_lit t.

  Lemma term_eqP : Equality.axiom eqb_term.
  Proof.
    rewrite /Equality.axiom => x y.
    apply: (iffP idP) => //= [| ->]; rewrite /eqb_term; last by case y.
    case: x y=> [i1|l1|b1] [i2|l2|b2] //;
                          move=> /eqP eq; by rewrite eq.
  Qed.

  Canonical term_eqType := EqType term (EqMixin term_eqP).

  Definition relabeling_term (μ : B -> B) (t : term) : term :=
    match t with
    | Bnode name => Bnode (μ name)
    | _ => t
    end.

  Lemma relabeling_term_id (t: term) : relabeling_term id t = t.
  Proof. by case t. Qed.

  Lemma relabeling_term_comp (t: term) (μ1 μ2 : B -> B) : relabeling_term (μ2 \o μ1) t = (relabeling_term μ2 \o (relabeling_term μ1)) t.
  Proof. by case t. Qed.

  Lemma relabeling_term_id_p_I (t : term) (p: is_iri t) : is_iri (relabeling_term id t).
  Proof. by rewrite relabeling_term_id p. Qed.

  Lemma relabeling_term_id_p_L (t : term) (p: is_lit t) : is_lit (relabeling_term id t).
  Proof. by rewrite relabeling_term_id p. Qed.

  Lemma relabeling_term_id_p_B (t : term) (p: is_iri t) : is_iri (relabeling_term id t).
  Proof. by rewrite relabeling_term_id p. Qed.

  Lemma relabeling_term_ext (μ1 μ2 : B -> B) : μ1 =1 μ2 -> forall t, relabeling_term μ1 t = relabeling_term μ2 t.
  Proof. move => μpweq [//| // | b] /=. by rewrite μpweq. Qed.

  Lemma relabeling_term_preserves_is_in_ib (μ : B -> B) (t : term) :
    is_in_ib t <-> is_in_ib (relabeling_term μ t).
  Proof. by case t. Qed.

  Lemma relabeling_term_preserves_is_in_i (μ : B -> B) (t : term) :
    is_in_i t <-> is_in_i (relabeling_term μ t).
  Proof. by case t. Qed.

  Lemma relabeling_term_preserves_is_in_ibl (μ : B -> B) (t : term) :
    is_in_ibl t <-> is_in_ibl (relabeling_term μ t).
  Proof. by case t. Qed.

End Term.
