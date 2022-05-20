From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
From RDF Require Import Term.

Section Triple.
  Variable I B L: eqType.
  Let term:= (term I B L).
  Let is_iri:= (@is_iri I B L).
  Let is_bnode:= (@is_bnode I B L).
  Let is_lit:= (@is_lit I B L).

  Record triple := mkTriple { subject : term
                            ; predicate : term
                            ; object: term
                            ; subject_in_IB: is_in_ib subject
                            ; predicate_in_I: is_in_i predicate
                            ; object_in_IBL: is_in_ibl object
                    }. 

  Lemma triple_inj : forall (t1 t2: triple),
      subject t1 = subject t2 ->
      predicate t1 = predicate t2 ->
      object t1 = object t2 ->
      t1 = t2.
  Proof. move=> [s1 p1 o1 sin1 pin1 oin1] [s2 p2 o2 sin2 pin2 oin2] /= seq peq oeq.
         subst. by f_equal; apply eq_irrelevance.
  Qed.

  Definition eqb_triple  (t1 t2 : triple) : bool :=
    ((subject t1) == (subject t2)) &&
      ((predicate t1) == (predicate t2)) &&
      ((object t1) == (object t2)).

  Lemma triple_eqP : Equality.axiom eqb_triple.
  Proof.
    rewrite /Equality.axiom => x y.
    apply: (iffP idP) => //= [| ->]; rewrite /eqb_triple; case: x y=> [s1 p1 o1 sin1 pin1 oin1] [s2 p2 o2 sin2 pin2 oin2] //=.
    case/andP; case/andP=> /eqP eq_s/eqP eq_p/eqP eq_o.
    apply: triple_inj; move=> //= {sin1 sin2 pin1 pin2 oin1 oin2}; by apply /eqP.
    by rewrite !eq_refl //.
  Qed.

  Canonical triple_eqType := EqType triple (EqMixin triple_eqP).

  Definition relabeling_triple (μ : B -> B) (t : triple) : triple :=
    let (s,p,o,sin,pin,oin) := t in
    mkTriple ((iffLR (relabeling_term_preserves_is_in_ib μ s)) sin)
             ((iffLR (relabeling_term_preserves_is_in_i μ p)) pin)
             ((iffLR (relabeling_term_preserves_is_in_ibl μ o)) oin).

  Lemma relabeling_triple_id (t : triple) : relabeling_triple id t = t.
  Proof.
    case t => [s p o sin pin oin] /=. apply triple_inj => /=; by apply relabeling_term_id. Qed.

  Lemma relabeling_triple_comp (μ1 μ2 : B -> B) (t : triple) : relabeling_triple (μ2 \o μ1) t = (relabeling_triple μ2 \o (relabeling_triple μ1)) t.
  Proof. case t=> [s p o sin pin oin] /=. apply triple_inj=> /=; by rewrite relabeling_term_comp. Qed.

  Lemma relabeling_triple_ext (μ1 μ2 : B -> B) : μ1 =1 μ2 -> forall t, relabeling_triple μ1 t = relabeling_triple μ2 t.
  Proof. move => μpweq t. apply /triple_inj; case t => /= [s p o _ _ _]; by apply (relabeling_term_ext μpweq). Qed.

  Definition terms_triple (t : triple) : seq term :=
    let (s,p,o,_,_,_) := t in
    [:: s ; p ; o].

  Definition bnodes_triple (t : triple) : seq term :=
    filter is_bnode (terms_triple t).

End Triple.
