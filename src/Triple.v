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
                            ; subject_in_IB: is_in_ib subject == true
                            ; predicate_in_I: is_in_i predicate == true
                            ; object_in_IBL: is_in_ibl object == true
                    }. 

  Lemma eq_ir : forall (t1 t2 : term) (eqt : t1 = t2) (p: term -> bool),
      (p t1 == true) -> (p t2 == true).
  Proof. move=> t1 t2 eqt p. by rewrite eqt.
  Qed.

  Lemma triple_inj : forall (t1 t2: triple),
      subject t1 = subject t2 ->
      predicate t1 = predicate t2 ->
      object t1 = object t2 ->
      t1 = t2.
  Proof. move=> [s1 p1 o1 sin1 pin1 oin1] [s2 p2 o2 sin2 pin2 oin2] /= seq peq oeq. 
         have: sin2 = (eq_ir seq sin1).  apply eq_irrelevance.
         move => eqsin. rewrite eqsin. erewrite <-seq.
         have: pin2 = (eq_ir peq pin1). apply eq_irrelevance.
         move => eqpin. rewrite eqpin. erewrite <-peq.
         have: oin2 = (eq_ir oeq oin1). apply eq_irrelevance.
         move => eqoin. rewrite eqoin. erewrite <-oeq.
         move => //=. f_equal; apply eq_irrelevance.
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
    apply: triple_inj; move=> //= {sin1 sin2 pin1 pin2 oin1 oin2}; apply /eqP; by [].
    rewrite !eq_refl //.
  Qed.


  Canonical triple_eqType := EqType triple (EqMixin triple_eqP).

  Lemma relabeling_preserves_is_in_ib : forall (t : term) (p: is_in_ib t == true) (μ : B -> B),
      is_in_ib (relabeling t μ) == true.
  Proof. move=> t. case t; by [].
  Qed.
  Lemma relabeling_preserves_is_in_i : forall (t : term) (p: is_in_i t == true) (μ : B -> B),
      is_in_i (relabeling t μ) == true.
  Proof. move=> t. case t; by [].
  Qed.
  Lemma relabeling_preserves_is_in_ibl : forall (t : term) (p: is_in_ibl t == true) (μ : B -> B),
      is_in_ibl (relabeling t μ) == true.
  Proof. move=> t. case t; by [].
  Qed.
  
  Definition relabeling (t : triple) (μ : B -> B) : triple :=
    let (s,p,o,sin,pin,oin) := t in
    mkTriple (relabeling_preserves_is_in_ib sin μ)
             (relabeling_preserves_is_in_i pin μ)
             (relabeling_preserves_is_in_ibl oin μ).

End Triple.
