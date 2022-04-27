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

  Lemma eq_ir : forall (t1 t2 : term) (eqt : t1 = t2) (p: term -> bool),
      (p t1) -> (p t2).
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

  Lemma relabeling_preserves_is_in_ib (μ : B -> B) (t : term) :
    is_in_ib t <-> is_in_ib (relabeling μ t).
  Proof. by case t. Qed.

  (* Corollary id_preserves_is_in_ib ()  : type. *)
  (* Corollary relabeling_by_id : type. *)

  Lemma relabeling_preserves_is_in_i (μ : B -> B) (t : term) :
    is_in_i t <-> is_in_i (relabeling μ t).
  Proof. by case t. Qed.

  Lemma relabeling_preserves_is_in_ibl (μ : B -> B) (t : term) :
    is_in_ibl t <-> is_in_ibl (relabeling μ t).
  Proof. by case t. Qed.
  
  Definition relabeling (μ : B -> B) (t : triple) : triple :=
    let (s,p,o,sin,pin,oin) := t in
    mkTriple ((iffLR (relabeling_preserves_is_in_ib μ s)) sin)
             ((iffLR (relabeling_preserves_is_in_i μ p)) pin)
             ((iffLR (relabeling_preserves_is_in_ibl μ o)) oin).

  Lemma relabeling_id (t : triple) : relabeling id t = t.
  Proof.
    case t => [s p o sin pin oin] /=. apply triple_inj => /=; apply relabel_id. Qed.

  Lemma relabeling_comp (μ1 μ2 : B -> B) (t : triple) : relabeling (μ2 \o μ1) t = (relabeling μ2 \o (relabeling μ1)) t.
  Proof. case t=> [s p o sin pin oin] /=. apply triple_inj=> /=; by rewrite relabel_comp. Qed.

End Triple.
