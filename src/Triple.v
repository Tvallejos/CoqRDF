From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
From RDF Require Import Term.

Section Triple.

  Record triple {I B L : Type} := mkTriple { subject : @term I B L
                                           ; predicate : @term I B L
                                           ; object: @term I B L
                                           ; subject_in_IB: is_in_ib subject
                                           ; predicate_in_I: is_in_i predicate
                                           ; object_in_IBL: is_in_ibl object
                                   }.
  Section PolyTriple.
    Variables I B L : Type.

    Definition relabeling_triple (u' : Type) (μ : B -> u') (t : @triple I B L) : @triple I u' L :=
      let (s,p,o,sin,pin,oin) := t in
      mkTriple ((iffLR (relabeling_term_preserves_is_in_ib μ s)) sin)
               ((iffLR (relabeling_term_preserves_is_in_i μ p)) pin)
               ((iffLR (relabeling_term_preserves_is_in_ibl μ o)) oin).

    Definition terms_triple (t : @triple I B L) : seq term :=
      let (s,p,o,_,_,_) := t in
      [:: s ; p ; o].

    Definition bnodes_triple (t : @triple I B L) : seq (@term I B L) :=
      filter (@is_bnode I B L) (terms_triple t).

    Lemma triple_inj : forall (t1 t2: triple),
        subject t1 = subject t2 ->
        predicate t1 = predicate t2 ->
        @object I B L t1 = @object I B L t2 ->
        t1 = t2.
    Proof. move=> [s1 p1 o1 sin1 pin1 oin1] [s2 p2 o2 sin2 pin2 oin2] /= seq peq oeq.
           subst. by f_equal; apply eq_irrelevance.
    Qed.

    Lemma relabeling_triple_id (t : triple) : @relabeling_triple B id t = t.
    Proof.
      case t => [s p o sin pin oin] /=. apply triple_inj => /=; by apply relabeling_term_id. Qed.

    Lemma relabeling_triple_comp (μ1 μ2 : B -> B) (t : triple) : relabeling_triple (μ2 \o μ1) t = (@relabeling_triple B μ2 \o (relabeling_triple μ1)) t.
    Proof. case t=> [s p o sin pin oin] /=. apply triple_inj=> /=; by rewrite relabeling_term_comp. Qed.

    Lemma relabeling_triple_ext (μ1 μ2 : B -> B) : μ1 =1 μ2 -> forall t, relabeling_triple μ1 t = @relabeling_triple B μ2 t.
    Proof. move => μpweq t. apply /triple_inj; case t => /= [s p o _ _ _]; by apply (@relabeling_term_ext I B L μ1 μ2 μpweq). Qed.

    Lemma relabeling_triple_preserves_is_in_ib (u' : Type) (μ : B -> u') (t : @triple I B L) :
      is_in_ib (subject t) <-> is_in_ib (subject (relabeling_triple μ t)).
    Proof. case t => s /= _ _ _ _ _ /=. by apply relabeling_term_preserves_is_in_ib. Qed.

    Lemma relabeling_triple_preserves_is_in_i (u' : Type) (μ : B -> u') (t : @triple I B L) :
      is_in_i (predicate t) <-> is_in_i (predicate (relabeling_triple μ t)).
    Proof. by case t => _ p /= _ _ _ _; apply relabeling_term_preserves_is_in_i. Qed.

    Lemma relabeling_triple_preserves_is_in_ibl (u' : Type) (μ : B -> u') (t : @triple I B L) :
      is_in_ibl (object t) <-> is_in_ibl (object (relabeling_triple μ t)).
    Proof. by case t => _ _ o /= _ _ _; apply relabeling_term_preserves_is_in_ibl. Qed.


  End PolyTriple.
  Section EqTriple.
    Variable I B L : eqType.

    Definition eqb_triple  (t1 t2 : @triple I B L) : bool :=
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

  End EqTriple.

  Section CountTriple.
    Variables I B L : countType.

    Definition code_triple (t : @triple I B L) :=
      let (s,p,o,_,_,_) := t in
      GenTree.Node 0 [:: (code_term s); (code_term p) ; (code_term o)].

    Definition decode_triple (x : GenTree.tree nat) : option (@triple I B L).
    Proof. destruct x eqn:E.
           - exact None.
           - destruct n as [| n'].
             + destruct l as [| s [| p [| o]]] eqn:size.
               * exact None.
               * exact None.
               * exact None.
               * destruct l0.
                 -- destruct (@decode_term I B L s) as [dst | ] eqn:ds;
                      destruct (@decode_term I B L p) as [dpt | ] eqn:dp;
                      destruct (@decode_term I B L o) as [ dot| ] eqn:do.
                                                                        destruct (is_in_ib dst) eqn:iib;
                                                                          destruct (is_in_i dpt) eqn:ii;
                                                                          destruct (is_in_ibl dot) eqn: ibl.

                                                                        ++ exact (Some (mkTriple iib ii ibl)).
                                                                        + all: exact None.
    Defined.

    Lemma cancel_triple_encode : pcancel code_triple decode_triple.
    Proof. case => s p o sib ii oibl. rewrite /code_triple /decode_triple.
           have cant: forall (t : term), @decode_term I B L (code_term t) = Some t. apply cancel_code_decode.
           rewrite /= !cant; destruct s; destruct p ; destruct o => //=.
           all: by f_equal; apply triple_inj.
    Qed.

    Definition triple_canChoiceMixin := PcanChoiceMixin cancel_triple_encode.
    Definition triple_canCountMixin := PcanCountMixin cancel_triple_encode.

    Canonical triple_choiceType := Eval hnf in ChoiceType triple triple_canChoiceMixin.
    Canonical triple_countType := Eval hnf in CountType triple triple_canCountMixin.

    Definition triple_canPOrderMixin := PcanPOrderMixin (@pickleK triple_countType).
    Canonical triple_POrderType := Eval hnf in POrderType tt triple triple_canPOrderMixin.

  End CountTriple.
End Triple.

