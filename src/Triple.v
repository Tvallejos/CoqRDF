From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
From RDF Require Import Term.

Section Triple.

  Record triple (I B L : Type) := mkTriple { subject : (term I B L)
                                           ; predicate : (term I B L)
                                           ; object: (term I B L)
                                           ; subject_in_IB: is_in_ib subject
                                           ; predicate_in_I: is_in_i predicate
                                           ; object_in_IBL: is_in_ibl object
                                   }.

  Lemma triple_inj (I B L : Type) (t1 t2 : triple I B L) :
    subject t1 = subject t2 ->
    predicate t1 = predicate t2 ->
    object t1 = object t2 ->
    t1 = t2.
  Proof.
    case: t1 t2 => [s1 p1 o1 sin1 pin1 oin1] [s2 p2 o2 sin2 pin2 oin2] /= seq peq oeq.
    subst. by f_equal; apply eq_irrelevance.
  Qed.

  Section PolyTriple.

    Variables I B L : Type.
    Implicit Type t : triple I B L.

    Definition is_ground_triple t : bool:=
      let (s,p,o,_,_,_) := t in
      ~~ (is_bnode s || is_bnode p || is_bnode o).

    Definition relabeling_triple (B' B'': Type) (μ : B' -> B'')
               (t : triple I B' L) : triple I B'' L :=
      let (s,p,o,sin,pin,oin) := t in
      mkTriple ((iffLR (relabeling_term_preserves_is_in_ib μ s)) sin)
               ((iffLR (relabeling_term_preserves_is_in_i μ p)) pin)
               ((iffLR (relabeling_term_preserves_is_in_ibl μ o)) oin).

    Lemma relabeling_triple_id t : relabeling_triple id t = t.
    Proof.
      case t => [s p o sin pin oin] /=. apply triple_inj => /=; by apply relabeling_term_id. Qed.

    Lemma relabeling_triple_comp (B' B'' : Type) (μ1 : B -> B') (μ2 : B' -> B'') t :
      relabeling_triple (μ2 \o μ1) t = relabeling_triple μ2 (relabeling_triple μ1 t).
    Proof. by case t=> [s p o sin pin oin] ;apply triple_inj ; rewrite /= relabeling_term_comp. Qed.

    Section Relabeling_triple.
      Variable B' : Type.
      Implicit Type μ : B -> B'.

      Lemma relabeling_triple_preserves_is_in_ib μ t :
        is_in_ib (subject t) <-> is_in_ib (subject (relabeling_triple μ t)).
      Proof. by case t => s /= _ _ _ _ _; apply relabeling_term_preserves_is_in_ib. Qed.

      Lemma relabeling_triple_preserves_is_in_i μ t :
        is_in_i (predicate t) <-> is_in_i (predicate (relabeling_triple μ t)).
      Proof. by case t => _ p /= _ _ _ _; apply relabeling_term_preserves_is_in_i. Qed.

      Lemma relabeling_triple_preserves_is_in_ibl μ t :
        is_in_ibl (object t) <-> is_in_ibl (object (relabeling_triple μ t)).
      Proof. by case t => _ _ o /= _ _ _; apply relabeling_term_preserves_is_in_ibl. Qed.

      Lemma relabeling_triple_ext μ1 μ2:
        μ1 =1 μ2 -> forall t, relabeling_triple μ1 t = relabeling_triple μ2 t.
      Proof. by move=> μpweq t; apply /triple_inj; case t => /= [s p o _ _ _]; apply (relabeling_term_ext μpweq). Qed.

    End Relabeling_triple.
  End PolyTriple.

  Section EqTriple.
    Variable I B L : eqType.
    Implicit Type t : triple I B L.

    Definition eqb_triple  t1 t2 : bool :=
      ((subject t1) == (subject t2)) &&
        ((predicate t1) == (predicate t2)) &&
        ((object t1) == (object t2)).

    Lemma triple_eqP : Equality.axiom eqb_triple.
    Proof.
      rewrite /Equality.axiom /eqb_triple => x y.
      apply: (iffP idP) => //= [| ->];
                          case: x y=> [s1 p1 o1 sin1 pin1 oin1] [s2 p2 o2 sin2 pin2 oin2] //=.
      case/andP; case/andP=> /eqP eq_s/eqP eq_p/eqP eq_o.
      by apply triple_inj => /=.
      by rewrite !eq_refl //.
    Qed.

    Canonical triple_eqType := EqType (triple I B L) (EqMixin triple_eqP).

    Definition terms_triple t : seq (term I B L) :=
      let (s,p,o,_,_,_) := t in
      undup [:: s ; p ; o].

    Definition bnodes_triple t : seq (term I B L) :=
      undup (filter (@is_bnode _ _ _) (terms_triple t)).

  End EqTriple.

  Section CountTriple.
    Variables I B L : countType.
    Implicit Type t : triple I B L.

    Definition code_triple t :=
      let (s,p,o,_,_,_) := t in
      GenTree.Node 0 [:: (code_term s); (code_term p) ; (code_term o)].

    Definition decode_triple (x : GenTree.tree nat) : option (triple I B L).
    Proof. destruct x eqn:E.
           - exact None.
           - destruct n as [| n'].
             + destruct l as [| s [| p [| o]]] eqn:size.
               * exact None.
               * exact None.
               * exact None.
               * destruct l0.
                 -- destruct (decode_term I B L s) as [dst | ] eqn:ds;
                      destruct (decode_term I B L p) as [dpt | ] eqn:dp;
                      destruct (decode_term I B L o) as [ dot| ] eqn:do.
                                                                       destruct (is_in_ib dst) eqn:iib;
                                                                         destruct (is_in_i dpt) eqn:ii;
                                                                         destruct (is_in_ibl dot) eqn: ibl.

                                                                       ++ exact (Some (mkTriple iib ii ibl)).
                                                                       + all: exact None.
    Defined.

    Lemma cancel_triple_encode : pcancel code_triple decode_triple.
    Proof. case => s p o sib ii oibl. rewrite /code_triple /decode_triple.
           have cant: forall (trm : term I B L), decode_term I B L (code_term trm) = Some trm. apply cancel_code_decode.
           rewrite /= !cant; destruct s; destruct p ; destruct o => //=.
           all: by f_equal; apply triple_inj.
    Qed.

    Definition triple_canChoiceMixin := PcanChoiceMixin cancel_triple_encode.
    Definition triple_canCountMixin := PcanCountMixin cancel_triple_encode.

    Canonical triple_choiceType := Eval hnf in ChoiceType (triple I B L) triple_canChoiceMixin.
    Canonical triple_countType := Eval hnf in CountType (triple I B L) triple_canCountMixin.

    Definition triple_canPOrderMixin := PcanPOrderMixin (@pickleK triple_countType).
    Canonical triple_POrderType := Eval hnf in POrderType tt (triple I B L) triple_canPOrderMixin.

  End CountTriple.
End Triple.

