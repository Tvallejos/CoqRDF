From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
From RDF Require Import Term.

Section Triple.
  Variable I B L: countType.
  Let term:= (term I B L).
  Let is_iri:= (@is_iri I B L).
  Let is_bnode:= (@is_bnode I B L).
  Let is_lit:= (@is_lit I B L).
  Let code_term:= (@code_term I B L).
  Let decode_term:= (@decode_term I B L).

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

  Definition code_triple (t : triple) :=
    let (s,p,o,_,_,_) := t in
    GenTree.Node 0 [:: (code_term s); (code_term p) ; (code_term o)].

  (* Variable T : eqType. *)
  (* Variable p : T -> bool. *)
  (* Definition f ( x' : T) : option {x | p x}. *)
  (* Proof. destruct (p x') eqn:E. *)
  (*        - exact (Some (exist _ x' E)). *)
  (*        - exact None. *)
  (* Qed. *)

  Definition decode_triple (x : GenTree.tree nat) : option triple.
  Proof. destruct x eqn:E.
         - exact None.
         - destruct n as [| n'].
           + destruct l as [| s [| p [| o]]] eqn:size.
             * exact None.
             * exact None.
             * exact None.
             * destruct l0.
               -- destruct (decode_term s) as [dst | ] eqn:ds; destruct (decode_term p) as [dpt | ] eqn:dp ; destruct (decode_term o) as [ dot| ] eqn:do.
                                                                                                                                                        destruct (is_in_ib dst) eqn:iib; destruct (is_in_i dpt) eqn:ii; destruct (is_in_ibl dot) eqn: ibl.
                                                                                                                                                        ++ exact (Some (mkTriple iib ii ibl)).
                                                                                                                                                        -- repeat exact None.
                                                                                                                                                           all: exact None.
  Defined.
  
  Lemma cancel_triple_encode : pcancel code_triple decode_triple.
  Proof. case => s p o sib ii oibl. rewrite /code_triple /decode_triple.
         (* rewrite *)
         have cans: decode_term (code_term s) = Some s. apply cancel_code_decode.
         have canp: decode_term (code_term p) = Some p. apply cancel_code_decode.
         have cano: decode_term (code_term o) = Some o. apply cancel_code_decode.
         rewrite /= !cans !canp !cano.
         destruct s => //=; destruct p => //=; destruct o => //=.
         all: f_equal; apply triple_inj; rewrite /=; reflexivity.
         Qed. 
         
  Definition triple_eqMixin := PcanEqMixin cancel_triple_encode.
  Definition triple_canChoiceMixin := PcanChoiceMixin cancel_triple_encode.
  Definition triple_canCountMixin := PcanCountMixin cancel_triple_encode.

  Canonical triple_eqType := Eval hnf in EqType triple triple_eqMixin.
  Canonical triple_choiceType := Eval hnf in ChoiceType triple triple_canChoiceMixin.
  Canonical triple_countType := Eval hnf in CountType triple triple_canCountMixin.

  Definition triple_canPOrderMixin := PcanPOrderMixin (@pickleK triple_countType).
  Canonical triple_POrderType := Eval hnf in POrderType tt triple triple_canPOrderMixin.

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
