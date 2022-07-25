From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.Theory.
Section Term.

  (* literals should be of Datatype type, is not important for the moment*)
  Open Scope order_scope.

  Inductive term (I B L : Type) : Type :=
  | Iri (id: I)
  | Lit (l : L)
  | Bnode (name : B).

  Arguments Iri {I B L}.
  Arguments Lit {I B L}.
  Arguments Bnode {I B L}.

  
  Definition is_lit (I B L : Type) (trm : term I B L) : bool :=
    match trm with
    | Lit _ => true
    | _ => false
    end.

  Definition is_iri(I B L : Type) (trm : term I B L) : bool :=
    match trm with
    | Iri _ => true
    | _ => false
    end.

  Definition is_bnode (I B L : Type) (trm : term I B L) : bool :=
    match trm with
    | Bnode _ => true
    | _ => false
    end.

  Definition is_in_ib (I B L : Type) (trm : term I B L) : bool :=
    is_iri trm || is_bnode trm.

  Definition is_in_i (I B L : Type) (trm : term I B L) : bool :=
    is_iri trm.

  Definition is_in_ibl (I B L : Type) (trm : term I B L) : bool :=
    is_iri trm || is_bnode trm || is_lit trm.


  Section Poly.
    Variables I B L : Type.
    Implicit Type trm : term I B L.

    Definition get_b_term trm : is_bnode trm -> B.
    Proof. rewrite /is_bnode=> is_b. case trm eqn:E;
             try discriminate is_b.
           exact name.
    Defined.

    Definition relabeling_term (B' B'' : Type) (μ : B' -> B'') (trm : (term I B' L)) : term I B'' L :=
      match trm with
      | Bnode name => Bnode (μ name)
      | Iri i => Iri i
      | Lit l => Lit l
      end.

    Lemma relabeling_term_id trm : relabeling_term id trm = trm.
    Proof. by case trm. Qed.

    Lemma relabeling_term_comp (B' B'' : Type) trm (μ1: B -> B') (μ2 : B' -> B'') :
      relabeling_term (μ2 \o μ1) trm = relabeling_term μ2 (relabeling_term μ1 trm).
    Proof. by case trm. Qed.

    Section Relabeling_term.
      Variable B' : Type.
      Implicit Type μ : B -> B'.

      Lemma relabeling_term_preserves_is_in_ib μ trm :
        is_in_ib  trm <-> is_in_ib (relabeling_term μ trm).
      Proof. by case trm. Qed.

      Lemma relabeling_term_preserves_is_in_i μ trm :
        is_in_i trm <-> is_in_i (relabeling_term μ trm).
      Proof. by case trm. Qed.

      Lemma relabeling_term_preserves_is_in_ibl μ trm :
        is_in_ibl trm <-> is_in_ibl (relabeling_term μ trm).
      Proof. by case trm. Qed.

      Lemma relabeling_term_ext μ1 μ2 :
        μ1 =1 μ2 -> forall trm, relabeling_term μ1 trm = relabeling_term μ2 trm.
      Proof. by move=> μpweq [//| // | b] /=; rewrite μpweq. Qed.

    End Relabeling_term.
  End Poly.

  Section EqTerm.
    Variables I B L : eqType.
    Implicit Type trm : term I B L.

    Definition eqb_term trm1 trm2 : bool :=
      match trm1, trm2 with
      | Iri i1, Iri i2 => i1 == i2
      | Bnode b1, Bnode b2 => b1 == b2
      | Lit l1, Lit l2 => l1 == l2
      | _, _ => false
      end.

    Lemma term_eqP : Equality.axiom eqb_term.
    Proof.
      rewrite /Equality.axiom => x y.
      apply: (iffP idP) => //= [| ->]; rewrite /eqb_term; last by case y.
      by case: x y=> [i1|l1|b1] [i2|l2|b2] // => /eqP ->.
    Qed.

    Canonical term_eqType := EqType (term I B L) (EqMixin term_eqP).

  End EqTerm.
  Section CountTerm.
    Variable I B L: countType.
    Implicit Type trm : term I B L.

    Definition code_term trm :=
      match trm with
      | Iri i => GenTree.Node 0 (GenTree.Leaf (pickle i) :: nil)
      | Lit l => GenTree.Node 1 (GenTree.Leaf (pickle l) :: nil)
      | Bnode name => GenTree.Node 2 (GenTree.Leaf (pickle name) :: nil)
      end.

    Definition decode_term (x : GenTree.tree nat) : option (term I B L) :=
      match x with
      | GenTree.Node 0 (GenTree.Leaf i :: nil) => omap (@Iri I B L) (unpickle i)
      | GenTree.Node 1 (GenTree.Leaf l :: nil) =>  omap (@Lit I B L) (unpickle l)
      | GenTree.Node 2 (GenTree.Leaf name :: nil) => omap (@Bnode I B L) (unpickle name)
      | _ => None
      end.

    Lemma cancel_code_decode : pcancel code_term decode_term.
    Proof. case => [i | l | name] /=; by rewrite pickleK. Qed.

    Definition term_canChoiceMixin := PcanChoiceMixin cancel_code_decode.
    Definition term_canCountMixin := PcanCountMixin cancel_code_decode.

    Canonical term_choiceType := Eval hnf in ChoiceType (term I B L) term_canChoiceMixin.
    Canonical term_countType := Eval hnf in CountType (term I B L) term_canCountMixin.

    Definition term_canPOrderMixin := PcanPOrderMixin (@pickleK term_countType).
    Canonical term_POrderType := Eval hnf in POrderType tt term_countType term_canPOrderMixin.

  End CountTerm.
End Term.

  Arguments Iri {I B L}.
  Arguments Lit {I B L}.
  Arguments Bnode {I B L}.
