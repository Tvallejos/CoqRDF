From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.Theory.
Section Term.

  (* literals should be of Datatype type, is not important for the moment*)
  Open Scope order_scope.

  Inductive term {I B L : Type} : Type :=
  | Iri (id: I)
  | Lit (l : L)
  | Bnode (name : B).

  Section Poly.
    Variables I B L : Type.

    Definition is_lit (t u v : Type) (t : @term t u v) : bool :=
      (match t with
       | Lit _ => true
       | _ => false
       end).

    Definition is_iri (t u v : Type) (t : @term t u v) : bool :=
      (match t with
       | Iri _ => true
       | _ => false
       end).

    Definition is_bnode (t u v : Type) (t : @term t u v) : bool :=
      (match t with
       | Bnode _ => true
       | _ => false
       end).

    Definition is_in_ib (t u v : Type) (t : @term t u v) : bool :=
      is_iri t || is_bnode t.

    Definition is_in_i (t u v : Type) (t : @term t u v) : bool :=
      is_iri t.

    Definition is_in_ibl (t u v : Type) (t : @term t u v) : bool :=
      is_iri t || is_bnode t || is_lit t.

    Definition relabeling_term (t u u' v : Type) (μ : u -> u') (trm : (@term t u v)) : @term t u' v :=
      match trm with
      | Bnode name => Bnode (μ name)
      | Iri i => Iri i
      | Lit l => Lit l
      end.

    Lemma relabeling_term_id (t: term) : @relabeling_term I B B L id t = t.
    Proof. by case t. Qed.

    Lemma relabeling_term_comp (t: term) (μ1 μ2 : B -> B) : relabeling_term (μ2 \o μ1) t = (@relabeling_term I B B L μ2 \o (relabeling_term μ1)) t.
    Proof. by case t. Qed.

    Lemma relabeling_term_preserves_is_in_ib (u' : Type) (μ : B -> u') (t : @term I B L) :
      is_in_ib t <-> is_in_ib (relabeling_term μ t).
    Proof. by case t. Qed.

    Lemma relabeling_term_preserves_is_in_i (u' : Type) (μ : B -> u') (t : @term I B L) :
      is_in_i t <-> is_in_i (relabeling_term μ t).
    Proof. by case t. Qed.

    Lemma relabeling_term_preserves_is_in_ibl (u' : Type) (μ : B -> u') (t : @term I B L) :
      is_in_ibl t <-> is_in_ibl (relabeling_term μ t).
    Proof. by case t. Qed.

    Lemma relabeling_term_ext (μ1 μ2 : B -> B) : μ1 =1 μ2 -> forall t : @term I B L, relabeling_term μ1 t = relabeling_term μ2 t.
    Proof. move => μpweq [//| // | b] /=. by rewrite μpweq. Qed.

  End Poly.
  Section EqTerm.
    Variables I B L : eqType.

    Definition eqb_term (t1 t2 : @term I B L) : bool :=
      match t1, t2 with
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

    Canonical term_eqType := EqType term (EqMixin term_eqP).

  End EqTerm.
  Section CountTerm.
    Variable I B L: countType.

    Definition code_term (x : (@term I B L)) :=
      match x with
      | Iri id => GenTree.Node 0 (GenTree.Leaf (pickle id) :: nil)
      | Lit l => GenTree.Node 1 (GenTree.Leaf (pickle l) :: nil)
      | Bnode name => GenTree.Node 2 (GenTree.Leaf (pickle name) :: nil)
      end.

    Definition decode_term (x : GenTree.tree nat) : option (@term I B L) :=
      match x with
      | GenTree.Node 0 (GenTree.Leaf id :: nil) => omap Iri (unpickle id)
      | GenTree.Node 1 (GenTree.Leaf l :: nil) =>  omap Lit (unpickle l)
      | GenTree.Node 2 (GenTree.Leaf name :: nil) => omap Bnode (unpickle name)
      | _ => None
      end.

    Lemma cancel_code_decode : pcancel code_term decode_term.
    Proof. case => [id | l | name]; by rewrite /= pickleK. Qed.

    Definition term_canChoiceMixin := PcanChoiceMixin cancel_code_decode.
    Definition term_canCountMixin := PcanCountMixin cancel_code_decode.

    Canonical term_choiceType := Eval hnf in ChoiceType term term_canChoiceMixin.
    Canonical term_countType := Eval hnf in CountType term term_canCountMixin.

    Definition term_canPOrderMixin := PcanPOrderMixin (@pickleK term_countType).
    Canonical term_POrderType := Eval hnf in POrderType tt term term_canPOrderMixin.

  End CountTerm.
End Term.

