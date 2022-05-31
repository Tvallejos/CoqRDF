From mathcomp Require Import all_ssreflect.
(* all_algebra. *)
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.Theory.
(* GRing.Theory Num.Theory. *)
Section Term.

  (* literals should be of Datatype type, is not important for the moment*)
  Open Scope order_scope.
  Variable I B L: countType.

  Inductive term : Type :=
  | Iri (id: I) 
  | Lit (l : L) 
  | Bnode (name : B).

  Definition code_term (x : term) :=
    match x with
    | Iri id => GenTree.Node 0 (GenTree.Leaf (pickle id) :: nil)
    | Lit l => GenTree.Node 1 (GenTree.Leaf (pickle l) :: nil)
    | Bnode name => GenTree.Node 2 (GenTree.Leaf (pickle name) :: nil)
    end.

  Definition unwrap {T U: Type} (ctor : T -> U) (x : option T) : option U :=
    match x with
    | Some t => Some (ctor t)
    | None => None
    end.

  Definition decode_term (x : GenTree.tree nat) : option term :=
    match x with
    | GenTree.Node 0 (GenTree.Leaf id :: nil) => unwrap Iri (unpickle id)
    | GenTree.Node 1 (GenTree.Leaf l :: nil) =>  unwrap Lit (unpickle l)
    | GenTree.Node 2 (GenTree.Leaf name :: nil) => unwrap Bnode (unpickle name)
    | _ => None
    end.

  Lemma cancel_code_decode : pcancel code_term decode_term.
  Proof. case => [id | l | name]; by rewrite /= pickleK. Qed.

  Definition term_eqMixin := PcanEqMixin cancel_code_decode.
  Definition term_canChoiceMixin := PcanChoiceMixin cancel_code_decode.
  Definition term_canCountMixin := PcanCountMixin cancel_code_decode.

  Canonical term_eqType := Eval hnf in EqType term term_eqMixin.
  Canonical term_choiceType := Eval hnf in ChoiceType term term_canChoiceMixin.
  Canonical term_countType := Eval hnf in CountType term term_canCountMixin.

  Definition term_canPOrderMixin := PcanPOrderMixin (@pickleK term_countType).
  Canonical term_POrderType := Eval hnf in POrderType tt term term_canPOrderMixin.

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

  Definition is_in_ib (t : term) : bool :=
    is_iri t || is_bnode t.

  Definition is_in_i (t : term) : bool :=
    is_iri t.

  Definition is_in_ibl (t : term) : bool :=
    is_iri t || is_bnode t || is_lit t.

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
