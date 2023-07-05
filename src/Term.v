From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.Theory.

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

Remark term_spec (I B L : Type) (trm : term I B L) : is_in_ibl trm.
Proof. by case trm. Qed.

Definition iri_from_i (I B L : Type) (i : I) : term I B L := @Iri I B L i.
Definition bnode_from_b (I B L : Type) (b : B) : term I B L := @Bnode I B L b.
Definition lit_from_l (I B L : Type) (l : L) : term I B L := @Lit I B L l.

Remark i_in_ib (I B L:Type) (i : I) : is_in_ib (@iri_from_i I B L i).
Proof. done. Defined.

Remark b_in_ib (I B L:Type) (b : B) : is_in_ib (@bnode_from_b I B L b).
Proof. done. Defined.

Remark i_in_i (I B L:Type) (i : I) : is_in_i (@iri_from_i I B L i).
Proof. done. Defined.

Definition is_ground_term (I B L : Type) (trm : term I B L) : bool :=
  is_iri trm || is_lit trm.

Section Poly.
  Variables I B B1 B2 B3 L : Type.

  Definition relabeling_term B1 B2 mu (trm : term I B1 L) : term I B2 L :=
    match trm with
    | Bnode name => Bnode (mu name)
    | Iri i => Iri i
    | Lit l => Lit l
    end.
  Section blank_node_mapping.
    Variable mu : B -> B.
    Lemma bnodes_to_bnodes (t : term I B L) : is_bnode t -> is_bnode (relabeling_term mu t).
      Proof. by case t. Qed.

    Lemma relabeling_lit l : (relabeling_term mu (Lit l)) = Lit l.
      Proof. by []. Qed.

    Lemma relabeling_iri i : (relabeling_term mu (Iri i)) = Iri i.
      Proof. by []. Qed.
  End blank_node_mapping.

  (* Definition relabeling_term_alt B1 B2 (μ : (trm : term I B1 L) : term I B2 L := *)
  (*   match trm with *)
  (*   | Bnode name => Bnode (μ name) *)
  (*   | Iri i => Iri i *)
  (*   | Lit l => Lit l *)
  (*   end. *)

  Lemma relabeling_term_id (trm : term I B L) : relabeling_term id trm = trm.
  Proof. by case: trm. Qed.

  Lemma relabeling_term_comp trm (mu1 : B1 -> B2) (mu2 : B2 -> B3) :
    relabeling_term (mu2 \o mu1) trm = relabeling_term mu2 (relabeling_term mu1 trm).
  Proof. by case: trm. Qed.

  Lemma relabeling_term_preserves_is_in_ib (mu : B1 -> B2) (trm : term I B1 L) :
    is_in_ib  trm <-> is_in_ib (relabeling_term mu trm).
  Proof. by case: trm. Defined.

  Lemma relabeling_term_preserves_is_in_i (mu : B1 -> B2) (trm : term I B1 L) :
    is_in_i trm <-> is_in_i (relabeling_term mu trm).
  Proof. by case: trm. Defined.

  Lemma relabeling_term_ext (mu1 mu2 : B1 -> B2) :
    mu1 =1 mu2 -> relabeling_term mu1 =1 relabeling_term mu2.
  Proof. by move=> mupweq [//| // | b] /=; rewrite mupweq. Qed.

  Lemma relabeling_term_inj (mu : B1 -> B2) (inj_mu : injective mu) : injective (relabeling_term mu).
  Proof. move=> x y; case x; case y => // x' y'; case=> eq; rewrite ?eq //.
         by congr Bnode; apply inj_mu.
  Qed.

End Poly.

Section CodeTerm.

  Variables (I B L : Type).

  Implicit Type trm : term I B L.

  Definition code_term trm : GenTree.tree (I + B + L)%type :=
    match trm with
    | Iri i => GenTree.Node 0 (GenTree.Leaf (inl (inl i)) :: nil)
    | Lit l => GenTree.Node 1 (GenTree.Leaf (inr l) :: nil)
    | Bnode name => GenTree.Node 2 (GenTree.Leaf (inl (inr name)) :: nil)
    end.

  Definition decode_term (x : GenTree.tree (I + B + L)) : option (term I B L) :=
    match x with
    | GenTree.Node 0 (GenTree.Leaf (inl (inl i)) :: nil) => Some (Iri i)
    | GenTree.Node 1 (GenTree.Leaf (inr l) :: nil) =>  Some (Lit l)
    | GenTree.Node 2 (GenTree.Leaf (inl (inr name)) :: nil) => Some (Bnode name)
    | _ => None
    end.

  Lemma pcancel_code_decode : pcancel code_term decode_term.
  Proof. by case => [i | l | name]. Qed.

End CodeTerm.

Definition term_canEqMixin (I B L : eqType) := PcanEqMixin (@pcancel_code_decode I B L).
Canonical term_eqType (I B L : eqType) :=
  Eval hnf in EqType (term I B L) (term_canEqMixin I B L).

Section EqTerm.
  Variables I B L : eqType.
  Definition eqb_term (t1 t2 : term I B L) : bool :=
    match t1, t2 with
    | Lit l1,Lit l2 => l1 == l2
    | Bnode b1, Bnode b2=> b1 == b2
    | Iri i1, Iri i2 => i1 == i2
    | _,_ => false
    end.

  Lemma eqb_eq trm1 trm2 : (trm1 == trm2) = eqb_term trm1 trm2.
  Proof. rewrite /eq_op/Equality.op/code_term.
         case e: (eqb_term trm1 trm2); move: e; case trm1; case trm2=> //x y /=.
         by move=> /eqP ->; rewrite eqxx.
         by move=> /eqP ->; rewrite eqxx.
         by move=> /eqP ->; rewrite eqxx.
         by move=> H; apply /eqP; move=> []z; rewrite z eqxx in H.
         by move=> H; apply /eqP; move=> []z; rewrite z eqxx in H.
         by move=> H; apply /eqP; move=> []z; rewrite z eqxx in H.
  Qed.

End EqTerm.

Definition get_b_term (I B L : eqType) (t : (term I B L)) : option B :=
  if t is Bnode b then Some b else None.

Definition get_bs (I B L : eqType) (ts : seq (term I B L)) :=
  pmap (@get_b_term I B L) ts.

Definition term_canChoiceMixin (I B L : choiceType) :=
  PcanChoiceMixin (@pcancel_code_decode I B L).

Canonical term_choiceType (I B L : choiceType) :=
  Eval hnf in ChoiceType (term I B L) (term_canChoiceMixin I B L).

Definition term_canCountMixin (I B L : countType) :=
  PcanCountMixin (@pcancel_code_decode I B L).
Canonical term_countType (I B L : countType) :=
  Eval hnf in CountType (term I B L) (term_canCountMixin I B L).

Definition term_canPOrderMixin (I B L : countType) :=
  PcanPOrderMixin (@pickleK (term_countType I B L)).

Canonical term_POrderType (I B L : countType) :=
  Eval hnf in POrderType tt (term_countType I B L) (term_canPOrderMixin I B L).

