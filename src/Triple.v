From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
From RDF Require Import Term Util.

Record triple (I B L : Type) :=
  mkTriple
    { subject : (term I B L)
    ; predicate : (term I B L)
    ; object: (term I B L)
    ; subject_in_IB: is_in_ib subject
    ; predicate_in_I: is_in_i predicate
    }.

Lemma triple_inj (I B L : Type) (t1 t2 : triple I B L) :
  subject t1 = subject t2 ->
  predicate t1 = predicate t2 ->
  object t1 = object t2 ->
  t1 = t2.
Proof.
  case: t1 t2 => [s1 p1 o1 sin1 pin1] [s2 p2 o2 sin2 pin2] /= seq peq oeq.
  subst; congr mkTriple; exact: eq_irrelevance.
Qed.

Section PolyTriple.

  Variables I B L : Type.
  Implicit Type t : triple I B L.

  Remark triple_spec_correct t :
    is_in_ib (subject t) && is_in_i (predicate t) && is_in_ibl (object t).
  Proof. by case t=> ? ? []? /= -> ->. Qed.

  Definition is_ground_triple t : bool:=
    let (s,p,o,_,_) := t in
    ~~ (is_bnode s || is_bnode p || is_bnode o).

  Definition relabeling_triple B1 B2 (μ : B1 -> B2) (t : triple I B1 L) : triple I B2 L :=
    let (s, p, o, sin, pin) := t in
    mkTriple (relabeling_term μ o)
      ((iffLR (relabeling_term_preserves_is_in_ib μ s)) sin)
      ((iffLR (relabeling_term_preserves_is_in_i μ p)) pin).

  Lemma relabeling_triple_id t : relabeling_triple id t = t.
  Proof. by case t => * /=; apply triple_inj; apply relabeling_term_id. Qed.

  Lemma relabeling_triple_comp (B1 B2 : Type) (μ1 : B -> B1) (μ2 : B1 -> B2) t :
    relabeling_triple (μ2 \o μ1) t = relabeling_triple μ2 (relabeling_triple μ1 t).
  Proof. by case t=> * ; apply: triple_inj ; rewrite /= relabeling_term_comp. Qed.

  Section Relabeling_triple.

    Variable B1 : Type.
    Implicit Type μ : B -> B1.

    Lemma relabeling_triple_preserves_is_in_ib μ t :
      is_in_ib (subject t) <-> is_in_ib (subject (relabeling_triple μ t)).
    Proof. by case t => s /= *; apply: relabeling_term_preserves_is_in_ib. Qed.

    Lemma relabeling_triple_preserves_is_in_i μ t :
      is_in_i (predicate t) <-> is_in_i (predicate (relabeling_triple μ t)).
    Proof. by case t => ? p /= *; apply: relabeling_term_preserves_is_in_i. Qed.

    Lemma relabeling_triple_ext μ1 μ2:
      μ1 =1 μ2 -> relabeling_triple μ1 =1 relabeling_triple μ2.
    Proof.
      move=> μpweq t; apply: triple_inj; case t => /= *; exact: relabeling_term_ext.
    Qed.

  End Relabeling_triple.
End PolyTriple.

Section CodeTriple.

  Variables (I B L : Type).

  Implicit Type tr : triple I B L.

  Definition code_triple tr : (term I B L * term I B L * term I B L)%type :=
    let: mkTriple s p o  _ _ := tr in (s, p, o).

  Definition decode_triple (t : (term I B L * term I B L * term I B L)%type) :=
    let: (s, p, o) := t in
    if insub s : {? x | is_in_ib x} is Some ss then
      if insub p : {? x | is_in_i x} is Some pp then
        Some (mkTriple o (valP ss) (valP pp))
      else None
    else None.

  Lemma pcancel_code_decode : pcancel code_triple decode_triple.
  Proof.
    case=> s p o ibs ip /=.
    case: insubP=> [u uP us |]; last by rewrite ibs.
    case: insubP=> [v vP vs |]; last by rewrite ip.
    by congr Some; apply: triple_inj.
  Qed.

End CodeTriple.

Definition triple_canEqMixin (I B L : eqType) := PcanEqMixin (@pcancel_code_decode I B L).
Canonical triple_eqType (I B L : eqType) :=
  Eval hnf in EqType (triple I B L) (triple_canEqMixin I B L).

Definition triple_canChoiceMixin (I B L : choiceType) :=
  PcanChoiceMixin (@pcancel_code_decode I B L).

Canonical triple_choiceType (I B L : choiceType) :=
  Eval hnf in ChoiceType (triple I B L) (triple_canChoiceMixin I B L).

Definition triple_canCountMixin (I B L : countType) :=
  PcanCountMixin (@pcancel_code_decode I B L).
Canonical triple_countType (I B L : countType) :=
  Eval hnf in CountType (triple I B L) (triple_canCountMixin I B L).

Definition triple_canPOrderMixin (I B L : countType) :=
  PcanPOrderMixin (@pickleK (triple_countType I B L)).

Canonical triple_POrderType (I B L : countType) :=
  Eval hnf in POrderType tt (triple_countType I B L) (triple_canPOrderMixin I B L).

(* assia : below not cleaned up *)
Section OperationsOnTriples.

  Variables I B L : eqType.
  Implicit Type t : triple I B L.

  Definition terms_triple (I' B' L': eqType) (t : triple I' B' L') : seq (term I' B' L') :=
    let (s,p,o,_,_) := t in undup [:: s ; p ; o].

  Lemma terms_relabeled_triple (B1 B2: eqType) (t : triple I B1 L)
    (mu: B1 -> B2) (inj_mu: injective mu) :
    terms_triple (relabeling_triple mu t) = map (relabeling_term mu) (terms_triple t).
  Proof. case t=> s p o ? ?.
         rewrite /relabeling_triple /terms_triple -undup_map_inj //; exact: relabeling_term_inj.
  Qed.

  Canonical triple_predType (I' B' L': eqType):= PredType (pred_of_seq \o (@terms_triple I' B' L')).

  Definition bnodes_triple (t : triple I B L) : seq (term I B L) :=
    filter (@is_bnode I B L) (terms_triple t).

  Lemma is_ground_not_bnode t :
    is_ground_triple t =
      ~~ is_bnode (subject t) && ~~ is_bnode (predicate t) &&  ~~ is_bnode (object t).
  Proof. by case t => s p o /= _ _; rewrite -orbA !negb_or; case: s p o. Qed.

  Lemma Obnodes_groundtriple t : size (bnodes_triple t) == 0 = is_ground_triple t.
  Proof. rewrite sizeO_filter /terms_triple -all_filter; case t=> s p o.
         rewrite filter_undup all_undup.
         by case: s; case: p; case: o.
  Qed.

  Canonical triple_predType2 := PredType (pred_of_seq \o (bnodes_triple)).

  (* Variable t : triple I B L. *)
  (* Variable B' : eqType. *)
  (* Variable f : finType. *)
  (* Variable funn : {ffun f -> B'}. *)
  (* Variable fibn : (seq_sub (@bnodes_triple B t)). *)
  (* (* Check fibn : finType. *) *)
  (* Variable m : {ffun (seq_sub (@bnodes_triple B t)) -> Type}. *)

  (* (μ :  {ffun (seq_sub (bnodes g1)) -> B}) *)

  Definition all_bnodes_triple_is_bnode t : all (@is_bnode I B L) (bnodes_triple t).
  Proof.
    case t=> s p o; rewrite /bnodes_triple/terms_triple=> _ _.
    rewrite filter_undup all_undup; exact: filter_all.
  Qed.

  Remark undup_bnodes_triple (t: triple I B L) : undup (bnodes_triple t) = bnodes_triple t.
  Proof. by case t=> ? ? ? ? ?; rewrite /bnodes_triple/terms_triple filter_undup undup_idem. Qed.

  Lemma i_in_bnodes_triple id t: Iri id \in bnodes_triple t = false.
  Proof. by rewrite /bnodes_triple mem_filter. Qed.

  Lemma l_in_bnodes_triple l t: Lit l \in bnodes_triple t = false.
  Proof. by rewrite /bnodes_triple mem_filter. Qed.

  Definition get_b_triple t : seq B.
  Proof. apply bnodes_triple in t as bns.
         elim bns => [|b bs ibs].
         + exact [::].
         + case b=> x.
           exact [::]. exact [::]. exact (undup (x::ibs)).
  Defined.

End OperationsOnTriples.

(* Section Relabeling_alt. *)

(*   Variables (I B L : countType).  *)

(*   (* Definition f (B1 B2 : countType) (t : triple I B1 L) (μ : {ffun (seq_sub (bnodes_triple t)) -> B2}) : *) *)
(*   (* Variable x : seq_sub (bnodes_triple ) *) *)

(*   (* Variable (t : triple I B L) (μ : {ffun (seq_sub (bnodes_triple t)) -> B}). *) *)
(*   (* Variable (x : (seq_sub (bnodes_triple t))). *) *)
(*   (* Check μ x. *) *)

(*   (* Definition f (t : triple I B L) : (seq_sub (bnodes_triple t)). *) *)
(*   (* Proof. exact: (seq_sub_of (bnodes_triple t)). *) *)




(*   Definition relabeling_triple_alt (B1 B2: countType) (t : triple I B1 L) (μ : {ffun (seq_sub (bnodes_triple t)) -> B2}) : triple I B2 L:= *)
(*     let (s, p, o, sin, pin) := t in *)
(*     if insub s : {? x | is_bnode x} is Some ss then *)
(*       if insub p : {? x | is_in_i x} is Some pp then *)
(*         if insub o : {? x | is_in_i x} is Some pp then *)
(*           todo _ *)
(*           else todo _. *)
(*     mkTriple (?? (μ o)) *)
(*              ((iffLR (relabeling_term_preserves_is_in_ib μ s)) sin) *)
(*              ((iffLR (relabeling_term_preserves_is_in_i μ p)) pin). *)
