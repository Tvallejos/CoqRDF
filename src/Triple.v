From HB Require Import structures.
From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
From RDF Require Import Term Util.

(******************************************************************************)
(* This file defines RDF triples by parameterizing three types for its        *)
(* IRIs, blank nodes, and literals.                                           *)
(* Every triple is well-formed, that is:                                      *)
(*   * its subject is an IRI or a blank node                                  *)
(*   * its predicate is an IRI and its object                                 *)
(*   * its object is an IRI, a blank node or a literal.                       *)
(*                                                                            *)
(* The definitions and theories of triples are divided in sections,           *)
(* which are organized by the required hypothesis to develop the theories     *)
(* of different operations.                                                   *)
(*                                                                            *)
(* For triples we define:                                                     *)
(*                                                                            *)
(*  ** Predicates                                                             *)
(*       trm \in t              == trm is either the subject, predicate,      *)
(*                                    or object of t.                         *)
(*       is_ground_triple t     == every term in t is not a blank node        *)
(*       lt_triple t1 t2        == t1 is less than or equal to t2.            *)
(*       le_triple t1 t2        == t1 is less than or equal to t2.            *)
(*       meet_triple t1 t2      == the meet of t1 and t2.                     *)
(*       join_triple t1 t2      == the join of t1 and t2.                     *)
(*                                                                            *)
(*  ** Blank node relabeling                                                  *)
(*       relabeling_triple mu t == the relabeling of every term of t under mu *)
(*                                                                            *)
(*  ** Projections                                                            *)
(*       terms_triple t         == the duplicate free sequence of terms in t  *)
(*       bnodes_triple t        == the duplicate free sequence of terms in t, *)
(*                                 which are blank nodes                      *)
(*                                                                            *)
(******************************************************************************)

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

  Remark triple_spec_wf t :
    is_in_ib (subject t) && is_in_i (predicate t) && is_in_ibl (object t).
  Proof. by case t=> ? ? []? /= -> ->. Qed.

  Definition is_ground_triple t : bool:=
    let (s,p,o,_,_) := t in
    ~~ (is_bnode s || is_bnode p || is_bnode o).

  Lemma is_ground_not_bnode t :
    is_ground_triple t =
      ~~ is_bnode (subject t) && ~~ is_bnode (predicate t) &&  ~~ is_bnode (object t).
  Proof. by case t => s p o /= _ _; rewrite -orbA !negb_or; case: s p o. Qed.

  Definition relabeling_triple B1 B2 (mu : B1 -> B2) (t : triple I B1 L) : triple I B2 L :=
    let (s, p, o, sin, pin) := t in
    mkTriple (relabeling_term mu o)
      ((iffLR (relabeling_term_preserves_is_in_ib mu s)) sin)
      ((iffLR (relabeling_term_preserves_is_in_i mu p)) pin).

  Lemma relabeling_triple_id t : relabeling_triple id t = t.
  Proof. by case t => * /=; apply triple_inj; apply relabeling_term_id. Qed.

  Lemma relabeling_triple_comp (B1 B2 B3 : Type) (mu1 : B1 -> B2) (mu2 : B2 -> B3) (t : triple I B1 L) :
    relabeling_triple (mu2 \o mu1) t = relabeling_triple mu2 (relabeling_triple mu1 t).
  Proof. by case t=> * ; apply: triple_inj ; rewrite /= relabeling_term_comp. Qed.

  Lemma map_of_triples t1 ft (f : B -> B): relabeling_term f (subject t1) = (subject ft) ->
                                                relabeling_term f (predicate t1) = predicate ft ->
                                                relabeling_term f (object t1) = object ft
                                                -> relabeling_triple f t1 = ft.
  Proof. by move=> rts rtp rto; apply triple_inj; rewrite -?rts -?rtp -?rto; case t1. Qed.

  Section Relabeling_triple.

    Variable B1 : Type.
    Implicit Type mu : B -> B1.

    Lemma ground_triple_relabeling t (mu : B -> B) : is_ground_triple t -> relabeling_triple mu t = t.
    Proof. by case: t => [[]]//s []//p []//=o /= sib pii _; apply triple_inj. Qed.

    Lemma relabeling_triple_preserves_is_in_ib mu t :
      is_in_ib (subject t) <-> is_in_ib (subject (relabeling_triple mu t)).
    Proof. by case t => s /= *; apply: relabeling_term_preserves_is_in_ib. Qed.

    Lemma relabeling_triple_preserves_is_in_i mu t :
      is_in_i (predicate t) <-> is_in_i (predicate (relabeling_triple mu t)).
    Proof. by case t => ? p /= *; apply: relabeling_term_preserves_is_in_i. Qed.

    Lemma relabeling_triple_ext mu1 mu2 :
      mu1 =1 mu2 -> relabeling_triple mu1 =1 relabeling_triple mu2.
    Proof.
      move=> μpweq t; apply: triple_inj; case t => /= *; exact: relabeling_term_ext.
    Qed.

    Lemma relabeling_triple_inj (mu : B -> B1) (mu_inj : injective mu) : injective (@relabeling_triple B B1 mu).
    Proof.
      have /(_ I L) rtmu_inj := (relabeling_term_inj mu_inj).
      by move=> [? ? ? ? ?] [? ? ? ? ?] // [] /rtmu_inj eq1 /rtmu_inj eq2 /rtmu_inj eq3; apply triple_inj.
    Qed.

    Lemma eq_relabeling_triple (mu nu : B -> B1) : mu =1 nu -> (relabeling_triple mu) =1 (relabeling_triple nu).
    Proof. by move=> feq [[]? []? []? ? ?]; apply /triple_inj=> //=; rewrite feq. Qed.

  End Relabeling_triple.

  Section Relabeling_triple_mem.
    Variables B1 B2 B3 : eqType.

    Lemma relabeling_triple_of_comp (mu : B2 -> B3) (nu : B1 -> B2) :
      ((relabeling_triple mu) \o (relabeling_triple nu)) =1 (relabeling_triple (mu \o nu)).
    Proof. by move=> t; rewrite relabeling_triple_comp. Qed.

  End Relabeling_triple_mem.

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

Section OperationsOnTriples.

  Variables I B L : eqType.
  Implicit Type t : triple I B L.

  Definition eqb_triple t1 t2 :=
    [&& (subject t1) == (subject t2),
      (predicate t1) == (predicate t2) &
        (object t1) == (object t2)].

  Lemma triple_case t1 t2: t1 = t2 -> eqb_triple t1 t2.
  Proof. case: t1; case :t2=> /= ? ? ? ? ? ? ? ? ? ? [].
         by rewrite /eqb_triple=> /=-> -> ->; rewrite !eqxx.
  Qed.

  Lemma triple_eqP : Equality.axiom eqb_triple.
  Proof.
    move=> x y. apply /(iffP idP).
    + by move/and3P => [/eqP eqs /eqP eqp /eqP eqo]; apply triple_inj.
      by apply triple_case.
  Qed.

  HB.instance Definition _ := hasDecEq.Build (triple I B L) triple_eqP.


  Corollary tripleNeqs t1 t2 : subject t1 != subject t2 -> t1 != t2.
  Proof. apply contraPT=> /=; rewrite negbK.
         by move=> /and3P[/eqP -> _ _]; apply /negP; rewrite negbK eqxx.
  Qed.

  Corollary tripleNeqp t1 t2 : predicate t1 != predicate t2 -> t1 != t2.
  Proof. apply contraPT=> /=; rewrite negbK.
         by move=> /and3P[_ /eqP -> _]; apply /negP; rewrite negbK eqxx.
  Qed.

  Corollary tripleNeqo t1 t2 : object t1 != object t2 -> t1 != t2.
  Proof. apply contraPT=> /=; rewrite negbK.
         by move=> /and3P[_ _ /eqP->]; apply /negP; rewrite negbK eqxx.
  Qed.

  Definition terms_triple (I' B' L' : eqType) (t : triple I' B' L') : seq (term I' B' L') :=
    let (s,p,o,_,_) := t in undup [:: s ; p ; o].

  Lemma terms_relabeled_triple_mem (B1 B2 : eqType) (t : triple I B1 L) (mu : B1 -> B2) :
    terms_triple (relabeling_triple mu t) =i map (relabeling_term mu) (terms_triple t).
  Proof. by case t=> s p o ? ? trm; rewrite mem_undup -mem_map_undup. Qed.

  Lemma terms_relabeled_triple (B1 B2 : eqType) (t : triple I B1 L)
    (mu : B1 -> B2) (inj_mu : injective mu) :
    terms_triple (relabeling_triple mu t) = map (relabeling_term mu) (terms_triple t).
  Proof. case t=> s p o ? ?.
         rewrite /relabeling_triple /terms_triple -undup_map_inj //; exact: relabeling_term_inj.
  Qed.

  Canonical triple_predType (I' B' L' : eqType):= PredType (pred_of_seq \o (@terms_triple I' B' L')).

  Lemma mem_triple_terms (trm : term I B L) (t : triple I B L) :
    trm \in t = [|| (trm == (subject t)),
        (trm == (predicate t)) |
        (trm == (object t))].
  Proof.
    suffices H: forall s x, mem_seq (undup s) x = mem_seq s x.
    by case: trm=> x; case : t=> s p o ? ? /=; rewrite -topredE /=;
    have ->: (if s \in [:: p; o]
     then if p \in [:: o] then [:: o] else [:: p; o]
              else s :: (if p \in [:: o] then [:: o] else [:: p; o])) = undup [:: s ; p ; o] by [];
       rewrite H /= Bool.orb_false_r.
    by move=> T s x; rewrite !topredE mem_undup.
  Qed.

  Definition bnodes_triple (t : triple I B L) : seq (term I B L) :=
    filter (@is_bnode I B L) (terms_triple t).

  Lemma Obnodes_groundtriple t : size (bnodes_triple t) == 0 = is_ground_triple t.
  Proof. rewrite sizeO_filter /terms_triple -all_filter; case t=> s p o.
         rewrite filter_undup all_undup.
         by case: s; case: p; case: o.
  Qed.

  Lemma is_ground_triple_bnodes_nil t : is_ground_triple t = (bnodes_triple t == [::]).
  Proof. by rewrite -Obnodes_groundtriple; case (bnodes_triple t). Qed.

  Lemma all_bnodes_triple_is_bnode t : all (@is_bnode I B L) (bnodes_triple t).
  Proof.
    case t=> s p o; rewrite /bnodes_triple/terms_triple=> _ _.
    rewrite filter_undup all_undup; exact: filter_all.
  Qed.

  Remark undup_bnodes_triple (t : triple I B L) : undup (bnodes_triple t) = bnodes_triple t.
  Proof. by case t=> ? ? ? ? ?; rewrite /bnodes_triple/terms_triple filter_undup undup_idem. Qed.

  Lemma i_in_bnodes_triple id t : Iri id \in bnodes_triple t = false.
  Proof. by rewrite /bnodes_triple mem_filter. Qed.

  Lemma l_in_bnodes_triple l t : Lit l \in bnodes_triple t = false.
  Proof. by rewrite /bnodes_triple mem_filter. Qed.

  Definition get_b_triple t : seq B.
  Proof. apply bnodes_triple in t as bns.
         elim bns => [|b bs ibs].
         + exact [::].
         + case b=> x.
           exact [::]. exact [::]. exact (undup (x::ibs)).
  Defined.

End OperationsOnTriples.
Section ChoiceTriple.
  Variable I B L: choiceType.

  HB.instance Definition _ :=
    Choice.copy (triple I B L) (pcan_type (@pcancel_code_decode I B L)).

End ChoiceTriple.

Section OrderTriple.
  Variable d : unit.
  Variables I B L : orderType d.

  Definition le_triple : rel (triple I B L) :=
    fun (x y : triple I B L)=>
      let (sx,px,ox,_,_) := x in
      let (sy,py,oy,_,_) := y in
      if (sx == sy) then
        if (px == py) then
          if (ox == oy) then true
          else le_term ox oy
        else  le_term px py
      else le_term sx sy.

  Definition lt_triple : rel (triple I B L) :=
    fun (x y : triple I B L)=> (negb (x == y)) && (le_triple x y).

  (* Infimum *)
  Definition meet_triple : (triple I B L) -> (triple I B L) -> (triple I B L) :=
    fun x y => (if lt_triple x y then x else y).

  (* Supremum *)
  Definition join_triple : (triple I B L) -> (triple I B L) -> (triple I B L) :=
    fun x y => (if lt_triple x y then y else x).

  Lemma lt_triple_def : forall x y, lt_triple x y = (y != x) && (le_triple x y).
  Proof. by move=> x y; rewrite /lt_triple/negb eq_sym. Qed.

  Lemma meet_triple_def : forall x y, meet_triple x y = (if lt_triple x y then x else y).
  Proof. by []. Qed.

  Lemma join_triple_def : forall x y, join_triple x y = (if lt_triple x y then y else x).
  Proof. by []. Qed.

  Lemma le_triple_total : total le_triple.
  Proof. move=> [sx px ox ? ?] [sy py oy ? ?] /=.
         case e: (sx == sy); rewrite (eq_sym sy sx) e; last by apply le_term_total.
         case e2: (px == py); rewrite (eq_sym py px) e2; last by apply le_term_total.
         by case e3: (ox == oy); rewrite (eq_sym oy ox) e3; last by apply le_term_total.
  Qed.

  Lemma lt_triple_neq_total t1 t2 : t1 != t2 -> lt_triple t1 t2 || lt_triple t2 t1.
  Proof. by rewrite !lt_triple_def /negb eq_sym=> -> /=; apply le_triple_total. Qed.

  Lemma le_triple_antisym t1 t2 : le_triple t1 t2 && le_triple t2 t1 -> t1 == t2.
  Proof. case: t1=> [sx px ox ? ?]; case: t2=> [sy py oy ? ?] /=.
         case e: (sx == sy); rewrite (eq_sym sy sx) e; last by move=> /le_term_anti/eqP; rewrite e.
         case e2: (px == py); rewrite (eq_sym py px) e2; last by move=> /le_term_anti/eqP; rewrite e2.
         case e3: (ox == oy); rewrite (eq_sym oy ox) e3 //; move=> ?; apply /eqP; apply triple_inj=> /=; apply /eqP=> //.
         by apply /eqP; apply le_term_anti.
  Qed.

  Lemma le_triple_anti : antisymmetric le_triple.
  Proof. by move=> t1 t2 /le_triple_antisym/eqP ->. Qed.

  Lemma le_triple_trans : transitive le_triple.
  Proof. move=> [sx px ox sibx piix] [sy py oy siby piiy] [sz pz oz sibz piiz] /=.
         repeat (let le := fresh "le" in case : ifP=> [/eqP ? | /eqP ? le] );
         subst=> //; rewrite ?eqxx;
         repeat (case : ifP=> // /eqP ?; subst)=> //;
         try (by apply: le_term_trans le le0);
         by move: (le_term_anticurr le le0)=> //.
  Qed.

End OrderTriple.

Fact triple_display : unit. exact tt. Qed.

HB.instance Definition _ (d : unit) (I B L: orderType d):=
  Order.isOrder.Build triple_display (triple I B L)
    (@lt_triple_def d I B L) (@meet_triple_def d I B L) (@join_triple_def d I B L)
    (@le_triple_anti d I B L) (@le_triple_trans d I B L) (@le_triple_total d I B L).
