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

  Lemma triple_case t1 t2: t1 = t2 -> [&& (subject t1) == (subject t2),
        (predicate t1) == (predicate t2) &
          (object t1) == (object t2)].
  Proof. by case t1; case t2=> /= ? ? ? ? ? ? ? ? ? ? [] -> -> ->; rewrite !eqxx. Qed.

  Lemma tripleE t1 t2 : t1 == t2 = [&& (subject t1) == (subject t2),
        (predicate t1) == (predicate t2) &
          (object t1) == (object t2)].
  Proof. case e: [&& subject t1 == subject t2, predicate t1 == predicate t2 & object t1 == object t2].
         by move/and3P : e=> [/eqP eqs /eqP eqp /eqP eqo]; apply /eqP; apply triple_inj.
         by move/negP : e=> H; apply /negP; apply: contra_not H=> /eqP/triple_case.
  Qed.

  Corollary tripleNeqs t1 t2 : subject t1 != subject t2 -> t1 != t2.
  Proof. apply contraPT=> /=; rewrite negbK tripleE.
         by move=> /and3P[/eqP -> _ _]; apply /negP; rewrite negbK eqxx.
  Qed.

  Corollary tripleNeqp t1 t2 : predicate t1 != predicate t2 -> t1 != t2.
  Proof. apply contraPT=> /=; rewrite negbK tripleE.
         by move=> /and3P[_ /eqP -> _]; apply /negP; rewrite negbK eqxx.
  Qed.

  Corollary tripleNeqo t1 t2 : object t1 != object t2 -> t1 != t2.
  Proof. apply contraPT=> /=; rewrite negbK tripleE.
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

  Canonical triple_predType2 := PredType (pred_of_seq \o (bnodes_triple)).

  (* Variable t : triple I B L. *)
  (* Variable B' : eqType. *)
  (* Variable f : finType. *)
  (* Variable funn : {ffun f -> B'}. *)
  (* Variable fibn : (seq_sub (@bnodes_triple B t)). *)
  (* (* Check fibn : finType. *) *)
  (* Variable m : {ffun (seq_sub (@bnodes_triple B t)) -> Type}. *)

  (* (μ :  {ffun (seq_sub (bnodes g1)) -> B}) *)

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

Section OrderTriple.
  Variables I B L : orderType tt.

  Definition le_triple : rel (triple I B L) :=
    fun (x y : triple I B L)=>
      let (sx,px,ox,_,_) := x in
      let (sy,py,oy,_,_) := y in
      if (le_term sx sy) then
        true
      else (if (le_term sx sy) && (le_term px py) then
              true
            else (le_term sx sy) && (le_term px py) && le_term ox oy).

  (* Hypothesis r : rel I. *)
  (* Goal total r. *)
  (* Proof. move=> x y. apply/eqP. *)
  (*        move: H. *)
  (*        apply contraPT. *)

  (* Definition le_triple_eqs x y : le_triple x y -> le_term (subject x) (subject y). *)
  (* Proof. move=>  *)

  Definition lt_triple : rel (triple I B L) :=
    fun (x y : triple I B L)=> (negb (x == y)) && (le_triple x y).

  (* Infimum *)
  Definition meet_triple : (triple I B L) -> (triple I B L) -> (triple I B L) :=
    fun x y => (if lt_triple x y then x else y).

  (* Supremum *)
  Definition join_triple : (triple I B L) -> (triple I B L) -> (triple I B L) :=
    fun x y => (if lt_triple x y then y else x).

  Lemma lt_def : forall x y, lt_triple x y = (y != x) && (le_triple x y).
  Proof. by move=> x y; rewrite /lt_triple/negb eq_sym. Qed.

  Lemma meet_def : forall x y, meet_triple x y = (if lt_triple x y then x else y).
  Proof. by []. Qed.

  Lemma join_def : forall x y, join_triple x y = (if lt_triple x y then y else x).
  Proof. by []. Qed.

  Lemma le_total : total le_triple.
  Proof. move=> x y; have /(_ I B L) ltot := le_term_total.
         have /orP[] := ltot (subject x) (subject y);
         have /orP[] := ltot (predicate x) (predicate y);
         have /orP[] := ltot (object x) (object y);
         by case: x=> sx px ox ? ?; case: y=> sy py oy ? ? /= -> -> ->; rewrite ?orbT.
  Qed.

  Lemma lt_neq_total t1 t2 : t1 != t2 -> lt_triple t1 t2 || lt_triple t2 t1.
  Proof. by rewrite !lt_def /negb eq_sym=> -> /=; apply le_total. Qed.

  (* Lemma lt_neq_antisym t1 t2 : t1 != t2 -> lt_triple t1 t2 == ~~ lt_triple t2 t1. *)
  (* Proof. move=> neqT. rewrite !lt_def. /negb eq_sym=> -> /=; apply le_total. Qed. *)

  Lemma le_neq_antisym_triple t1 t2 : t1 != t2 -> le_triple t1 t2 == ~~ le_triple t2 t1.
  Proof.
    Abort.

    (* move=> /negP/negP ; rewrite tripleE !Bool.negb_andb=> /orP[]. *)
    (*      move=> H; have /le_neq_antisym /eqP /= : (subject t1 != subject t2) by []. *)
    (*      case: t1 H => [sx px ox sibx piix] ; case: t2=> [sy py oy siby piiy] /= H LH. *)
    (*      + move : (le_term_total sx sy)=> /orP[]. *)
    (*        - by rewrite LH=> H2; rewrite H2 -if_neg H2 -if_neg !negb_and H2 /= !negb_and H2. *)
    (*        - by move=> H2; rewrite LH /= H2 /=. *)
    (*      case/orP. *)
    (*      move=> H; have /le_neq_antisym /eqP /= : (predicate t1 != predicate t2) by []. *)
    (*      case: t1 H => [sx px ox sibx piix] ; case: t2=> [sy py oy siby piiy] /= H LH. *)
    (*      + move : (le_term_total px py)=> /orP[]. *)
    (*        - by rewrite LH=> H2; rewrite H2 -if_neg H2 -if_neg !negb_and H2 /= !negb_and H2. *)
    (*        - by move=> H2; rewrite LH /= H2 /=.  *)
         


    (*      move : (le_term_total px py)=> /orP[]. *)
    (*      rewrite H=> H2. rewrite H2 -if_neg H2. *)
    (*      rewrite -if_neg. rewrite -{2}if_neg. {2}H negbK. *)
    (*      rewrite H /=. *)
    (*      case: t1; sx *)
    (*      rewrite /le_triple H. *)

    (*      rewrite /le_triple. *)



  Lemma le_triple_antisym : antisymmetric le_triple.
  Proof. move=> x y. move=> H. apply/eqP. apply: contraPT H=> neqT.
         have neqTsym: y != x by rewrite /negb eq_sym.
         apply /negP. rewrite Bool.negb_andb.
         move: (lt_neq_total neqT).
         rewrite !lt_def neqT neqTsym /=. 
         rewrite /negb. case e: (x == y)=> // _.

         (* ========================== *)
    (*      move: e; rewrite tripleE=> /negP/negP. *)
    (*      rewrite !Bool.negb_andb. *)
    (*      case/orP. *)
    (*      + move=> neqs; apply /negP. rewrite Bool.negb_andb. *)
    (*      move/negP : e=> /negP. *)
         
    (*      apply /negP; rewrite Bool.negb_andb. apply /orP. *)
    (*      apply /nandP. *)

    (* move=> [sx px ox sibx piix] [sy py oy siby piiy] /= H. *)
    (*      apply triple_inj=> //=. *)
    (*      move: H=> /andP[hx hy]. *)
    (*      case/orP : hx hy=> hx /orP[] hy. *)
    (*      by apply le_term_antisym; rewrite hx hy. *)
    (*      case/orP : hy. *)
    (*      case e: hx. *)
    (*      => /andP[/ifP hx hy]. *)


    (*      /andP[/ifP hx hy]. [/orP [hx | hx] /orP hy]. *)
    (*      admit. *)
    (*      apply triple_inj=> //=; case/andP : H; case/orP=> lexlr /orP[] lexrl. *)
    (*      apply le_term_antisym. by apply /andP; split. *)
    (*      move/orP : lexrl=> []. *)


    (*      [lexrl f]. /le_term_antisym. => *)
  (*      move/andP : H. move:   => [/ifP h1 h2]. *)
         Abort.


  Lemma le_triple_trans : transitive le_triple.
  Proof. move=> [sx px ox sibx piix] [sy py oy siby piiy] [sz pz oz sibz piiz] //=.
         case/orP=> H.
         + case/orP=> H2.
           - by rewrite (le_term_trans H H2).
           - case/orP: H2=> /andP[H12 H22].
             * by rewrite (le_term_trans H H12).
             * by move/andP: H12=> [H112 H122]; rewrite (le_term_trans H H112).
         + case/orP: H.
         (*   move=> /andP [H12 H22]. suffices eqleq: forall a b, a == b -> le_term a b /\ le_term b a. *)
         (*   case e: (sx == sz). *)
         (*   apply eqleq in e. *)
         (*   move : e. move=> [H HH]. *)
         (*   rewrite H. *)
         (*   rewrite HH. *)


         (*   rewrite /le_term. case e: (eqb_term sx sz). *)
         (*   case: sx sibx H12 e; case: sy siby => x _ y _ lexy //=; case: sz sibz=> z _ //=. *)
         (*   move=> /eqP ->; rewrite Order.POrderTheory.lexx /=. move=> _. *)
         (*   apply/orP=> /=. *)
           


         (*   case/orP=> H2. by rewrite (le_term_trans H H2). *)

           (* exact: le_trans. Qed. *)
           Abort.


Definition triple_leOrderMixin :=
  Eval hnf in
    @LeOrderMixin (@triple_choiceType I B L)
      le_triple lt_triple meet_triple join_triple
      lt_def meet_def join_def
      le_triple_antisym le_triple_trans le_total.

Canonical my_triple_OrderType :=
  Eval hnf in OrderOfChoiceType tt triple_leOrderMixin.

Canonical my_triplePOrderType :=
  Eval hnf in Order.Total.porderType my_triple_OrderType.

End OrderTriple.

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
