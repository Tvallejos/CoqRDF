From mathcomp Require Import all_ssreflect fingraph.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
From RDF Require Export Rdf Triple Term Util.

Section HashedData.

  (* A type for a data (t : T) paired with its current hash (h : H) *)

  Variables (H T : Type).

  Inductive hash  := Hash of T * H.

  Definition input h :=  let: Hash th := h in th.1.

  Definition current_hash h := let: Hash th := h in th.2.

  Definition mkHinput (t : T) (h : H) := Hash (t, h).

  Definition pair_of_hash h := let: Hash th := h in th.

  Canonical hash_subType := [newType for pair_of_hash].


End HashedData.

(* Various transfers of structures *)
Definition hash_eqMixin (H T : eqType) := Eval hnf in [eqMixin of hash H T by <:].
Canonical hash_eqType (H T : eqType) :=
  Eval hnf in EqType (hash H T) (hash_eqMixin H T).
Lemma eq_i_ch (H T : eqType) (h1 h2: hash H T) : h1 == h2 = ((input h1) == (input h2)) && ((current_hash h1) == (current_hash h2)).
Proof. by case h1; case h2. Qed.

Definition hash_choiceMixin (H T : choiceType) := [choiceMixin of hash H T by <:].
Canonical hash_choiceType (H T : choiceType) :=
  Eval hnf in ChoiceType (hash H T) (hash_choiceMixin H T).
Definition hash_countMixin (H T : countType) := [countMixin of hash H T by <:].
Canonical hash_countType (H T : countType) :=
  Eval hnf in CountType (hash H T) (hash_countMixin H T).
Canonical hash_subCountType (H T : countType) :=
  Eval hnf in [subCountType of hash H T].

(* Waiting for inisight on using subtypes for automated transfer *)
Axiom hin_canPOrderMixin : forall (H T : countType), lePOrderMixin (hash_eqType H T).
Canonical hin_POrderType (H T : countType) :=
  Eval hnf in POrderType tt (hash H T) (hin_canPOrderMixin H T).


Section IsoCan.

  Variable I B L: countType.

  (*   Definition isocanonical_function (M : B -> B) (g : rdf_graph_) :=
    iso g (Rdf.relabeling M g) /\
      forall (h : rdf_graph_), iso g h <-> (relabeling M g) = (relabeling M h). *)

  Section IsoCanAlgorithm.

    Variable h : countType.
    Variables h0 hfwd hbwd hmark herror: h.
    Variable b0 : B.
    (* add conditions on the input *)
    Variable hashTerm : term I B L -> h.
    Hypothesis perfectHashingSchemeTerm : injective hashTerm.

    Implicit Type trm : term I B L.

    Local Notation hash := (hash h).

    Lemma by_perf_hash trm (o : h) (eqb : hashTerm trm == o) : hashTerm trm = o.
    Proof. apply /eqP. apply eqb. Qed.

    Definition hterm := term I (hash B) L.

    (* should this be a coercion? let's see *)
    Definition term_of_hterm (ht : hterm) : term I B L :=
      match ht with
      |Iri i => Iri i
      |Bnode hb => Bnode (input hb)
      |Lit l => Lit l
      end.

    Definition eqb_trm_hi trm (ht : hterm) : bool := trm == (term_of_hterm ht).

    Definition eqb_b_hterm b (ht : hterm) : bool :=
      if ht is Bnode hb then b == (input hb) else false.

    Definition htriple := triple I (hash B) L.

    Definition has_term_triple trm (trpl : htriple) : option hterm :=
      let (s,p,o,_,_) := trpl in
      if eqb_trm_hi trm s then Some s
      else if eqb_trm_hi trm p then Some p
           else if eqb_trm_hi trm o then Some o
                else None.

    Definition is_some {T : Type} (ot : option T) : bool :=
      match ot with Some _ => true | None => false end.

    Definition hgraph := rdf_graph I (hash B) L.

    Definition get t (g : hgraph) : option hterm :=
      let otrs := (map (has_term_triple t) (graph g)) in
      head None (filter is_some otrs).

    Definition lookup_hash (hb : hterm) : option (hash B) :=
      if hb is Bnode hin then some hin else None.

    Definition lookup_hash_default (hb : hterm) : h :=
      if hb is Bnode hin then current_hash hin else herror.

    Section Partition.

      Definition eq_hash (b1 b2 : hterm) : bool :=
        match (lookup_hash b1), (lookup_hash b2) with
        | Some hin1, Some hin2 => current_hash hin1 == current_hash hin2
        | _,_ => false
        end.

      Lemma eq_hash_refl b : is_bnode b -> eq_hash b b.
      Proof. rewrite /eq_hash /lookup_hash => isb. case: b isb; rewrite //.
      Qed.

      (* change for finset *)
      Fixpoint partitionate (f : hterm -> bool) (s : seq hterm) : seq hterm * seq hterm :=
        match s with
        | nil => (nil, nil)
        | x :: tl => let (g,d) := partitionate f tl in
                     if f x then (x::g,d) else (g,x::d)
        end.

      (* should be parameterized by a hgraph
         part shoud be the finset of (hash B) that shares hash in g *)
      Definition part := seq (hash B).

      (* the finset of parts in g *)
      Definition partition := seq part.

      Fixpoint someT_to_T {T : Type} (os : seq (option T)) : seq T :=
        match os with
        | nil => nil
        | Some t :: oss => t :: someT_to_T oss
        | None :: oss => someT_to_T oss
        end.

      Definition mkPartition (g : hgraph) : partition :=
        let bnodes := (bnodes g) in
        let equiv := (fun b => (fun t=> eq_hash b t)) in
        (* undup up to permutation *)
        let P := undup (map (fun b=> (partitionate (equiv b) bnodes).1 ) bnodes) in
        let ohs := map (fun bs => map lookup_hash bs) P in
        map someT_to_T ohs.

      Definition is_trivial (p : part) : bool :=
        size p == 1%N.

      Definition is_non_trivial (p : part) : bool :=
        ~~ is_trivial p.

      Definition is_fine (P : partition) : bool :=
        all is_trivial P.

      Definition is_coarse (P : partition) : bool :=
        size P == 1%N.

      Definition is_intermediate (P : partition) :=
        ~~ is_fine P && ~~ is_coarse P.

    End Partition.
    
    Definition init_bnode (b : B) : (hash B) :=
      mkHinput b h0.

    (* Algorithm 1, lines 2-8
       initializes every blank node with a known default name *)
    Definition init_hash (g : rdf_graph _ _ _) : hgraph :=
      relabeling init_bnode g.

    Hypothesis to_string : h -> B.
    Hypothesis inj_to_string : injective to_string.

    Definition label_bnode (hb : (hash B)) : B :=
      to_string (current_hash hb).

    (* Definition inj_label_bnode : injective label_bnode. move=> x y. rewrite /label_bnode. apply inj_to_string. case. by inj_to_string. *)

    Definition label_term (htrm : hterm) : term I B L :=
      relabeling_term label_bnode htrm.

    Definition label_triple ht : triple I B L :=
      relabeling_triple label_bnode ht.

    Definition label (g : hgraph) : rdf_graph I B L :=
      relabeling label_bnode g.

    (* assumes order and no dup in parts *)
    Definition cmp_part (p1 p2 : part) : bool :=
      all2 (fun b1 b2 => input b1 == input b2) p1 p2.

    (* assumes order and no dup in partition *)
    (* answers true if every part in the partition of g is equal to the respective part in h *)
    Definition cmp_partition (g h: hgraph) : bool :=
      let Pg := mkPartition g in
      let Ph := mkPartition h in
      all2 (fun p1 p2 => cmp_part p1 p2) Pg Ph.


    Variable hashBag : seq h -> h.
    Hypothesis hashBag_assoc : forall (l1 l2 l3: seq h),
        hashBag ([:: hashBag (l1 ++ l2)] ++ l3) = hashBag (l1 ++ [:: hashBag (l2 ++ l3)]).
    Hypothesis hashBag_comm : forall (l1 l2: seq h),
        hashBag (l1 ++ l2) = hashBag (l2 ++ l1).

    Variable hashTuple : seq h -> h.
    Hypothesis hashTuple_neq_init : forall s, hashTuple s == h0 = false.
    Hypothesis hashTuple_neq_error : forall s, hashTuple s == herror = false.
    Lemma hasTuple_neq_errorP s: hashTuple s = herror -> False.
    Proof. by apply /eqP; rewrite /negb hashTuple_neq_error. Qed.

    Hypothesis inj_hashTuple : injective hashTuple.


    (* Definition update_bnode_triple (b : )(t : triple I (hash B) L) : *)
    Definition term_hash (trm : hterm) : h :=
      match trm with
      | Iri x | Lit x => hashTerm (term_of_hterm trm)
      | Bnode hb => current_hash hb
      end.

    (* updates the current hash of b by b' in all the ocurrences
       in g *)
    Definition replace_bnode (b b': hash B) (g : hgraph) : hgraph :=
      relabeling (fun a_hash => if a_hash == b then b' else a_hash) g.


    Definition cmp_bnode (b : B) (ht : hterm) : bool :=
      match ht with
      | Bnode hin => b == (input hin)
      | _ => false
      end.

    Definition lookup_bnode_in_triple (b : B) (t : htriple) : option hterm :=
      let (s,p,o,_,_) := t in
      if cmp_bnode b s then Some s
      else if cmp_bnode b p then Some p
           else if cmp_bnode b o then Some o else None.

    Definition lookup_bnode_in_graph (g : hgraph) (b : B) : option hterm :=
      let otrms := map (lookup_bnode_in_triple b) g in
      head None (filter is_some otrms).

    Definition lookup_bnode_in_graph' (g : hgraph) (b : B) : option hterm :=
      match (filter (cmp_bnode b) (bnodes g)) with
      | nil => None
      | hb :: _ => Some hb
      end.

    Definition lookup_bnode_in_graph_default (g : hgraph) (b : B) : h :=
      if lookup_bnode_in_graph g b is Some trm then term_hash trm else herror.

    Definition new_hash (s p o : hterm) gacc hldr : option ((hash B) * (hash B)) :=
      if s is Bnode hb
      then
        let c := hashTuple [:: (term_hash o) ; (term_hash p) ; hldr] in
        let b_curr := lookup_bnode_in_graph_default gacc (input hb) in
        Some (hb,(mkHinput (input hb) (hashBag [:: c ; b_curr ])))
      else None.

    Definition new_hash_fwd (s p o: hterm) gacc : option ((hash B) * (hash B)) :=
      new_hash s p o gacc hfwd.

    Definition new_hash_bwd (s p o : hterm) gacc : option ((hash B) * (hash B)) :=
      new_hash o p s gacc hbwd.

    (* Algorithm 1, lines 12-17
       update the hashes of blank nodes using the neighborhood
       it hashes differently outgoing edges from incoming ones *)
    Definition update_bnodes (g : hgraph) : hgraph :=
      let fix help g gacc hf :=
        match g with
        | nil => gacc
        | cons t ts => let (s,p,o,_,_) := t : htriple in
                       let newhash := hf s p o gacc in
                       if newhash is Some (hb,hb')
                       then let gacc' := replace_bnode hb hb' gacc in
                            help ts gacc' hf
                       else help ts gacc hf
        end in
      let g_fwd := help g g new_hash_fwd in
      help g g_fwd new_hash_bwd.

    (* Algorithm 1, lines 9-18
       the iteration: computes the update of blank nodes until
           - the partition is fine
           - the partition did not change with respect to the previous one
     *)
    Fixpoint iterate (g : hgraph) (fuel : nat) : hgraph :=
      match fuel with
      | O => g
      | S n' =>
          let h := update_bnodes g in
          if cmp_partition g h || is_fine (mkPartition h) then h else
            iterate h n'
      end.


    Definition hashNodes_initialized (g : hgraph) : hgraph :=
      iterate g (size (graph g)).

    (* need the lemma stating hashNodes terminates without
       getting out of fuel *)
    (* Algorithm 1*)
    Definition hashNodes (g : rdf_graph _ _ _) : hgraph :=
      hashNodes_initialized (init_hash g).

    (* Definition 4.6 ≡ ~G *)
    Definition reachability_rel (g : hgraph) (t1 t2 : htriple) : bool :=
      let (s1, _, o1, _, _) := t1 in
      let (s2, _, o2, _, _) := t2 in
      let s1s2 := (s1 == s2) && is_bnode s1 in
      let s1o2 := (s1 == o2) && is_bnode s1 in
      let o1s2 := (o1 == s2) && is_bnode o1 in
      let o1o2 := (o1 == o2) && is_bnode o1 in
      s1s2 || s1o2 || o1s2 || o1o2.

    (* Algorithm 2, line 2:
       computes the connected components based on definition 4.6 (~G)
     *)
    Definition blank_node_split (t u v : Type) (g : rdf_graph t u v) : seq (rdf_graph t u v).
    Proof.
    (* compute the graph G,
         where V := g and
         (t,u) : (triple I B L * triple I B L) \in E iff
         [:: t ; u] is graph and bnodes(t) ∩ bnodes(u) ≠ ϕ

       Then compute the connected componens using reachability rel*)
    Admitted.


    (* The graph that contains all (and only the) ground triples of G *)
    Definition ground_split {t u v : Type} (g : rdf_graph t u v) : rdf_graph t u v :=
      let groundTriples := filter (fun t => is_ground_triple t) g in
      mkRdfGraph groundTriples.

    Lemma merge_split {t u v : Type} (g : rdf_graph t u v) :
      merge_rdf_graph (merge_seq_rdf_graph (blank_node_split g)) (ground_split g) = g. Admitted.

    (* Algorithm 2 *)
    Definition hashBnodesPerSplit (g : hgraph) : hgraph :=
      let splitG := blank_node_split g in
      foldr (@merge_rdf_graph _ _ _) (empty_rdf_graph _ _ _) splitG.


    (* Algorithm 3, line 13
       hashes b incorporating an arbitrary hash hmark *)
    Definition mark_hash (b : hash B) : hash B :=
      mkHinput (input b) (hashTuple [:: (current_hash b) ; hmark]).

    Definition mark_bnode (b : hterm) : hterm :=
      match b with
      | Iri i| Lit i => Bnode (mkHinput b0 herror)
      | Bnode hb=> Bnode (mark_hash hb)
      end.

    (* algorithm 3, lines 9-10
       chooses the canonical part which is not fine *)
    Fixpoint choose_part (P : partition) : part :=
      match P with
      | nil => nil (* FIXME: is this the good way to do it? *)
      | cons p t => if is_trivial p then choose_part t else p
      end.

    (* Algorithm 3, lines 13-14 when color refine is hashBnodes_initialized.
       b is_bnode *)
    Definition distinguishBnode g (color_refine : hgraph -> hgraph ) (b : hash B) : hgraph :=
      let b' := mark_hash b in
      let g' := replace_bnode b b' g in
      color_refine g'.

    (* choose canonical graph from sequence of graphs that have fine partitions *)
    Definition choose_graph (gs : seq hgraph) : hgraph :=
      if insub gs : {? x | all (is_fine \o mkPartition) x} is Some _
      then foldl Order.min (mkRdfGraph [::]) gs
      else mkRdfGraph [::].

    (* give partition and proof that partition is not fine *)
    (* or compute it again ... *)
    (* Algorithm 3, function distinguish, lines 9-20
       lines 16-18 were moved to a higher level: should consume more space
       FIXME just call distinguish_ with not fine partitions so
       is not needed to repeat the question *)
    Fixpoint distinguish_ g (color : hgraph -> hgraph) (fuel:nat) : hgraph :=
      match fuel with
      | O => g
      | S n' =>
          let P := mkPartition g in
          if is_fine P then g
          else
            let p := choose_part P in
            let gs := map (distinguishBnode g color) p in
            let just_fine := (fun g: hgraph =>
                                if is_fine (mkPartition g) then g
                                else distinguish_ g color n') in
            choose_graph (map just_fine gs)
      end.

    (* Algorithm 3, function distinguish
       when color_refine is hashBnodes_initialized *)
    Definition distinguish g (color_refine : hgraph -> hgraph) : hgraph :=
      distinguish_ g color_refine (size g).


    (* FIXME replace by padding function
     if ht in g then lookup in a finfun else
     just the input of the hterm *)
    Definition build_mapping_from_graph (g : hgraph) : B -> B :=
      let f := fun ht mapping =>
                 (fun b =>
                    if (input ht) == b
                    then (to_string (current_hash ht))
                    else mapping b) in
      foldr f id (get_b g).

    Definition build_mapping_from_graph' (g : hgraph) : B -> B :=
      let bns := bnodes g in
      fun b =>
        let p := eqb_b_hterm b in
        let default := (Bnode (mkHinput b herror)) in
        if has p bns then
          let the_bnode := nth default bns (find p bns) in
          to_string (lookup_hash_default the_bnode)
        else b.

    Definition map_fintype (T U: eqType) (s : seq T) (f : T -> U)
      (* (injF : injective f) *)
      : seq_sub s -> seq_sub (map f s).
    Proof. move=> arg.
           have ssval_arg: f (ssval arg) \in (map f s). apply (map_f f). apply (ssvalP arg). 
           exact (SeqSub ssval_arg).
    Qed.

    Definition build_finfun_from_graph (g : hgraph) : (seq_sub (bnodes g)) -> (seq_sub (map label_term (bnodes g))).
    Proof. apply map_fintype. Qed.

    (* label_term is injective only on terms when the hash partition *)
    (* returned the discrete partition.  *)
    (* Definition inj_label_term : injective label_term. *)
    (* Proof. move=> t1 t2. rewrite /label_term. *)
    (*        case t1; case t2=> x y //; rewrite /relabeling_term. *)
    (*        - by case=> ->.  *)
    (*        - by case=> ->.  *)
    (*        - Abort. *)

    

    (* Definition bf_from_graph_inj g : injective (build_finfun_from_graph g). *)

    Definition build_mapping_from_seq (trms : seq hterm) : B -> B :=
      fun b =>
        if has (eqb_b_hterm b) trms then
          let the_bnode := nth (Bnode (mkHinput b herror)) trms (find (eqb_b_hterm b) trms) in
          to_string (lookup_hash_default the_bnode)
        else
          b.

    (* nth_iota: forall (p m : nat) [n i : nat], (i < n)%N -> nth p (iota m n) i = m + i *)
    (* nth (Bnode (mkHinput x herror)) (mapi (app_n mark_bnode) (undup s)) *)
    (*                            (find (eqb_b_hterm x) (mapi (app_n mark_bnode) (undup s))) = *)


    Fixpoint app_n (T: Type)(f : T -> T) (x : T) (n:nat) :=
      match n with
      | O => x
      | S n' => f (app_n f x n')
      end.

    (* Lemma nth_iota_mark : forall (b : B) g [n i : nat], (i < n)%N -> nth p (init_bnodes ) i = app_n mark_bnode () m + i *)

    Definition k_distinguish bns : seq (term I (hash B) L) :=
      let fix help bns n :=
        match bns with
        | nil => nil
        | trm :: trms => app_n mark_bnode trm n :: help trms (S n)
        end in
      help bns 0.

    Definition mapi {A B : Type} (f : A -> nat ->  B) (s : seq A) : seq B :=
      map (fun an => (f an.1) an.2) (zip s (iota 0 (size s))).

    Definition ak_mapping (g : rdf_graph I B L) : seq hterm :=
      let bns := bnodes (init_hash g) in
      mapi (app_n mark_bnode) bns.

    (* Lemma mapi_marks_injective : injective (mapi (app_n mark_bnode)). *)
    (*   Proof. move=> x y. *)

    (* TODO uses app_n mark_node injective *)

    (* Lemma k_mapping_injectiveb g : dinjectiveb (fun an=> app_n mark_bnode an.1 an.2) (seq_sub (bnodes (init_hash g))). *)

    Definition fun_to_fin (T : eqType) (s : seq T) (f : T -> T) : seq_sub s -> T:=
      fun s0=> let (ssval,_) := s0 in (f ssval).

    Lemma inj_init_bnode : injective init_bnode.
    Proof. by move=> x y; rewrite /init_bnode=> [[]] ->. Qed.

    Lemma mark_hash_init b g : Bnode b \in bnodes (init_hash g) -> current_hash b = h0.
    Proof. rewrite /bnodes/init_hash -filter_undup mem_filter /=.
           rewrite undup_terms (terms_relabeled g inj_init_bnode).
           by move=> /map_inv [[] // ?]=> [[]] ->. 
    Qed.

    (* Lemma app_n_Sn (A : Type) (f: A -> A) x n: app_n f x n.+1 = f (app_n f x n). *)
    (* Proof. rewrite /=. elim n=> [//| n' IHn]. *)
    (*        rewrite /=.  /app_n. *)
    (*        rewrite -IHn. *)


    Lemma app_n_mark_bnode g b n:
      Bnode b \in bnodes (init_hash g) ->
                  app_n mark_bnode (Bnode b) n = Bnode (app_n mark_hash (mkHinput (input b) h0) n).
    Proof. move=> /mark_hash_init b_hash. elim n=> [| n' IHn]; last by rewrite /= IHn.
           by rewrite /=; f_equal; case: b b_hash=> /= [[]] ? ? /= ->.
    Qed.

    Lemma mark_hash_idem_inj b1 b2:
      mark_hash (mark_hash b1) = mark_hash (mark_hash b2) ->
      mark_hash b1 = mark_hash b2.
    Proof. case b1; case b2=> [[a b] [a' b']] /=.
           by rewrite /mark_hash /==> /eqP; rewrite eq_i_ch /==> /andP [/eqP -> /eqP/inj_hashTuple [->]].
    Qed.

    Lemma appn_mark_hash (b1 b2: hash B) n:
      mark_hash (app_n mark_hash (mkHinput (input b1) h0) n) = mark_hash (app_n mark_hash (mkHinput (input b2) h0) n) ->
      ((input b1) == (input b2)) && (app_n mark_hash (mkHinput (input b1) h0) n == app_n mark_hash (mkHinput (input b2) h0) n).
    Proof. elim: n=> [/=| n' IHn].
           case b1; case b2=> [[a b] [a' b']] /==> /eqP.
           by rewrite eq_i_ch /= => /andP [/eqP -> _]; rewrite !eqxx.
           by move=> /= /mark_hash_idem_inj /IHn => /andP [-> /eqP ->]; rewrite eqxx.
    Qed.

    Lemma inj_mark_bnode g: {in (bnodes g), injective mark_bnode}.
    Proof. move=> x in_bns y.
           case: x in_bns; case y=> x' y'; rewrite ?i_in_bnodes ?l_in_bnodes // => in_bns /=
               => [[]] i_eq /eqP; rewrite ?hashTuple_neq_error //.
           move=> /eqP/inj_hashTuple []=> ch_eq.
           by f_equal; apply /eqP; rewrite eq_i_ch i_eq ch_eq !eqxx.
    Qed.

    Lemma eq_appn_init_num b1 b2 g :
      Bnode b1 \in bnodes (init_hash g) ->
                   Bnode b2 \in bnodes (init_hash g) ->
                                forall n m,
                                  (app_n mark_bnode (Bnode b1) n) = (app_n mark_bnode (Bnode b2) m) -> n = m.
      move=> b1in_bns b2in_bns.
      have b1_hash:  current_hash b1 = h0. by apply: mark_hash_init b1in_bns.
      have b2_hash:  current_hash b2 = h0. by apply: mark_hash_init b2in_bns.
      move=> n m. rewrite (app_n_mark_bnode n b1in_bns) (app_n_mark_bnode m b2in_bns).
      move=> [appn_eq].
      elim: n m appn_eq=> [// m | n' IHn m].
      + by case: m=> [//| n' []] => _ /eqP; rewrite eq_sym hashTuple_neq_init.
      + case: m IHn=> [//| m'] IHn []; first by move=> _ /eqP /=; rewrite hashTuple_neq_init.
      - move=> eq_i /inj_hashTuple [] eq_ch.
        have eq_appn: app_n mark_hash (mkHinput (input b1) h0) n' = app_n mark_hash (mkHinput (input b2) h0) m'.
        by apply /eqP; rewrite eq_i_ch eq_i eq_ch !eqxx.
        by rewrite eq_appn in IHn; rewrite (IHn m').
    Qed.

    (* Lemma inj_mark_bnode' b1 b2: is_bnode b1 -> is_bnode b2 -> *)
    (*  mark_bnode b1 = mark_bnode b2 -> b1 = b2.  *)
    (* Proof. move=> x y. *)
    (*        case: x; case y=> x' y'. rewrite ?i_in_bnodes ?l_in_bnodes // => in_bns /= *)
    (*            => mbns_eq; injection mbns_eq=> /eqP; rewrite ?hashTuple_neq_error //. *)
    (*        move=> /eqP/inj_hashTuple eq_seq; injection eq_seq=> ch_eq i_eq. *)
    (*        by f_equal; apply /eqP; rewrite eq_i_ch i_eq ch_eq !eqxx. *)
    (* Qed. *)

    Lemma appn_mark_hash_eq_input (b1 b2: hash B) n:
      (app_n mark_hash (mkHinput (input b1) h0) n) = app_n mark_hash (mkHinput (input b2) h0) n ->
      input b1 = input b2.
    Proof.
      case: n=> [/=| n']; first by move=> [] ->.
      by rewrite /==> /appn_mark_hash /andP [/eqP -> _].
    Qed.

    Lemma app_n_mark_eq_bns (b1 b2: hash B) g :
      Bnode b1 \in bnodes (init_hash g) ->
                   Bnode b2 \in bnodes (init_hash g) ->
                                forall n,
                                  (app_n mark_bnode (Bnode b1) n) = (app_n mark_bnode (Bnode b2) n) -> (@Bnode I (hash B) L b1) = (Bnode b2).
      move=> b1in_bns b2in_bns n.
      rewrite (app_n_mark_bnode n b1in_bns) (app_n_mark_bnode n b2in_bns)=> [[]] /appn_mark_hash_eq_input eq_i.
      by f_equal; apply /eqP; rewrite eq_i_ch eq_i (mark_hash_init b1in_bns) (mark_hash_init b2in_bns) !eqxx.
    Qed.

    Lemma k_mapping_seq_uniq_graph g: uniq (mapi (app_n mark_bnode) (bnodes (init_hash g))).
    Proof.
      rewrite /mapi; pose g' := init_hash g.
      rewrite map_inj_in_uniq; first by apply (zip_uniq_l _ (uniq_bnodes g')).
      move=> [t n] [u m] /in_zip/andP [tin_bns n_iota] /in_zip/andP [uin_bns m_iota] /= eq_app_n.
      case: t tin_bns uin_bns eq_app_n; case: u => nt nu; rewrite ?i_in_bnodes ?l_in_bnodes // => nu_bns nt_bns.
      move=> injH.
      have eqnm: n = m. apply (eq_appn_init_num nu_bns nt_bns injH).
      f_equal; last by apply eqnm.
      + rewrite eqnm in injH. apply (app_n_mark_eq_bns nu_bns nt_bns injH).
    Qed.

    Lemma k_mapping_seq_uniq_seq s (s_uniq: uniq s): uniq (mapi (app_n mark_bnode) s).
    Proof.
      rewrite /mapi map_inj_in_uniq.
      apply: zip_uniq_l s_uniq.
      move=> [t n] [u m] x_in_zip y_in_zip /= eq_app_n.
      admit.
    Admitted.
    (* Lemma k_mapping_seq_uniq' g: uniq (mapi (app_n mark_bnode) {set (seq_sub (bnodes (init_hash g)))}). *)
    (* Proof. *)
    (*   rewrite /mapi. *)
    (*   have injF : injective (fun an=> app_n mark_bnode an.1 an.2). admit. *)
    (*   rewrite map_inj_uniq. *)
    (*   have uniq_iota : uniq (iota 0 (size (bnodes (init_hash g)))). by apply iota_uniq. *)
    (*   apply zip_uniq. apply uniq_bnodes. apply uniq_iota. *)
    (*   apply injF. *)
    (* Admitted. *)

    Definition k_mapping (g : rdf_graph I B L) : rdf_graph I B L :=
      let all_maps :=
        map (mapi (app_n mark_bnode)) (permutations (bnodes (init_hash g))) in
      let mus := map build_mapping_from_seq all_maps in
      let isocans := map (fun mu => relabeling mu g) mus in
      foldl Order.min (relabeling id g) isocans.


    (* let isoG := choose_graph isocans in *)
    (* let isoMu := nth id mus (find (eqb_rdf isoG) isocans) in *)
    (* isoMu. *)

    (* need the proof that is a blank node!
       build_mapping (k_distinguish (mkRdfGraph bns)). *)

    Definition isoCanonicalTemplate g (color color_refine: hgraph -> hgraph) p_refining : rdf_graph I B L:=
      let g' := color (init_hash g) in
      let P := mkPartition g' in
      let g_iso := if is_fine P then g' else p_refining g' color_refine in
      label g_iso.

    (* first approach *)
    Definition justDistinguish g :=
      isoCanonicalTemplate g id id distinguish.

    Definition isoCanonicalNoIter g :=
      isoCanonicalTemplate g update_bnodes update_bnodes distinguish.

    Definition isoCanonicalIter g :=
      isoCanonicalTemplate g hashNodes_initialized hashNodes_initialized distinguish.

    Definition isoCanonicalise g :=
      isoCanonicalTemplate g hashBnodesPerSplit hashNodes_initialized distinguish.

    Lemma size_0_nil (T : Type) (s : seq T) : size s = 0 -> s = [::].
    Proof. by case s. Qed.


    (* Lemma singleton_g_is_coarse (g : hgraph) : size (bnodes g) = 1%N -> is_coarse (mkPartition g). *)
    (* Proof. rewrite /mkPartition/bnodes. case g => g'. case g' => [// | [s p o sib pi] tl] => /= singleton.  *)
    (*        rewrite /terms/terms_triple. case trpl=> s p o sib pi. case s. *)


    Lemma seq1_empty_seq (A : Type) (hd:A) d s : hd :: s = [:: d] -> s = [::].
    Proof. by case s. Qed.

    Lemma no_bnodes_same_partition t ts : bnodes_triple t = [::] -> is_fine (mkPartition {| graph := ts |}) -> is_fine (mkPartition {| graph := t :: ts |}).
    Proof. by rewrite /mkPartition bnodes_cons /bnodes => -> /=; rewrite undup_idem. Qed.

    Lemma eq_hash_refl_singl b g : bnodes g = [:: b] -> (if eq_hash b b then ([:: b], [::]) else ([::], [:: b])).1 = [:: b].
    Proof. by move=> H; apply b_in_bnode_is_bnode in H; rewrite (eq_hash_refl H). Qed.

    Lemma sing_fine (g : hgraph) (b : hterm): bnodes g = [:: b] -> is_fine (mkPartition g).
    Proof.
      case: g b=> g'; elim: g'=> [//| t ts IHts].
      rewrite bnodes_cons. 
      case t=> s p o; case s; case p; case o=> //;
                                                 rewrite /bnodes_triple/terms_triple => id id0 id1 sib pii b;
                                                                                        rewrite filter_undup ?undup_idem /mkPartition => /= singl;
                                                                                                                                         try (move: singl; rewrite /undup_idem bnodes_cons /bnodes_triple /terms_triple filter_undup /= undup_bnodes).
      + apply no_bnodes_same_partition. by rewrite /bnodes_triple filter_undup. apply (IHts b singl).
      + apply no_bnodes_same_partition. by rewrite /bnodes_triple filter_undup. apply (IHts b singl).
      (* =============== *)
      + case e: (Bnode id \in bnodes {| graph := ts |})=> singl.
      - by apply (IHts b singl).
      - by case: singl=> _ -> /=; rewrite eq_hash_refl. 
        (* =============== *)
        + case: (Bnode id1 \in bnodes {| graph := ts |})=> singl.
      - by apply (IHts b singl).
      - by case: singl=> _ -> /=; rewrite eq_hash_refl. 
        (* =============== *)
        + case: (Bnode id1 \in bnodes {| graph := ts |})=> singl.
      - by apply (IHts b singl).
      - by case: singl=> _ -> /=; rewrite eq_hash_refl. 
        (* =============== *)
        + move: singl.
          have b_def : (bnodes_triple
                          {|
                            subject := Bnode id1;
                            predicate := Iri id0;
                            object := Bnode id;
                            subject_in_IB := sib ;
                            predicate_in_I := pii
                          |}) = (if Bnode id1 \in [:: Bnode id] then [:: Bnode id] else [:: Bnode id1; Bnode id]). move=> ? ?. by rewrite /bnodes_triple /terms_triple filter_undup /=.
          rewrite bnodes_cons /bnodes_triple filter_undup -b_def -bnodes_cons => singl.
          rewrite /= -b_def -bnodes_cons singl.
          have isbb: is_bnode b. by apply (b_in_bnode_is_bnode singl).
          by rewrite /= (eq_hash_refl isbb); case: b isbb singl.
    Qed.

    Lemma distinguish_preserves_isomorphism g : iso (justDistinguish g) g.
    Proof. 
      rewrite /iso/justDistinguish/isoCanonicalTemplate/is_iso.
      case (is_fine (mkPartition (init_hash g))).
      case g=> g'. elim g'=> [|t ts ihts].
      - exists id. split.
        + by exists id.
                    + by rewrite relabeling_id. 
                    - 
                      (* need to build μ. and μ bij. *)
    Admitted.

    Lemma empty_ak_mapping : ak_mapping (mkRdfGraph [::]) = [::]. Proof. by []. Qed.

    Lemma inv_of_ak_mapping g : exists mu, eqb_rdf (relabeling mu g) (relabeling (build_mapping_from_seq (ak_mapping g)) g).
    Proof. by exists (build_mapping_from_seq (ak_mapping g)); apply eqb_rdf_refl. Qed.


    Lemma inv_of_perm_ak_mapping g p :
      p \in (permutations (ak_mapping g)) ->
            exists mu, eqb_rdf (relabeling mu g) (relabeling (build_mapping_from_seq p) g).
    Proof.
      move=> hp.
      exists (build_mapping_from_seq p).
      exact: eqb_rdf_refl.
    Qed.

    Lemma min_seq (disp : unit) (T: porderType disp) (s: seq T) (hd:T) : exists minimum, forall t, t \in (hd::s) -> minimum <= t.
    Proof. elim: (hd::s) => [| a t [minimum IHts]];
                            first by exists hd=> t; rewrite in_nil.
                                            case e: (minimum <= a); [exists minimum | exists a]=> a0; rewrite in_cons; case/orP.
                                            - move=> /eqP ->. exact: e.
                                            - move=> ain. apply: IHts ain.
                                            - move=> /eqP ->; apply Order.POrderTheory.lexx.
                                            - have legt : ((minimum <= a) == false = ((minimum > a) == true)).
                                              admit.
                                              move=> ain. eapply (Order.POrderTheory.le_trans).
                                              (* by rewriting legt on the evidence of the case *)
                                              admit.
                                              apply: IHts ain.
    Admitted.


    Lemma the_μ g :
      exists f,
        [seq relabeling mu0 g
        | mu0 <- [seq build_mapping_from_seq i
                 | i <- permutations (ak_mapping g)]] =

          map f [seq build_mapping_from_seq i
                | i <- permutations (ak_mapping g)].
    Proof. rewrite /= /ak_mapping. elim g=> gs; elim: gs=> [| a t IHts].
           - by exists (fun g=> relabeling g (mkRdfGraph [::])).
                       - admit.
    Admitted.

    Lemma init_hash_nil : init_hash {| graph := [::] |} = {| graph := [::] |}. by []. Qed.

    Lemma relabeling_mu_inv (g : rdf_graph I B L) (fs : seq (B -> B)) (mapping : rdf_graph I B L -> rdf_graph I B L) :
      (mapping g) \in (map (fun mu => relabeling mu g) fs) ->
                      exists (mu : B -> B), relabeling mu g == mapping g.
    Proof.
      elim : fs => [| f fs' IHfs]; first by rewrite in_nil.
      rewrite in_cons; case/orP.
      + by rewrite eq_sym; exists f.
      + by move=> H; apply IHfs in H; apply H.
    Qed.


    (* Lemma k_mapping  *)
    Lemma k_mapping_cons_const x y z sib pii as' :
      is_ground_term x -> is_ground_term y -> is_ground_term z ->
      (k_mapping {| graph :=
                     {|
                       subject := x;
                       predicate := y;
                       object := z;
                       subject_in_IB := sib;
                       predicate_in_I := pii
                     |} :: as'
                 |})
      =
        mkRdfGraph 
          ({|
              subject := x;
              predicate :=  y;
              object := z;
              subject_in_IB := sib;
              predicate_in_I := pii
            |} :: (k_mapping {| graph:= as' |})).
    Proof. rewrite /k_mapping /init_hash relabeling_cons relabeling_id relabeling_triple_id. Admitted.

    Lemma injection_hterm b (ht : hterm) : eqb_b_hterm b ht -> is_bnode ht. Proof. by case ht. Qed.
    Lemma eqb_b_hterm_trans b b' ht : eqb_b_hterm b ht -> eqb_b_hterm b' ht -> b = b'.
    Proof. by case: ht=> // name; move=> /eqP -> /eqP ->. Qed.

    Lemma injection_kmap b b' ht s : eqb_b_hterm b ht -> eqb_b_hterm b' ht ->
                                     (build_mapping_from_seq (mapi (app_n mark_bnode) s) b) = (build_mapping_from_seq (mapi (app_n mark_bnode) s) b').
    Proof. move=> eb eb'. suffices : b = b'. by move=> ->.
           by apply (eqb_b_hterm_trans eb eb'). Qed.

    Lemma has_not_default T (s : seq T) p : has p s -> forall x0 x1,  nth x0 s (find p s) = nth x1 s (find p s).
    Proof. elim: s=> [//| hd tl IHtl] hps x1.
           rewrite /= in hps. case/orP: hps=> [| hptl]; first by move=> /= ->.
           + rewrite /=. case: (p hd); first by [].
             by apply (IHtl hptl).
    Qed.

    (* Lemma nth_uniq (T: eqType) (s : seq T) x0 : uniq s -> forall n, nth x0 s n \in s -> forall m, nth x0 s n = nth x0 s m <-> n = m. *)
    (* Proof. elim: s => [//| hd tl IHtl]. split; last by move=> ->. *)
    (*        + case: n H0 => [//| n']. *)
    (*          rewrite /=. *)
    (*          case: m=> [//| m']. *)
    (*          rewrite /= in H *. *)
    

    (* Lemma find_eq (T: eqType) (s : seq T) x y x0 : (x \in s) -> *)
    (*                                                uniq s -> *)
    (*                                                (nth x0 s (index x s)) = nth x0 s (index y s) -> x = y. *)
    (* Proof. *)
    (*   have: uniq (undup s). by apply undup_uniq. *)
    (*   elim: (undup s)=> [//| a l IHl] uniq_s x_in_s. *)
    (*   (* rewrite has_pred1 in has_x. *) *)
    (*   (* + rewrite /=. *) *)



    (*   rewrite (nth_index _ x_in_s)=> eq. *)
    (*   rewrite eq /= in IHl x_in_s. *)
    (*   case: (a ==y) IHl x_in_s=> /=. *)
    (*   move=> uniq_l contr. rewrite /= in uniq_s. move: uniq_s=> /andP [a_nil_l _]. *)
    (*   rewrite in_cons in contr. case/orP: contr. *)



    (*   subst. rewrite /= in uniq_s *. rewrite in_cons in x_in_s. case/orP: x_in_s=> [| has_l]. rewrite eq_sym=> ->. *)
    (*     rewrite /=. *)

    Lemma eq_to_fin (T: eqType) (ft ft' : finType) (f : T -> T) (injF: injective f) (funt : ft -> T) (injFt: injective funt) (funt' : T -> ft') (injFt' : injective funt')
      (eq_card : #|ft| = #|ft'|) : exists (f'' : ft -> ft'), injective f''.
    Proof. exists (fun argT => (funt' (f (funt argT)))).
           by apply: (inj_comp injFt') (inj_comp injF injFt). Qed.

    Lemma all_kmaps_bijective g : List.Forall (fun mu => bijective mu) [seq build_mapping_from_seq i
                                                                       | i <- [seq mapi (app_n mark_bnode) i
                                                                              | i <- permutations (bnodes (init_hash g))]].
    Proof.
      have map2Listmap U V (f : U -> V) (s : seq U) : map f s = List.map f s. admit.
      have nth2Listnth U (d : U) (s : seq U) n : nth d s n = List.nth n s d. admit.
      have size2Listlength U (s : seq U) : List.length s = size s. admit.
      rewrite !map2Listmap !List.Forall_map.
      suffices step s : perm_eq s (bnodes (init_hash g)) -> bijective (build_mapping_from_seq (mapi (app_n mark_bnode) s)).
      apply/List.Forall_nth=> i d lti. apply: step. rewrite -mem_permutations -nth2Listnth. apply: mem_nth.
      by rewrite -size2Listlength; apply/ltP.
      have inj_lookup: injective lookup_hash_default. admit.
      pose the_list := (mapi (app_n mark_bnode) (undup s)).
      have inj_mu: injective (build_mapping_from_seq (mapi (app_n mark_bnode) (undup s))).
      move=> x y. rewrite -/the_list /build_mapping_from_seq. case e: (has (eqb_b_hterm x) (mapi (app_n mark_bnode) (undup s))); case e2:  (has (eqb_b_hterm y) (mapi (app_n mark_bnode) (undup s))); last done.
      move=> /inj_to_string /inj_lookup/eqP eq_hash.
      have ansx : ((eqb_b_hterm x) (nth (Bnode (mkHinput x herror)) (mapi (app_n mark_bnode) (undup s))
                                      (find (eqb_b_hterm x) (mapi (app_n mark_bnode) (undup s))))).
      apply nth_find; apply e.
      have ansy : ((eqb_b_hterm y) (nth (Bnode (mkHinput x herror)) (mapi (app_n mark_bnode) (undup s))
                                      (find (eqb_b_hterm y) (mapi (app_n mark_bnode) (undup s))))).
      apply nth_find; apply e2.
      rewrite -/the_list in
        e e2
          eq_hash ansx ansy.
      rewrite (has_not_default e (Bnode (mkHinput x herror)) (Bnode (mkHinput y herror))) nth_uniq in eq_hash.
      move: eq_hash=> /eqP eq_hash. 
      rewrite eq_hash in ansx.
      apply: eqb_b_hterm_trans ansx ansy.
      rewrite -has_find. apply e.
      rewrite -has_find. apply e2.
      rewrite /the_list.
      apply k_mapping_seq_uniq_seq. apply undup_uniq.
      admit.
      admit.
      admit.
      (* modify bijective on (bnodes g) -> (mapi (app_n mark_bnode) (bnodes g))*)
    Admitted.

    (* TODO *)
    Lemma inv_of_k_mapping g : exists mu, (relabeling mu g) == (k_mapping g) /\ bijective mu.
    Proof.
      have step1 : k_mapping g = g \/
                     (k_mapping g) \in [seq relabeling mu0 g
                                       | mu0 <- [seq build_mapping_from_seq i
                                                | i <- [seq mapi (app_n mark_bnode) i
                                                       | i <- permutations
                                                                (bnodes (init_hash g))]]].
      by rewrite /k_mapping relabeling_id; apply: foldl_op.
      case: step1=> [ -> | in_tail ].
      + exists id; split.
      - by rewrite relabeling_id.
      - exact: id_bij. 
        + have [mu eq_mu_map] : exists mu : B -> B, relabeling mu g == k_mapping g.
          exact: relabeling_mu_inv in_tail.
          exists mu. split; first exact eq_mu_map.
          (* needs mu to have eqType, could be a finfun *)
          have fin_mu : (seq_sub (bnodes g)) -> B.
          Fail move: (finfun (fun b => b)).
          admit.
          (* Fail fin_mu \in in_tail. *)
    Admitted.

    (* TODO *)
    (* USES inv_of_k_mapping *)
    Lemma k_mapping_iso_output g : iso (k_mapping g) g.
    Proof. case (inv_of_k_mapping g)=> μ [rel_eq_kmap bijmu].
           exists μ. split. exact: bijmu. by rewrite eq_sym.
    Qed.

    (* TODO *)
    Lemma k_mapping_dont_manipulate_names : (dont_manipulate_names_mapping k_mapping).
    Proof.
      rewrite /dont_manipulate_names_mapping=> g μ bijmu.
      - have step1 : k_mapping g = g \/
                       (k_mapping g) \in [seq relabeling mu0 g
                                         | mu0 <- [seq build_mapping_from_seq i
                                                  | i <- [seq mapi (app_n mark_bnode) i
                                                         | i <- permutations
                                                                  (bnodes (init_hash g))]]].
        by rewrite /k_mapping relabeling_id; apply: foldl_op.
        (* case: step1=> [ -> | in_tail ]. *)
        (* elim g=> g'; elim: g'=> [//| a tl IHa]. *)
        rewrite /k_mapping.
    Admitted.


    (* TODO *)
    (* USES inv_of_k_mapping *)
    Lemma k_mapping_isocan : isocanonical_mapping k_mapping.
    Proof. split; first by apply k_mapping_iso_output.
           split.
           + have isog1k1 : iso g1 (k_mapping g1). by rewrite iso_symm; apply k_mapping_iso_output.
             have isog2k2 : iso (k_mapping g2) g2. by apply k_mapping_iso_output.
             move=> /eqP k1_eq_k2. rewrite k1_eq_k2 in isog1k1. apply (iso_trans isog1k1 isog2k2).
           + have dmnm : (dont_manipulate_names_mapping k_mapping). apply k_mapping_dont_manipulate_names.
             by apply iso_leads_canonical.
    Admitted.

    (* Lemma relabeling_mu_inv_bij (g : rdf_graph I B L) (fs : seq (B -> B)) : *)
    (*   List.Forall (fun mu => bijective mu) fs -> *)
    (*         exists (mu : B->B), relabeling mu g == k_mapping g /\ bijective mu. *)
    (* Proof. move => all_bij.  *)
    (*        have H: exists mu, (relabeling mu g) == (k_mapping g). apply inv_of_k_mapping. *)
    (*        case: H=> mu /eqP eqmu. *)
    (*        exists mu. rewrite eqmu. split; first by []. *)
    (* Qed. *)

    (* Lemma k_mapping_iso g : iso (k_mapping g) g. *)
    (* Proof. rewrite /iso/is_iso. *)
    (*        have H: exists mu, (relabeling mu g) == (k_mapping g). apply inv_of_k_mapping. *)
    (*        case: H=> mu /eqP eqmu. *)
    (*        exists mu. rewrite eqmu. split; last by []. *)
    (*        admit. *)
    (* Admitted. *)

    (* Hypothesis perfectHashingSchemeTriple : injective hashTriple. *)

  End IsoCanAlgorithm.

  Section Example.
    (* From Coq Require Import Strings.String. *)
    Require Import Strings.Ascii.
    Variables (b : seq ascii) (p : nat).
    Definition B_ := (@Bnode nat (seq ascii) nat b).
    Definition P := (@Iri nat (seq ascii) nat p).
    Lemma inib : is_in_ib B_.
    Proof. by []. Qed.

    Lemma ini : is_in_i P. Proof. by []. Qed.
    (* Check nat : countType. *)

    Definition t := mkTriple B_ inib ini.
    Definition g := mkRdfGraph [:: t].
    Variable h:countType.
    Variable h0 h1 h2 h3 h4: h.
    Check g.
    (* Open *)
    Open Scope char_scope.
    Check ascii.
    Definition berror := [:: "e"; "r"; "r"; "o"; "r"] : seq ascii.
    About Countable.pack.
    About Countable.mixin_of.
    Variable ascii_countMixin : Countable.mixin_of ascii.
    Fail Canonical ascii_countType := Eval hnf in CountType ascii ascii_countMixin.
    (* CountType ascii ascii_countMixin. *)

    Fail Compute isoCanonicalise h0 h1 h2 h3 h4 berror g .


  End Example.


End IsoCan.
