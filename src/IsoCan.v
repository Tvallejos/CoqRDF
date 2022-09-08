From mathcomp Require Import all_ssreflect fingraph.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
From RDF Require Export Rdf Triple Term.

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

    (* misnommer ? *)
    Definition get_triple trm (trpl : htriple) : option hterm :=
      let (s,p,o,_,_) := trpl in
      if eqb_trm_hi trm s then Some s
      else if eqb_trm_hi trm p then Some p
           else if eqb_trm_hi trm o then Some o
                else None.

    Definition is_some {T : Type} (ot : option T) : bool :=
      match ot with Some _ => true | None => false end.

    Definition hgraph := rdf_graph I (hash B) L.

    Definition get t (g : hgraph) : option hterm :=
      let otrs := (map (get_triple t) (graph g)) in
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

    Definition label_bnode (hb : (hash B)) : B :=
      to_string (current_hash hb).

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
    Definition mark_bnode (b : hash B) : hash B :=
      mkHinput (input b) (hashTuple [:: (current_hash b) ; hmark]).

    Definition mark_bnode' (b : hterm) : hterm :=
      match b with
      | Iri i| Lit i => Bnode (mkHinput b0 herror)
      | Bnode hb=> Bnode (mark_bnode hb)
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
      let b' := mark_bnode b in
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

    Definition build_mapping_from_seq (trms : seq hterm) : B -> B :=
      fun b =>
        if has (eqb_b_hterm b) trms then
          let the_bnode := nth (Bnode (mkHinput b herror)) trms (find (eqb_b_hterm b) trms) in
          to_string (lookup_hash_default the_bnode)
        else
          b.

    Fixpoint app_n (f : hterm -> hterm) (x : hterm) (n:nat) :=
      match n with
      | O => x
      | S n' => app_n f (f x) n'
      end.

    Definition k_distinguish bns : seq (term I (hash B) L) :=
      let fix help bns n :=
        match bns with
        | nil => nil
        | trm :: trms => app_n mark_bnode' trm n :: help trms (S n)
        end in
      help bns 0.

    Definition mapi {A B : Type} (f : A -> nat ->  B) (s : seq A) : seq B :=
      map (fun an => (f an.1) an.2) (zip s (iota 0 (size s))).

    Definition ak_mapping (g : rdf_graph I B L) : seq hterm :=
      let bns := bnodes (init_hash g) in
      mapi (app_n mark_bnode') bns.

    Definition k_mapping (g : rdf_graph I B L) : rdf_graph I B L :=
      let all_maps := permutations (ak_mapping g) in
        (* map (mapi (app_n mark_bnode')) (permutations (bnodes (init_hash g))) in *)
                        (* (ak_mapping g) in *)
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

    Lemma singleton_g_is_fine (g: hgraph) : size (bnodes g) = 1%N -> is_fine (mkPartition g).
    Proof. rewrite /mkPartition/is_fine. case g=> /= g'. 
           elim g'=> [//| hd t ih] /= => singleton.
           (* injection singleton as tsize. *)
           (* apply size_0_nil in tsize. rewrite tsize /=. *)
           case hd=> s p o ? ? /=. rewrite /bnodes/terms/terms_triple /=.
           (* case (s \in [:: p;o]) => /=.  *)
           (* case s. case p. case o=> /=. *)
    Abort.

    (* Lemma  *)
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
    
    Lemma empty_permutations (T:eqType) : @permutations T [::] = [:: [::]]. Proof. by []. Qed. 
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

    Lemma inweak (T: eqType) (l:seq T) t u : t \in l -> t \in (u::l).
    Proof. rewrite -!has_pred1 /has. case (pred1 t u); first done.
           by move=> ->.
    Qed.

    Lemma min_seq (disp : unit) (T: porderType disp) (s: seq T) (hd:T) : exists minimum, forall t, t \in (hd::s) -> minimum <= t.
    Proof. elim: (hd::s) => [| a t [minimum IHts]];
                          first by exists hd=> t; rewrite in_nil.
                                     (* why does not apply done in the last of the second case? *)
                                     case: (minimum <= a); [exists minimum | exists a]=> a0; rewrite in_cons; case: orP; last done.
                                     - move=> [/eqP -> | ain] _.
                                     (* minimum is min*)
                                     + admit. (* goal is what I shoud be true in this case *)
                                     + apply: IHts ain.
                                       (* a in min*)
                                       * done. move=> [/eqP -> | ain] _.
                                     - exact: Order.POrderTheory.lexx.
                                     - have legt : ((minimum <= a) == false = ((minimum > a) == true)). admit.  
                                       eapply (Order.POrderTheory.le_trans).
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


    Lemma syntax_f (T U: eqType) (s:seq T) (f: T -> U): forall (u:U), u \in map f s -> exists t, u = (f t).
    Proof. elim : s => [| a t IHts] u /=; first by rewrite in_nil.
           rewrite in_cons. case: orP=> [[/eqP -> | y]|] _; last by done.
           - by exists a.
                  - apply: IHts; apply y.
    Qed.

    Lemma foldl_op (disp: unit) (T: porderType disp) (l: seq T) (x0 : T) : foldl Order.min x0 l = x0 \/ foldl Order.min x0 l \in l.
    Proof. elim: l x0 => [ | t ts IHts] x0 /=.
           + by left.
           + case: (IHts (Order.min x0 t))=> [->|intail] /=.
           - rewrite Order.POrderTheory.minEle; case: ifP=> _.
             * by left.
             * by right; rewrite in_cons eqxx.
           - by right; rewrite in_cons intail orbT.
    Qed.

    Lemma inv_of_k_mapping g : exists mu, eqb_rdf (relabeling mu g) (k_mapping g).
    Proof.
      rewrite /k_mapping relabeling_id.
      have step0 l :
        let res := foldl Order.min g l in
        res = g \/ res \in l.
      apply foldl_op.
      have step1 : k_mapping g = g \/
                     (k_mapping g) \in [seq (relabeling mu0 g)
                                       | mu0 <- [seq build_mapping_from_seq i | i <- permutations (ak_mapping g)]].
      rewrite /k_mapping relabeling_id; apply: step0.
      case: step1=> [e | hin].
      have -> : (foldl Order.min g
                      [seq relabeling mu0 g
                      | mu0 <- [seq build_mapping_from_seq i | i <- permutations (ak_mapping g)]]) = k_mapping g.
      by rewrite /k_mapping relabeling_id.
      - rewrite e; exists id; rewrite relabeling_id; apply eqb_rdf_refl. 
      (* case: g e => [] [|  hd tl] //=.  admit. (* prove it early as a lemma by case on g *) *)
      - (* all elements in the sequence are of the form (relabeling mu0 g) .... Search _ all *)
        move: hin.
        have hinrelabel g' : g' \in [seq relabeling mu0 g
                                    | mu0 <- [seq build_mapping_from_seq i | i <- permutations (ak_mapping g)]] -> exists g1, exists μ, g' = relabeling μ g1.
        (* admit. *)
        (* apply syntax_f. *)
        elim g=> gs; elim: gs=> [| a as' IHas] /=.
      - rewrite relabeling_empty in_cons in_nil.
        case: orP.
        + move=> [].
        + move=> /eqP -> _. exists {| graph := [::] |}. exists (fun t=> b0). exact : relabeling_empty.
        + done.
        + done.
        + rewrite /ak_mapping/init_hash.
          case a=> s p o /= sib pii.
          admit.


        (*   ([seq relabeling mu0 g *)
        (*        | mu0 <- [seq build_mapping_from_seq i | i <- permutations (ak_mapping g)]])=> [|a as' IHas]; first by rewrite in_nil. *)
        (* rewrite in_cons. *)

        elim g => gs; elim: gs=> [| t ts IHts ] /=.
        (* if I try to do elim:g I get this Error: Cannot find the elimination combinator rdf_graph_ind, the elimination of the inductive *)
        (* definition rdf_graph on sort Prop is probably not allowed. *)
        (* just elim works fine *)
        + by exists id; rewrite /build_mapping_from_seq /= relabeling_id Order.POrderTheory.minEle Order.POrderTheory.lexx eqb_rdf_refl.
               + move=> hin.
               (*   apply hin in hinrelabel. *)
           
               (* * + move => hin. *) 
               (*   exists id. rewrite /eqb_rdf /=. apply /eqP. *)
               (*   elim  *)
               (*                [seq relabeling mu {| graph := t :: ts |} *)
               (*                | mu <- [seq build_mapping_from_seq i | i <- permutations (ak_mapping {| graph := t :: ts |})]]=> gfold; elim: gfold=> [| a as' IHas]. *)
                 admit.

    Admitted.


           (* Definition oget_bnode (t : term I B L) : option B := *)
           (*   if t is Bnode b then Some b else None. *)
           (* Lemma foo_term : forall f trm, *)
           (*     ((is_iri trm \/ is_lit trm) -> f trm = trm) -> exists mu, oget_bnode (f trm) = omap mu (oget_bnode trm). *)
           (* Proof. rewrite /oget_bnode => f trm. case trm=> /= [ i | l | name] idf. *)
           (*        + exists id. rewrite idf. by []. left. by []. *)
           (*        + exists id. rewrite idf. by []. right. by []. *)


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


