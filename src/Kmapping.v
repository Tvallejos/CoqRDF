From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
From RDF Require Export Rdf Triple Term Util IsoCan.

(******************************************************************************)
(*                                                                            *)
(*            κ-mapping algorithm rewritten in a functional style             *)
(*                                                                            *)
(******************************************************************************)
Section Kmapping.
  Variable disp : unit.
  Variable I B L : orderType disp.
  Hypothesis nat_inj : nat -> B.
  Hypothesis nat_inj_ : injective nat_inj.

  Notation hn := (hash nat B).
  Notation hterm := (term I hn L).
  Definition HBnode p := @Bnode I hn L (mkHinput p.1 p.2).

  Notation le_triple := (@le_triple disp I B L).
  Notation join_st := (@join_st disp I B L).
  Notation le_triple_total := (@le_triple_total _ I B L).
  Notation le_triple_anti := (@le_triple_anti _ I B L).
  Notation le_triple_trans := (@le_triple_trans _ I B L).

  Definition n0 := 0%N.

  Definition init_bnode_nat (b : B) : (hash nat B) := mkHinput b n0.

  Lemma init_bnode_nat_inj : injective init_bnode_nat.
  Proof. by move=> x y []. Qed.

  Definition build_kmapping_from_seq (trms : seq hterm) : B -> B :=
    fun b =>
      if has (eqb_b_hterm b) trms then
        let the_bnode := nth (HBnode (b,n0)) trms (find (eqb_b_hterm b) trms) in
        nat_inj (lookup_hash_default_ n0 the_bnode)
      else
        b.

  Definition hash_perm p := [seq HBnode an | an <- zip p (iota 0 (size p))].
  Definition kth_map := build_kmapping_from_seq \o hash_perm.

  (* Abstraction for graph canonical candidates *)
  Definition candidates (ts : seq (triple I B L)) :=
    map (((relabeling_seq_triple (B2:=B))^~ ts) \o kth_map) (permutations (get_bts ts)).

  (* Abstraction for sorted graph canonical candidates *)
  Definition s_can (ts : seq (triple I B L)) :=
    map (sort le_triple) (candidates ts).

  (* Definition k_mapping_ts (ts : seq (triple I B L)) : seq (triple I B L) := *)
  (*   foldl Order.max [::] (s_can ts). *)

  Definition k_mapping_ts (ts : seq (triple I B L)) : seq (triple I B L) :=
    foldl join_st [::] (s_can ts).

(******************************************************************************)
(*                  κ-mapping returns a well formed graph                     *)
(******************************************************************************)

  (* For every hashed permutation u,
     if a blank node b is in the blank nodes of ts,
     then u has a blank node whose initial value was b *)
  Lemma get_bts_in_l_perm (ts : seq (triple I B L)) (u : seq hterm)
    (mem : u \in map hash_perm (permutations (get_bts ts))):
    forall b, b \in get_bts ts -> has (eqb_b_hterm b) u.
  Proof.
  move=> b bin; move/mapP : mem=> [/= bs].
  rewrite mem_permutations=> /perm_mem peq ->; rewrite has_map /=.
  apply/hasP=> /=.
  have eqsize : size bs = size (iota 0 (size bs)) by rewrite size_iota.
  rewrite -peq in bin.
  have [/= st [stin [<- [t2 t2eq]]]]:= in_zip_l eqsize bin.
  by exists st.
  Qed.

  (* For every duplicate-free sequence of triples ts,
     a hashed permutation u,
     a blank node b which is in the blank nodes of ts,
     it exists a natural number n such that
        the element at index (find (eqb_b_hterm b) u) in u is an HBnode (b, n) *)
  Lemma nth_bperms (ts : seq (triple I B L)) (uniq_ts : uniq ts)
    (b : B) db dn (bin : b \in get_bts ts) (u : seq hterm):
    u \in  (map hash_perm (permutations (get_bts ts))) ->
      exists n : nat, nth (HBnode (db ,dn)) u (find (eqb_b_hterm b) u) = HBnode (b, n).
  Proof.
  move/mapP=> [/= bns].
  rewrite mem_permutations=> peq_bs ->.
  have permbs := perm_mem peq_bs.
  have uniqbs := perm_uniq peq_bs.
  suffices H1 :
    (find (eqb_b_hterm b) [seq Bnode (mkHinput an.1 an.2) | an <- zip bns (iota 0 (size bns))]) =
      (index b bns).
    suffices H2 : forall [S0 T0 : eqType] (x : S0) (y : T0) [s : seq S0] [t : seq T0] (i : nat),
        size s = size t -> nth (Bnode (mkHinput x y)) [seq Bnode (mkHinput an.1 an.2) | an <- zip s t ] i = Bnode (mkHinput (nth x s i) (nth y t i)).
      exists (index b bns).
      rewrite H2; last by rewrite size_iota.
      congr Bnode.
      rewrite H1 //; apply/eqP; rewrite eq_i_ch /=; apply /andP; split; apply/eqP.
      + by rewrite nth_index // permbs.
      + by rewrite nth_iota // index_mem permbs //.
    by apply hash_nth_mapzip.
  by move=> ? ?; apply: find_index_eqbb; rewrite size_iota.
  Qed.

  (* For every sequence of triples: ts and a hashed permutation of ts: u,
     for two hterms ht1 and ht2 which are members of u then
     if lookup_default_ n0 ht1 = lookup_default_ n0 ht2 it implies
     ht1 = ht2. *)
  Lemma in_perm_luh_inj (ts : seq (triple I B L)) (u : seq hterm) :
    u \in map hash_perm (permutations (get_bts ts)) ->
          {in u&, injective (lookup_hash_default_ n0)}.
  Proof.
  move/mapP=> [/= p pin ->] /= ht1 ht2.
  move/mapP=> [/= tgd_instx tgdinsxin ->] /mapP[/= tgd_insty tgdinsyin ->] /= eq2.
  congr Bnode.
  suffices minnrefl s : minn (size s) (size s) = size s.
    have eqsize : size p = size (iota 0 (size p)) by rewrite size_iota.
    move/nthP : tgdinsxin=> /= /(_ tgd_instx)[xn]; rewrite size_zip -eqsize minnrefl=> sizex.
    move: eq2; case : tgd_instx=> /= tagx1 tagx2 eq2.
    rewrite nth_zip // => /eqP; rewrite xpair_eqE=> /andP[/eqP x1nth /eqP x2nth].
    move/nthP : tgdinsyin=> /= /(_ tgd_insty)[yn]; rewrite size_zip -eqsize minnrefl=> sizey.
    move: eq2; case: tgd_insty=> /= tagy1 tagy2 eq2.
    rewrite nth_zip // => /eqP; rewrite xpair_eqE=> /andP[/eqP y1nth /eqP y2nth].
    rewrite -x2nth -y2nth in eq2.
    rewrite -x1nth{x1nth} -x2nth{x2nth} -y1nth{y1nth} -y2nth{y2nth}.
    move: eq2; rewrite (set_nth_default tagx2); last by rewrite -eqsize.
    move=> /eqP; rewrite nth_uniq //; rewrite -?eqsize //; last by apply iota_uniq.
    by move=> /eqP ->; apply/eqP; rewrite eq_i_ch /= eqxx andbC /= (set_nth_default tagx1) //.
  by move=> ?; apply minn_refl.
  Qed.

  (* For every duplicate-free sequence of triples: ts and a hashed permutation of ts: u,
     for two blank nodes b1 and b2 which are members of the blank nodes of ts then
     if (build_kmapping_from_seq u) b1 = (build_kmapping_from_seq u) b2 it implies
     b1 = b2. *)
  Lemma labeled_perm_inj (ts : seq (triple I B L)) (uniq_ts : uniq ts)
    u (mem : u \in (map hash_perm (permutations (get_bts ts)))) :
    {in get_bts ts &, injective (build_kmapping_from_seq u)}.
  Proof.
  move=> x y xin yin; rewrite /build_kmapping_from_seq.
  suffices mem_has: forall b, b \in get_bts ts -> has (eqb_b_hterm b) u.
    rewrite !mem_has // => /nat_inj_.
    set dflt := HBnode (y,n0).
    have ->: (nth (HBnode (x,n0)) u (find (eqb_b_hterm x) u)) = (nth dflt u (find (eqb_b_hterm x) u)) by rewrite (set_nth_default (HBnode (x,n0))) // -has_find mem_has.
    move: (nth_bperms uniq_ts y n0 xin mem) (nth_bperms uniq_ts y n0 yin mem)=> [n eqnnthx] [m eqmnthy].
    rewrite eqnnthx eqmnthy.
    suffices lh_inj: {in u&, injective (lookup_hash_default_ n0)}.
      move=> /lh_inj; rewrite -eqnnthx -eqmnthy.
      move : (mem_has x xin) (mem_has y yin); rewrite !has_find=> nthxin nthyin.
      by rewrite !mem_nth // => /(_ isT isT); rewrite eqnnthx eqmnthy; move=> [->].
    by apply (in_perm_luh_inj mem).
   apply get_bts_in_l_perm. rewrite /hash_perm in mem. apply mem.
  Qed.

  (* For every duplicate-free sequence of triples: ts and a permutation of ts blank nodes: perm,
     if (build_map_k perm) is injective in the domain of blank nodes of ts,
     then (build_map_k perm) is a pre-isomorphism from ts to relabeling ts under (build_map_k perm) *)
  Lemma auto_iso_rel_perm (ts : seq (triple I B L)) (uts : uniq ts)
    (perm : seq B) (inperm : perm \in permutations (get_bts ts))
    (mu_inj : {in get_bts ts&, injective (kth_map perm)}):
      is_pre_iso_ts ts (relabeling_seq_triple (kth_map perm) ts) (kth_map perm).
  Proof.
  rewrite /is_pre_iso_ts/bnode_map_bij !uniq_get_bts.
  apply uniq_perm.
  + by rewrite map_inj_in_uniq // uniq_get_bts.
  + by rewrite uniq_get_bts.
  + suffices rt_inj: {in ts &, injective (relabeling_triple (kth_map perm))}.
    by rewrite -(get_bs_map _ (all_bnodes_ts _)); apply eq_mem_pmap=> b; rewrite bnodes_ts_relabel_mem.
  by apply: inj_get_bts_inj_ts mu_inj.
  Qed.

  (* For every sequence of triples: ts and a permutation of ts blank nodes: perm,
     the zip of perm and the n first natural numbers is
     in the sequence of hashed permutation candidates of ts *)
  Lemma candidate_in_perm (ts : seq (triple I B L)) perm
    (bin : perm \in permutations (get_bts ts)) :
    [seq (HBnode an) | an <- zip perm (iota 0 (size perm))]
      \in map hash_perm (permutations (get_bts ts)).
  Proof. by apply (map_f hash_perm). Qed.

  (* For every duplicate-free sequence of triples: ts,
     for every possible hashed permutation candidate: u,
     (build_k_mapping_from_seq u) is a pre-isomorphism
     from ts to relabeling ts under (build_kmapping_from_seq u) *)
  Lemma all_kmap_preiso (ts : seq (triple I B L)) (uniq_ts : uniq ts):
    forall u, u \in map hash_perm (permutations (get_bts ts)) ->
      is_pre_iso_ts ts
        (relabeling_seq_triple (build_kmapping_from_seq u) ts)
        (build_kmapping_from_seq u).
  Proof.
  move=> /= u /mapP /= [perm pin ->].
  suffices mu_inj : {in get_bts ts&, injective (kth_map perm)}.
    by apply auto_iso_rel_perm.
  by apply (labeled_perm_inj uniq_ts (candidate_in_perm pin)).
  Qed.

  Lemma kth_map_preiso (ts : seq (triple I B L)) (uniq_ts : uniq ts) (p : seq B):
    p \in permutations (get_bts ts) -> is_pre_iso_ts ts (relabeling_seq_triple (kth_map p) ts) (kth_map p).
  Proof. by move=> pin; apply all_kmap_preiso => //; apply candidate_in_perm. Qed.


  (* For any uniq sequence of triples: ts, its image under k_mapping_ts remains uniq *)
  Lemma uniq_k_mapping_ts (ts : seq (triple I B L)) (u1 : uniq ts) : uniq (k_mapping_ts ts).
  Proof.
  rewrite /k_mapping_ts/s_can/candidates map_comp.
  set build_kmap := map kth_map _.
  set relab := [seq relabeling_seq_triple mu ts | mu <- build_kmap].
  case: (foldl_max_st (map (sort le_triple) relab) [::])=> [-> //| /mapP[u mem ->]].
  suffices relab_uniq : all uniq relab.
    by rewrite sort_uniq; apply (allP relab_uniq)=> //.
  rewrite /relab/build_kmap (map_comp  _ hash_perm) -map_comp.
  apply/allP=> /= t /mapP[/= s sin ->]; apply uniq_relabeling_pre_iso=> //.
  by apply all_kmap_preiso; rewrite // -map_comp.
  Qed.

  (* For any RDF graph: g, its image under k_mapping_ts remains well-formed *)
  Lemma uniq_k_mapping (g : rdf_graph I B L) : uniq (k_mapping_ts g).
  Proof. by apply : uniq_k_mapping_ts (ugraph _). Qed.

  Definition k_mapping (g : rdf_graph I B L) : rdf_graph I B L :=
    @mkRdfGraph I B L (k_mapping_ts (graph g)) (uniq_k_mapping g).

  Section Kmapping_isocan.

(******************************************************************************)
(*            κ-mapping returns graphs isomorphic to the input                *)
(******************************************************************************)

    (* For any sequence of triples: ts,
       if the image of ts under k_mapping_ts is the empty sequence,
       then ts is also the empty sequence. *)
    Lemma k_mapping_nil_is_nil ts: k_mapping_ts ts = [::] -> ts = [::].
    Proof.
    case: ts=> // t ts' /max_foldl_minimum_in_st /orP[]//.
    + move=> y yin.
      suffices neqs : size y != 0.
        have := join_nil_size neqs.
        by rewrite /join_st; case: ifP.
      by move/mapP : yin=> [/= t']=> /mapP[/= p pin ->] ->; rewrite size_sort.
    + rewrite /s_can/= !map_nil_is_nil => /eqP.
      by apply contra_eq; rewrite permutations_neq_nil.
    + move=> /mapP[/=xs /mapP[/= a ain]] -> => /eqP.
      by rewrite eq_sym=> /eqP/(sort_nil le_triple_total le_triple_trans le_triple_anti).
    Qed.

    (* For any pair of duplicate-free sequence of triples: ts1 and ts2,
       and an isomorphism mu from ts1 to ts2,
       then for any sequence of triple: ts3
       which is equal to ts2 modulo permutation,
       then mu is also an isomorphism from ts1 to ts3. *)
    Lemma ts_pre_iso_iso_mem [ts1 ts2: seq (triple I B L)] [mu : B -> B]:
      uniq ts1 -> uniq ts2 ->
      is_effective_iso_ts ts1 ts2 mu -> forall (ts3 : (seq (triple I B L))), (perm_eq ts3 ts2) -> is_effective_iso_ts ts1 ts3 mu.
    Proof.
    move=> u1 u2 /and3P[piso urel peq] ts3 p13.
    apply/and3P; split=> //.
    + rewrite/is_pre_iso_ts/bnode_map_bij !uniq_get_bts; apply uniq_perm=> [| |b].
      * rewrite map_inj_in_uniq; first by rewrite uniq_get_bts.
        - by apply (is_pre_iso_ts_inj piso).
      * by rewrite uniq_get_bts.
      * move: piso=> /and3P [_ _ piso]; rewrite (perm_mem piso) /get_bts/get_bs.
        apply eq_mem_pmap=> bb; rewrite /bnodes_ts !mem_undup.
        rewrite !mem_filter; congr (andb (is_bnode bb)).
        rewrite /terms_ts !mem_undup.
        apply/flatten_mapP/flatten_mapP; move=> [/= t tin bbin]; exists t=> //.
        - by rewrite (perm_mem p13) tin.
        - by rewrite -(perm_mem p13) tin.
    + by rewrite perm_sym in p13; apply (perm_trans peq p13).
    Qed.


    (* For any duplicate-free sequence of triples: ts,
       k_mapping returns a sequence which is isomorphic_ts to ts *)
    Lemma kmapping_iso_out_ts ts (uts : uniq ts) : effective_iso_ts ts (k_mapping_ts ts).
    Proof.
    have := uniq_k_mapping_ts uts.
    rewrite /iso_ts/is_iso_ts/k_mapping_ts.
    case : (foldl_max_st (map (sort le_triple) (candidates ts)) [::]); first by move=> /k_mapping_nil_is_nil -> _; exists id.
    move=> /mapP/= [s /mapP[/= p pin ->] ->]; rewrite sort_uniq=> ukres.
    exists (kth_map p).
    suffices /(ts_pre_iso_effective_iso ukres) preiso : is_pre_iso_ts ts (relabeling_seq_triple (kth_map p) ts) (kth_map p).
      apply: (ts_pre_iso_iso_mem uts ukres preiso); apply: uniq_perm=> //.
       + by rewrite sort_uniq.
       + by move=> ?; rewrite mem_sort.
    by apply kth_map_preiso.
    Qed.

    (* For any RDF graph g, k_mapping returns a graph which is isomorphic to g *)
    Lemma kmapping_iso_out g: effective_iso g (k_mapping g).
    Proof. by apply: kmapping_iso_out_ts (ugraph _). Qed.

(******************************************************************************)
(*              Proofs to derive κ-mapping is a graph invariant               *)
(******************************************************************************)

    (* Move for RDF For any two sequences of triples ts1 and ts2 which are isomorphic,
       either both are the empty sequence, or both are different from the empty sequence *)
    Lemma iso_structure (ts1 ts2: seq (triple I B L)) :
      effective_iso_ts ts1 ts2 -> ((ts1 == [::]) && (ts2 == [::]) || (ts1 != [::]) && (ts2 != [::])).
    Proof.
    rewrite /iso_ts/is_iso_ts /=; move=> [? /and3P [_ _]] ; case: ts1=> [|h1 tl1].
    + by rewrite relabeling_seq_triple_nil perm_sym=> /perm_nilP ->.
    + by apply contraTneq=> -> ; apply /perm_nilP.
    Qed.

    (* Relabeling a sequence of triples under the build_kmapping_from_seq of the empty sequence
       does not change the sequence of triples *)
    Lemma build_from_nil (ts : seq (triple I B L)) :
      relabeling_seq_triple (build_kmapping_from_seq [::]) ts = ts.
    Proof. by elim: ts=> [//| a l IHl]; by rewrite /= relabeling_triple_id IHl. Qed.

    (* For every blank node: b, which is member of a sequence of blank nodes s,
       the hashed permutation of s has an element whose initial blank node value is b *)
    Lemma eqb_b_hterm_memP (b : B) (s : seq B) :
      b \in s ->
            has (eqb_b_hterm (I:=I) (L:=L) b) (hash_perm s).
      (* [seq Bnode (mkHinput an.1 an.2) | an <- zip s (iota 0 (size s))]. *)
    Proof.
    move=> b1in ; apply/ (has_nthP (Bnode (mkHinput b 0))).
    exists (index b s).
    by rewrite size_map size_zip size_iota minn_refl index_mem.
    by rewrite nth_mapzip /= ?size_iota // nth_index // eqxx.
    Qed.

    (* For every blank node: b, which is member of a duplicate-free sequence of blank nodes s,
       kth_map of s applid to b is exactly:
       nat_inj (nth 0 (iota 0 (size s)) (index b s). *)
    Lemma out_of_build b s :
      b \in s -> uniq s ->
            (kth_map s) b = nat_inj (nth 0 (iota 0 (size s)) (index b s)).
    Proof.
    move=> bin ubs.
    rewrite /kth_map/hash_perm/build_kmapping_from_seq /= (eqb_b_hterm_memP bin); congr nat_inj.
    by rewrite find_index_eqbb ?size_iota // nth_mapzip ?size_iota //.
    Qed.

    (* For any two RDF graphs g and h which are isomorphic,
       the image of g and h under k_mapping is isomorphic *)
    Lemma iso_isokmap g h (igh: effective_iso g h) : effective_iso (k_mapping g) (k_mapping h).
    Proof.
    by apply: effective_iso_can_trans _ igh; rewrite /mapping_is_effective_iso_mapping; apply kmapping_iso_out.
    Qed.

    (* For any permutation p of the blank nodes of a duplicate-free sequence of triples: ts,
       relabeling ts under (build_map_k p) remains uniq *)
    Lemma uniq_build_map_k_perm (ts: seq (triple I B L)) (u : uniq ts):
      forall p : seq B, p \in permutations (get_bts ts) -> uniq (relabeling_seq_triple (kth_map p) ts).
    Proof.
    move=> p pinperm.
    suffices /inj_get_bts_inj_ts : {in get_bts ts &, injective (build_kmapping_from_seq (hash_perm p))}.
      by move=> /map_inj_in_uniq ->.
    by apply labeled_perm_inj=> //; apply candidate_in_perm.
    Qed.

    (* For any duplicate-free sequence of blank nodes bs,
       and any map between blank nodes: mu which is locally injective in the domain: bs,
       for every blank node b in bs,
       (build_map_k bs b) assign the sames values as (build_map_k (map mu bs) (mu b)) *)
    Lemma build_modulo_map (ts : seq (triple I B L)) b bs mu :
      uniq bs -> {in bs&, injective mu} -> b \in bs ->
        kth_map bs b = kth_map [seq mu i | i <- bs] (mu b).
    Proof.
    move=> up mu_inj bin.
    have mub_in : mu b \in [seq mu i | i <- bs] by apply map_f.
    rewrite (out_of_build bin up) out_of_build //; last by rewrite map_inj_in_uniq.
    by congr nat_inj; rewrite !nth_iota ?index_mem // index_map_in.
    Qed.

    (* For any pair of duplicate-free sequence of triples: ts1 and ts2,
       and an isomorphism from ts1 to ts2,
       then for any graph in the sequence of sorted graph candidates of ts1,
       it is also in the sequence of sorted graph candidates of ts2 *)
    Lemma iso_s_can_mem ts1 ts2:
      uniq ts1 -> effective_iso_ts ts1 ts2 -> forall sc, sc \in s_can ts1 -> sc \in s_can ts2.
    Proof.
    move=> /= u1 iso12 sc /mapP /= [cc1 /mapP[/= p pinperm ->] ->].
    apply/mapP => /=.
    case : iso12 => mu /and3P [/and3P [_ _ piso] u peq].
    exists (relabeling_seq_triple (kth_map (map mu p)) ts2).
    + rewrite /candidates; apply/mapP=> /=.
      exists (map mu p)=> //.
      rewrite mem_permutations; apply: (perm_trans _ piso).
      by apply perm_map; rewrite -mem_permutations.
    + apply/rdf_leP; apply uniq_perm=> [| |t]; first by apply uniq_build_map_k_perm.
      - apply uniq_build_map_k_perm; first by rewrite -(perm_uniq peq).
        rewrite mem_permutations; rewrite /is_pre_iso_ts in piso.
        by apply: (perm_trans _ piso); apply perm_map; rewrite -mem_permutations.
      - have <- : (relabeling_seq_triple (kth_map (map mu p)) (relabeling_seq_triple mu ts1)) =i
                   (relabeling_seq_triple (kth_map [seq mu i | i <- p]) ts2).
          by apply relabeling_mem; apply perm_mem.
        rewrite relabeling_seq_triple_comp; apply relabeling_ext_in.
        rewrite mem_permutations in pinperm.
        suffices build_modulo_map :
          forall b, b \in p -> (kth_map p) b = kth_map (map mu p) (mu b).
          by case=> [[]]//s []p' []o// sib pii tin //=;
               apply triple_inj=> //=; congr Bnode;
                 rewrite build_modulo_map // (perm_mem pinperm); apply (mem_ts_mem_triple_bts tin);
                   rewrite /bnodes_triple filter_undup mem_undup /= ?in_cons ?eqxx ?orbT //.
        have mu_inj : {in p &, injective mu}.
        have {}piso : is_pre_iso_ts ts1 ts2 mu. by apply /and3P; rewrite !uniq_get_bts.
          by move=> x y xin yin; apply (is_pre_iso_ts_inj2 piso); rewrite -(perm_mem pinperm).
        have up : uniq p by rewrite (perm_uniq pinperm) uniq_get_bts.
        by move=> b; apply (build_modulo_map ts1 up mu_inj).
    Qed.

    (* For any pair of duplicate-free sequence of triples: ts1 and ts2,
       and an isomorphism from ts1 to ts2,
       the sequences of sorted graph candidates of ts1 and ts2 have the same graphs *)
    Lemma iso_memeq_s_can ts1 ts2 :
      uniq ts1 -> uniq ts2 -> effective_iso_ts ts1 ts2 -> s_can ts1 =i s_can ts2.
    Proof.
    move=> u1 u2 isogh sc; apply/idP/idP.
    + by apply iso_s_can_mem.
    + have isohg: effective_iso_ts ts2 ts1. by apply effective_iso_ts_sym.
      by apply iso_s_can_mem.
    Qed.

    (* For any two graphs g and h which are isomorphic,
       k_mapping returns set-equal results for g and h *)
    Lemma kmapping_can_invariant ts1 ts2 (u1 : uniq ts1) (u2 : uniq ts2) (isogh : effective_iso_ts ts1 ts2) :
      perm_eq (k_mapping_ts ts1) (k_mapping_ts ts2).
    Proof.
    rewrite /k_mapping_ts.
    suffices memeq : s_can ts1 =i (s_can ts2).
      (* rewrite !foldl_idx (eq_big_idem (fun x => true) _ Order.POrderTheory.maxxx  memeq). *)
      (* todo: when changing *)
      by rewrite !foldl_idx (eq_big_idem (fun x => true) _ (@join_st_idem disp I B L) memeq).
    by apply iso_memeq_s_can.
    Qed.

    (* k_mapping is an isocanonical mapping *)
    Theorem effective_iso_can_kmapping : effective_isocanonical_mapping k_mapping.
    Proof.
    split=> [|g h].
    move=> g. rewrite /iso.
    + by apply kmapping_iso_out.
    + split.
      - by apply same_res_impl_effective_iso_mapping; rewrite /mapping_is_effective_iso_mapping; apply kmapping_iso_out.
      - by apply: kmapping_can_invariant (ugraph _) (ugraph _).
    Qed.

    Theorem spec_iso_can_kmapping : spec_isocanonical_mapping k_mapping.
    Proof. by apply effective_iso_can_spec_iso_can; apply effective_iso_can_kmapping. Qed.

  End Kmapping_isocan.

End Kmapping.
