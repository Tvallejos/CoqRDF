From Equations Require Import Equations.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
(* Unset Strict Implicit. *)
Unset Printing Implicit Defensive.
From RDF Require Export Rdf Triple Term Util IsoCan.

(******************************************************************************)
(*                                                                            *)
(*            template defined with equations                                 *)
(*                                                                            *)
(******************************************************************************)

Section Partition.

  Variable B : eqType.

  (* Hash maps as sequences of pairs of a b-node and a hash *)
  Definition hash_map := seq (B * nat).

  (* Type of an element of a partition *)
  Definition part := seq (B * nat).
  (* Type of partitions *)
  Definition partition := seq part.

  (* TODO : remove *)
  Definition pred_eq {T : eqType} (t: T):= fun t'=> t == t'.
  (* Tests whether the hash of p is n *)
  Definition eq_hash (n : nat) (p: B * nat) := pred_eq n p.2.
  (* Tests whether the node of p is b *)
  Definition eq_bnode (b : B) (p: B * nat) := pred_eq b p.1.
  (* splits hm according to hash n *)
  Definition partitionate (n : nat) (hm : hash_map) :=
    (filter (eq_hash n) hm, filter (negb \o eq_hash n) hm).
  Equations? gen_partition (hm : hash_map) : partition by wf (size hm) lt :=
    gen_partition nil := nil;
    gen_partition (bn::l) :=
      ((partitionate bn.2 (bn::l)).1) :: gen_partition (partitionate bn.2 (bn::l)).2.
  Proof.
    rewrite /= /eq_hash/pred_eq/negb /= eqxx /=.
    have H := size_filter_le ((fun b : bool => if b then false else true) \o (fun p : B * nat => n == p.2)) l.
    by apply /ltP; apply : leq_trans H _.
  Qed.

  Lemma hm_zip (hm : hash_map): hm = zip (map fst hm) (map snd hm).
  Proof. by rewrite zip_map; elim: hm => [//| [h1 h2] tl IHtl] /=; rewrite -IHtl. Qed.

  Lemma eq_hash_refl (bn : (B * nat)) : eq_hash bn.2 bn.
  Proof. by rewrite /eq_hash/pred_eq eqxx. Qed.

  Lemma eq_hash_sym (bn1 bn2 : (B * nat)) : eq_hash bn1.2 bn2 = eq_hash bn2.2 bn1.
  Proof. by apply /idP/idP; rewrite /eq_hash/pred_eq=> /eqP->; rewrite eqxx. Qed.

  Lemma part_size (hm : hash_map) : forall (p : part), p \in (gen_partition hm) -> size p > 0.
  Proof.
  move=> p; funelim (gen_partition hm)=> [//|].
  rewrite in_cons=> /orP[]; last by apply H.
  by move=> /eqP ->; rewrite /= eq_hash_refl.
  Qed.

  Lemma part_all_eq_hash (hd : B * nat) (tl : seq (B * nat)) (hm : hash_map) :
  (hd :: tl \in gen_partition hm) -> all (eq_hash hd.2) (hd::tl).
  Proof.
  funelim (gen_partition hm)=> [//|].
  rewrite in_cons=> /orP[].
  + move=> /eqP eq.
    suffices eqhash : bn.2 = hd.2.
      by rewrite eq eqhash; apply filter_all.
    by move: eq=> /=; rewrite /eq_hash/pred_eq eqxx; move=> [->].
  move=> inP; apply H; apply inP.
  Qed.


  Lemma gen_partition_filter (hd a : B * nat) (tl : seq (B * nat)) (hm' : hash_map) :
    hd :: tl \in gen_partition [seq x <- hm' | (negb \o eq_hash a.2) x] -> eq_hash hd.2 a = false.
  Proof.
  set hm := [seq x <- hm' | (negb \o eq_hash a.2) x].
  have : size hm < S (size hm) by apply ltnSn.
  have : all (negb \o eq_hash a.2) hm by apply filter_all.
  move: hm (size hm).+1.
  move=> hm n; move: n hm=> n.
  elim: n hd a => [//| n' IHn hd a hm] allPn measure.
  move: allPn.
  case: hm measure => [//|c l].
  autorewrite with gen_partition.
  rewrite in_cons.
  move=> measure allPn /orP[].
  rewrite /=. rewrite eq_hash_refl=> /eqP[-> _].
  by move: allPn=> /=/andP[]; rewrite eq_hash_sym; case: (eq_hash c.2 a). 
  move=> pin.
  have:= pin.
  apply IHn.
  move: allPn.
  set hs := c :: l.
  rewrite all_filter=> allPn.
  apply /allP.
  move=> /= bn bnin.
  apply /implyP.
  move=> _.
  by have /=-> := in_all bnin allPn.
  rewrite /=eq_hash_refl/=.
  by apply (leq_ltn_trans (size_filter_le _ l) measure).
  Qed.

  Lemma part_filter (hd : B * nat) (tl : seq (B * nat)) (hm : hash_map) :
    (hd :: tl \in gen_partition hm) -> hd :: tl = (partitionate hd.2 hm).1.
  Proof.
  have : size hm < S (size hm) by apply ltnSn.
  move: hm (size hm).+1.
  move=> hm n; move: n hm=> n.
  elim: n hd => [//| n' IHn hd hm] measure.
  case: hm measure => [//|a l].
  autorewrite with gen_partition.
  rewrite in_cons.
  move=> measure /orP[].
  rewrite /=. rewrite eq_hash_refl=> /eqP[-> ->].
  by rewrite eq_hash_refl.
  rewrite /= eq_hash_refl /==> pin.
  suffices neq_hash : eq_hash hd.2 a = false.
    rewrite neq_hash (IHn _ _ _ pin) /=.
    + rewrite -filter_predI.
      suffices /eq_filter-> : (predI (eq_hash hd.2) (negb \o eq_hash a.2)) =1 (eq_hash hd.2) by [].
      move=> bn /=; move: neq_hash; rewrite /eq_hash/pred_eq/negb eq_sym.
      by case_eq (hd.2 == bn.2)=> // /eqP -> ->.
    + move: measure=> /= measure.
      by apply (leq_ltn_trans (size_filter_le _ _) measure).
  by apply (gen_partition_filter _ _ _ _ pin).
  Qed.

  Lemma partP (hm : hash_map):
    forall (p : part), p \in (gen_partition hm) ->
      (* exists (bn : B * nat), bn \in hm /\ p = (partitionate bn.2 hm).1. *)
      exists (bn : B * nat), p = (partitionate bn.2 hm).1.
  Proof.
  move=> p pin.
  have /part_size := pin.
  move: pin.
  by case: p=> [//|hd tl] /part_filter ->; exists hd.
  Qed.

  Lemma partition_memP (hm : hash_map) :
    forall (p: part), p \in (gen_partition hm) -> subseq p hm.
  Proof.
  by move=> p /partP[bn ->]; apply filter_subseq.
  Qed.
End Partition.

Section Template.
  Variable disp : unit.
  (* TODO : check that order is needed, since below comes a comparison comp on graphs *)
  Variable I B L : orderType disp.
  Notation le_triple := (@le_triple disp I B L).


(* Enumeration of b-nodes *)
  Hypothesis nat_inj : nat -> B.
  Hypothesis nat_inj_ : injective nat_inj.

  (* comparison on graphs, morally an order relation.
     TODO : we can relax all assumptions on cmp/choose_graph to the relabelling of
     the graph to be canonized, is it relevant? *)
  Variable (cmp : seq (triple I B L) -> seq (triple I B L) -> bool).

  Hypothesis cmp_anti : antisymmetric cmp.
  Hypothesis cmp_total : total cmp.
  Hypothesis cmp_trans : transitive cmp.

  Lemma cmp_refl (g : seq (triple I B L)) : cmp g g.
  Proof. by move: (cmp_total g g); move=> /orP[]. Qed.

  Definition choose_graph (g1 g2 : seq (triple I B L)) :=
    if cmp g1 g2 then g2 else g1.

  Lemma choose_graphA : associative choose_graph.
  Proof.
  move=> g h i; rewrite /choose_graph.
  repeat (try case : ifP); rewrite //.
  + by move=> _ ->.
  + by move=> ghn ->.
  + by move=> _ ->.
  + by move=> gh hi; rewrite (cmp_trans gh hi).
  + by move=> _ ->.
  + by move=> _ ->.
  + move=> ghn gi hin _.
    move: (cmp_total g h) (cmp_total h i); rewrite ghn hin /==> hg ih {ghn hin}.
    have hi := (cmp_trans hg gi).
    have eq_hi : h = i by apply cmp_anti; rewrite hi ih.
    by apply cmp_anti; rewrite gi -eq_hi hg.
  Qed.

  Lemma choose_graphC : commutative choose_graph.
  Proof.
  move=> x y; rewrite /choose_graph; case: ifP; case: ifP=> //.
  + by move=> yx xy; apply cmp_anti; apply /andP.
  + by move=> yxn xyn; move: (cmp_total x y); rewrite xyn yxn.
  Qed.

  Lemma choose_graph_idem : idempotent choose_graph.
  Proof.
  by move=> x; rewrite /choose_graph cmp_refl.
  Qed.

  (* A default graph *)
  Variable can : seq (triple I B L).
  Hypothesis ucan : uniq can.
  Hypothesis sort_can : sort le_triple can = can.
  Hypothesis can_nil : can = nil.
  (* Determines a choice of default graph can *)
  Hypothesis can_extremum : forall (x : seq (triple I B L)), cmp can x.

  Lemma can_lid : left_id can choose_graph.
  Proof. by move=> x; rewrite /choose_graph can_extremum. Qed.

  HB.instance Definition _ :=
    Monoid.isComLaw.Build
      (seq (triple I B L)) can
      (choose_graph) choose_graphA
      choose_graphC
      can_lid.

  Local Notation hash_map := (@hash_map B).
  Local Notation part := (@part B).
  Local Notation partition := (@partition B).
  (* Initial hash map from a graph *)
  Definition bnodes_hm (hm : hash_map): seq B := map fst hm.

  Variable (init_hash : seq (triple I B L) -> hash_map).
  (* init_hash g has the same bnodes as the graph g *)
  Hypothesis good_init :
    forall (g : seq (triple I B L)), bnodes_hm (init_hash g) =i get_bts g.

  (* Pick a part p from a failed attempt at computing a fine partition from the input hashmap hm. Expected:
     - (map fst p) is included in (map fst hm)
     - elements of p have the same hash
     - p is non empty and non singleton *)
  Variable choose_part : hash_map -> part.
  (* all nodes in choose_part hm lead to bnodes of hm, but with possibly changed hashes.
     remember the list of bnodes of a graph is unique *)
  Hypothesis in_part_in_bnodes' :
    forall (bn : B * nat) hm, bn \in choose_part hm -> bn \in hm.

  Lemma in_part_in_bnodes (bn : B * nat) hm: bn \in choose_part hm -> bn.1 \in bnodes_hm hm.
  Proof.
  move/in_part_in_bnodes'; rewrite /bnodes_hm; rewrite {1}(hm_zip hm).
  by case: bn=> [b n] /in_zip/andP[->].
  Qed.

  (* update a hashmap from an input graph, without increasing the measure *)
  Variables (color color_refine : seq (triple I B L) -> hash_map -> hash_map).

  (* coloring a hashmap of a graph using the same graph does not change its bnodes
     TODO : Pick one of the versions, color_bnodes is stronger but may be not needed. *)
  Hypothesis color_good_hm :
    forall (g : seq (triple I B L)) hm,
      bnodes_hm hm =i get_bts g -> bnodes_hm (color g hm) =i get_bts g.
  (* Hypothesis color_bnodes : forall (g : seq (triple I B L)) hm, bnodes_hm (color g hm) =i bnodes_hm hm. *)

  (* Same for color_refine *)
  Hypothesis color_refine_good_hm :
    forall (g : seq (triple I B L)) hm,
      bnodes_hm hm =i get_bts g -> bnodes_hm (color_refine g hm) =i get_bts g.

  (* Marks a bnode in a hashmap*)
  Variable (mark : B -> hash_map -> hash_map).
  (* Marking a hashmap with one of its bnodes does not change its bnodes (but only the hashes)*)
  Hypothesis good_mark :
    forall (g : seq (triple I B L)) (hm : hash_map),
      bnodes_hm hm =i get_bts g ->
      forall b, b \in bnodes_hm hm -> bnodes_hm (mark b hm) =i get_bts g.
  (* TODO : to be simplified into
    Hypothesis good_mark : forall (hm : hash_map),
     forall b, b \in bnodes_hm hm -> bnodes_hm (mark b hm) =i bnodes_hm hm.
   *)

  (* Measure on hash_map*)
  Variable (M : hash_map -> nat).

  (* Mark decreases the measure *)
  Hypothesis markP :
    forall (bn : B * nat) (hm : hash_map),
      bn \in choose_part hm -> M (mark bn.1 hm) < M hm.
  (* color_refine does not increase the measure *)
  Hypothesis color_refineP :
    forall (g : seq (triple I B L)) (hm : hash_map) ,
      M (color_refine g hm) <= M hm.

  Local Notation eq_hash := (@eq_hash B).
  Local Notation eq_bnode := (@eq_bnode B).

  Definition fun_of_hash_map (hm : hash_map) : B -> B :=
    fun b =>
      if has (eq_bnode b) hm then
        let the_label := nth O (map snd hm) (find (eq_bnode b) hm) in
        nat_inj the_label
      else
        b.

  Hypothesis iso_color_fine_can :
    forall (g h : seq (triple I B L)),
      uniq g -> uniq h ->
      effective_iso_ts g h ->
         relabeling_seq_triple (fun_of_hash_map (color g (init_hash g))) g
      =i relabeling_seq_triple (fun_of_hash_map (color h (init_hash h))) h.

  Lemma nat_coq_nat (n m : nat) :  (n < m)%nat = (n < m). Proof. by []. Qed.
  Lemma nat_coq_le_nat (n m : nat) :  (n <= m)%N = (n <= m). Proof. by []. Qed.

  Definition is_trivial (p : part) : bool := size p == 1.
  Definition is_fine (P : partition) : bool := all is_trivial P.
  Definition hashes_hm (hm : hash_map): seq nat :=
    map snd hm.

  Equations? foldl_In {T R : eqType} (s : seq T) (f : R -> forall (y : T), y \in s -> R) (z : R) : R :=
    foldl_In nil f z := z;
    foldl_In (a :: l) f z := foldl_In l (fun x y inP=> f x y _) (f z a _).
  Proof.
  by rewrite in_cons inP orbT.
  by rewrite in_cons eqxx.
  Qed.

  Lemma foldl_foldl_eq {T R : eqType} (s : list T) (f : R -> T -> R) z :
    @foldl_In _ _ s (fun (r:R) (t:T) (_ : t \in s) => f r t) z = foldl f z s.
  Proof.
  funelim (foldl_In s _ z).
  - by [].
  - autorewrite with foldl_In; apply H.
  Qed.

  Section Distinguish.

    Lemma bnodes_hm_exists (hm : hash_map) :
      forall b, b \in bnodes_hm hm -> exists n, (b,n) \in hm.
    Proof.
    by move=> b /mapP/=[[b' n] bin ->]/=; exists n.
    Qed.

    Lemma bnodes_hm_has_eq_bnodes (hm : hash_map) :
      forall b, b \in bnodes_hm hm -> has (eq_bnode b) hm.
    Proof.
    move=> b /bnodes_hm_exists/=[n bnin].
    apply /hasP; exists (b,n)=> //.
    by rewrite /eq_bnode/pred_eq eqxx.
    Qed.

    Lemma find_index_eq_bnode bs s (bn : B) :
      size s = size bs ->
      find (eq_bnode bn) (zip bs s) = index bn bs.
    Proof.
    elim: bs s => [| a l IHl]; first by move=> ?; rewrite zip0s.
    by case =>  [//| b l2] /= [eqsize_tl]; rewrite eq_sym IHl //.
    Qed.

    Lemma find_index_eq_hash bs s (bn : nat) :
      size s = size bs ->
      find (eq_hash bn) (zip bs s) = index bn s.
    Proof.
    elim: s bs => [| a l IHl] bs; first by move=> ?; rewrite zips0.
    by case: bs => [//| b l2] /= [eqsize_tl]; rewrite eq_sym IHl //.
    Qed.

    Lemma rem_swap (T : eqType) (s : seq T) (x y : T):
      rem x (rem y s) = rem y (rem x s).
    Proof.
    elim: s=> [//| h tl IHtl] /=.
    case: ifP.
    + move=> /eqP eqhy; rewrite eqhy.
      case: ifP; first by move /eqP ->.
      by rewrite /= eqxx.
    + move=> neq_hy; case: ifP; first by move=> /eqP -> /=; rewrite eqxx.
      by move=> neq_hx /=; rewrite neq_hx neq_hy IHtl.
    Qed.

    Lemma size_proj (T1 T2 : Type) (s : seq (T1 * T2)) :
      size [seq i.2 | i <- s] = size [seq i.1 | i <- s].
    Proof. by elim: s=> [//| h tl IHtl] /=; rewrite IHtl. Qed.

    Lemma pair_zip_in (T1 T2 : eqType) (s1 : seq T1) (s2 : seq T2) (x0 x : T2) (y1: T1) (i : nat) :
      size s1 = size s2 -> i < size s2 -> nth x0 s2 i = x ->
      exists t1, (t1,x) \in zip s1 s2 /\ nth (t1,x0) (zip s1 s2) i = (t1,x).
    Proof.
    move=> eq_size i_in <-.
    exists (nth y1 s1 i); split.
    + rewrite -nth_zip //; apply mem_nth.
      by rewrite size_zip eq_size minn_refl.
    + rewrite nth_zip //; congr pair.
      by apply set_nth_default; rewrite eq_size.
    Qed.

    Lemma hashes_filter_neq (n m : nat) (hm : hash_map) :
      (m == n) = false ->
        n \in hashes_hm hm ->
          n \in hashes_hm (filter (negb \o (fun p0 : B * nat => m == p0.2)) hm).
    Proof.
    set p := negb \o (fun p0 : B * nat => m == p0.2).
    elim: hm=> [//| h tl IHtl] /=.
    rewrite in_cons; move=> neq /orP[/eqP eq| in_tl].
    + by rewrite /p/= -eq neq /= in_cons eq eqxx.
    + case: h=> b n'; rewrite /p/=.
      case_eq (m != n')=> H; last by apply IHtl.
      by rewrite /=; apply inweak; apply IHtl.
    Qed.


    Lemma partitionate_filter (n m : nat) (hm : hash_map):
      (n == m) = false ->
        (partitionate n hm).1 = (partitionate n [seq x <- hm | (negb \o eq_hash m) x]).1.
    Proof.
    elim: hm=> [//| h tl IHtl] neq; rewrite /=/eq_hash/pred_eq.
    case: ifP=> [/eqP eq_nh2| ]/=; last first.
    + move=> neq_nh2; rewrite /negb.
      by case: ifP; case: ifP=> //neq_mh2 _ /=; rewrite ?neq_nh2; apply IHtl.
    rewrite eq_sym in neq; rewrite -eq_nh2 neq /= eq_nh2 eqxx; congr cons.
    have -> : [seq p <- tl | h.2 == p.2] = (partitionate h.2 tl).1 by [].
    have -> : [seq p <- [seq x <- tl | m != x.2] | h.2 == p.2]
              = (partitionate n [seq x <- tl | (negb \o eq_hash m) x]).1.
      by rewrite /eq_hash/=/pred_eq/= eq_nh2.
    by rewrite -eq_nh2; apply IHtl; rewrite eq_sym.
    Qed.

    Lemma part_in_partition (n : nat) (hm : hash_map) :
      n \in (hashes_hm hm) -> (partitionate n hm).1 \in gen_partition hm.
    Proof.
    have : size hm < S (size hm) by apply ltnSn.
    move: hm (size hm).+1.
    move=> hm n1; move: n1 hm=> n1.
    elim: n1 => [//| n1 IHn hm].
    case hm=> //p tl/=.
    rewrite -nat_coq_nat ltnS nat_coq_nat=> measure.
    rewrite in_cons=> /orP[/eqP eq_np|].
    + rewrite eq_np/eq_hash/pred_eq eqxx.
      autorewrite with gen_partition.
      by rewrite in_cons /=/eq_hash/pred_eq !eqxx.
    + case_eq (n == p.2)=> [/eqP->|].
      - rewrite /eq_hash/pred_eq !eqxx=> nin.
        by autorewrite with gen_partition; rewrite in_cons /= /eq_hash/pred_eq !eqxx.
      move=> neq_np nin; rewrite /eq_hash/pred_eq neq_np.
      autorewrite with gen_partition; rewrite in_cons /= /eq_hash/pred_eq !eqxx /=.
      suffices -> : ([seq p0 <- tl | n == p0.2] \in gen_partition [seq x <- tl | (negb \o (fun p0 : B * nat => p.2 == p0.2)) x]).
        by rewrite orbT.
      have -> : [seq p0 <- tl | n == p0.2] = (partitionate n tl).1 by [].
      rewrite (partitionate_filter n p.2) //; apply IHn.
      + by apply: leq_ltn_trans measure; apply size_filter_le.
      + by apply hashes_filter_neq=> //; rewrite eq_sym neq_np.
    Qed.

    Lemma is_fine_uniq (hm : hash_map) :
      is_fine (gen_partition hm) -> uniq (hashes_hm hm).
    Proof.
    apply contraTT.
    move=> /(uniqPn O)/= [i [j [lt_ij j_in ]]].
    set xi := nth O (map snd hm) i.
    set xj := nth O (map snd hm) j.
    move=> eq_xij; apply /allPn=> /=.
    set wt := (partitionate xi hm).1.
    suffices wt_in : wt \in (gen_partition hm).
      exists wt=> //; rewrite /is_trivial.
      suffices : size wt >= 2.
        by case_eq (size wt == 1)=> //; move=> /eqP->.
      suffices -> : size wt = count (eq_hash xi) hm.
        suffices [[b [bin nth_i]] [b' [b'in nthj]]]:
          (exists b, (b,xi) \in hm /\ nth (b,O) hm i = (b,xi))
          /\ exists b', (b',xj) \in hm /\ nth (b',O) hm j = (b',xj).
          rewrite -(cat_take_drop j hm) !count_cat.
          suffices has_countxi : (1 <= count (eq_hash xi) (take j hm))%N.
            suffices has_countxj : (1 <= count (eq_hash xi) (drop j hm))%N.
              by rewrite -add1n -nat_coq_le_nat; apply leq_add.
            rewrite -has_count; apply /(has_nthP (b',0)).
            exists 0; first by rewrite size_drop subn_gt0; rewrite size_map in j_in.
            by rewrite nth_drop addn0 nthj eq_xij /eq_hash/=/pred_eq eqxx.
          rewrite -has_count; apply /(has_nthP (b,0)).
          exists i.
          + rewrite size_take_min ltn_min; apply /andP; split; first exact: lt_ij.
            by rewrite size_map in j_in; apply (ltn_trans lt_ij j_in).
          by rewrite nth_take // nth_i /eq_hash/=/pred_eq eqxx.
        split; rewrite (hm_zip hm); apply pair_zip_in=> //; rewrite -?size_proj //.
        + exact: nat_inj O.
        + by apply: ltn_trans lt_ij j_in.
        exact: nat_inj O.
      suffices partP : forall (n : nat) (hm : hash_map), n \in (hashes_hm hm) -> size (partitionate n hm).1 = count (eq_hash n) hm.
        by apply partP; apply mem_nth; apply: ltn_trans lt_ij j_in.
      by move=> n hm0 nin; rewrite /partitionate/= size_filter.
    suffices partIn : forall (n : nat) (hm : hash_map), n \in (hashes_hm hm) -> (partitionate n hm).1 \in gen_partition hm.
      by apply partIn ; apply mem_nth; apply: ltn_trans lt_ij j_in.
    by move=> n hm0 nin; apply part_in_partition.
    Qed.

    Lemma nth_funof (g : seq (triple I B L)) (hm : hash_map) :
      bnodes_hm hm =i get_bts g ->
        is_fine (gen_partition hm) ->
          forall (b : B) dfb dfn (bin : b \in get_bts g),
            exists n, (nth (dfb, dfn) hm (index b [seq i.1 | i <- hm])) = (b,n).
    Proof.
    move=> mem_eq fine b bdf dfn; rewrite -mem_eq.
    exists (nth dfn [seq i.2 | i <- hm] (index b [seq i.1 | i <- hm])).
    rewrite (hm_zip hm) nth_zip; last by rewrite size_proj.
    by rewrite -hm_zip; congr pair; rewrite nth_index.
    Qed.

    Lemma funof_snd_inj (g : seq (triple I B L)) (hm : hash_map) :
      bnodes_hm hm =i get_bts g ->
        is_fine (gen_partition hm) ->
          {in hm &, injective [eta snd]}.
    Proof.
    rewrite (hm_zip hm).
    set hm' := zip _ _.
    move=> mem_eq fine uhm /= bn bn' bnin bn'in.
    eapply (zip_uniq_proj2 )=> //.
    + by apply is_fine_uniq; apply fine.
    + by symmetry; apply size_proj.
    + by rewrite -hm_zip.
    + by rewrite -hm_zip.
    Qed.

    Lemma uniq_get_bts_is_fine (g : seq (triple I B L)) hm :
      bnodes_hm hm =i get_bts g ->
        is_fine (gen_partition hm) ->
          uniq [seq fun_of_hash_map hm i | i <- get_bts g].
    Proof.
    move=> mem_eq fine.
    apply /in_map_injP; first by apply uniq_get_bts.
    move=> b b'; rewrite -!mem_eq=> bin b'in.
    rewrite /fun_of_hash_map.
    have hasb := (bnodes_hm_has_eq_bnodes _ _ bin).
    have hasb' := (bnodes_hm_has_eq_bnodes _ _ b'in).
    rewrite hasb hasb' => /nat_inj_.
    have eqsize: size [seq i.2 | i <- hm] = size [seq i.1 | i <- hm] by apply size_proj.
    rewrite (hm_zip hm) !find_index_eq_bnode // -!hm_zip.
    move=> /eqP.
    have [n nin]:= bnodes_hm_exists hm b bin.
    have [n' n'in]:= bnodes_hm_exists hm b' b'in.
    suffices [inb inb'] :
      (index b [seq i.1 | i <- hm] < size hm)%N /\ (index b' [seq i.1 | i <- hm] < size hm)%N.
      rewrite (nth_map (b,O)) // (nth_map (b',O)) //.
      have [n'' n''P]: exists n, (nth (b, O) hm (index b [seq i.1 | i <- hm])) = (b,n).
        by apply (nth_funof g)=> //; rewrite -mem_eq.
      rewrite n''P.
      have [n''' n'''P]: exists n, (nth (b', O) hm (index b' [seq i.1 | i <- hm])) = (b',n).
        by apply (nth_funof g)=> //; rewrite -mem_eq.
      rewrite n'''P.
      move=> /eqP /(funof_snd_inj g hm mem_eq fine).
      rewrite -{1}n''P -{1}n'''P => /(_ (mem_nth _ inb) (mem_nth _ inb')).
      by move=> [].
    by split; rewrite -(find_index_eq_bnode (map fst hm) (map snd hm)) // -hm_zip -has_find.
    Qed.

    Lemma uniq_label_is_fine (g : seq (triple I B L)) (ug: uniq g) (hm : hash_map) :
      bnodes_hm hm =i get_bts g ->
        is_fine (gen_partition hm) ->
          uniq (relabeling_seq_triple (fun_of_hash_map hm) g).
    Proof.
    move=> mem_eq fine.
    have := uniq_get_bts_is_fine _ _ mem_eq fine.
    move=> /(in_map_injP _ (uniq_get_bts _)) mu_inj.
    rewrite map_inj_in_uniq=> //.
    by apply inj_get_bts_inj_ts.
    Qed.

    Equations? distinguish__
      (g : seq (triple I B L))
        (hm : hash_map)
        (gbot : seq (triple I B L))
        : seq (triple I B L) by wf (M hm) lt :=
      distinguish__ g hm gbot :=
      let p := choose_part hm in
	    let d := fun bn inP =>
	               let hm' := color_refine g (mark bn.1 hm) in
	               if is_fine (gen_partition hm') then
	                 let candidate := sort le_triple (relabeling_seq_triple (fun_of_hash_map hm') g) in
	                 candidate
	               else (distinguish__ g hm' gbot) in
      let f := fun gbot bn inP  =>
                 let candidate := d bn inP in
                 if cmp gbot candidate then candidate else gbot in
      foldl_In p f gbot.
      Proof.
      by apply /ltP; apply (leq_ltn_trans (color_refineP _ _) (markP _ _ inP)).
      Qed.

    Definition distinguish (g : seq (triple I B L)) (hm : hash_map) : seq (triple I B L) :=
      distinguish__ g hm can.

    Definition distinguish_ (g : seq (triple I B L)) (hm : hash_map) : seq (triple I B L) :=
      let p := choose_part hm in
	    let d := fun bn =>
	               let hm' := color_refine g (mark bn.1 hm) in
	               if is_fine (gen_partition hm') then
	                 let candidate := sort le_triple (relabeling_seq_triple (fun_of_hash_map hm') g) in
	                 candidate
	               else (distinguish g hm') in
      let f := fun gbot bn  =>
                 let candidate := d bn in
                 if cmp gbot candidate then candidate else gbot in
      foldl f can p.

    Lemma eq_distinguish (g : seq (triple I B L)) (hm : hash_map) :
      distinguish g hm = distinguish_ g hm.
    Proof.
    rewrite /distinguish_/distinguish -foldl_foldl_eq.
    by autorewrite with distinguish__.
    Qed.

    Definition canonicalize (g : seq (triple I B L)) (hm : hash_map)
      (* (gbot : seq (triple I B L)) *)
      (bn : (B * nat)) :=
	      let hm' := color_refine g (mark bn.1 hm) in
	      if is_fine (gen_partition hm') then
	        let candidate := sort le_triple (relabeling_seq_triple (fun_of_hash_map hm') g) in
	        candidate
	      else (distinguish g hm').

    Definition distinguish_fold (g : seq (triple I B L)) (hm : hash_map) : seq (triple I B L) :=
      let p := choose_part hm in
      foldl choose_graph can (map (canonicalize g hm) p).

    Lemma fold_map (T1 T2 R : Type) (f : R -> T2 -> R) (g : T1 -> T2) (z : R) (s : seq T1) :
      foldl (fun r1 t1=> f r1 (g t1)) z s = foldl f z (map g s).
    Proof. by elim: s z=> [//| a tl IHl] /= z; rewrite -IHl. Qed.

    Lemma distinguish_fold_map (g : seq (triple I B L)) (hm : hash_map) :
      distinguish g hm = distinguish_fold g hm.
    Proof. by rewrite /distinguish_fold eq_distinguish /distinguish_  -fold_map. Qed.

    Definition template (g : seq (triple I B L)) :=
      let hm := init_hash g in
      let hm' := color g hm in
      let iso_g := if is_fine (gen_partition hm')
                   then (sort le_triple (relabeling_seq_triple (fun_of_hash_map hm') g))
                   else distinguish g hm' in
      iso_g.

    Lemma distinguish_choice_default (gs: seq (seq (triple I B L))) (x0: seq (triple I B L)) :
      let ans := foldl choose_graph x0 gs in
     ans = x0 \/ ans \in gs.
    Proof.
    move=> ans; rewrite /ans{ans}.
    elim: gs x0 => [//| t ts IHts] x0; first by left.
    + rewrite in_cons /=. case: (IHts (choose_graph x0 t))=> [ -> |intail] /=.
    - rewrite /choose_graph; case: ifP=> _; first by right; rewrite eqxx.
      * by left.
    - by right; rewrite intail orbT.
    Qed.

    Lemma distinguish_choice (g : seq (triple I B L)) (hm: hash_map) :
      distinguish g hm = can \/ distinguish g hm \in (map (canonicalize g hm) (choose_part hm)).
    Proof. by rewrite distinguish_fold_map; apply distinguish_choice_default. Qed.

    Lemma uniq_distinguish (g : seq (triple I B L)) (ug: uniq g) hm :
      bnodes_hm hm =i get_bts g -> (negb \o is_fine) (gen_partition hm) -> uniq (distinguish g hm).
    Proof.
    have : M hm < S (M hm) by apply ltnSn.
    move: hm (M hm).+1.
    move=> hm n; move: n hm=> n.
    elim: n => [//| n IHn hm].
    case: (distinguish_choice g hm); first by move=> ->; rewrite ucan.
    move=> /mapP/= [bn pin ->].
    move=> MH eqbns finePn.
    rewrite /canonicalize.
    case: ifP.
    -  move=> isFine; rewrite sort_uniq.
       apply uniq_label_is_fine=> //. apply color_refine_good_hm. apply good_mark. apply eqbns.
       by apply in_part_in_bnodes.
    - move=> finePn1. apply IHn.
      apply: Order.POrderTheory.le_lt_trans (color_refineP _ _) _.
      by apply: Order.POrderTheory.lt_le_trans (markP _ _ _) MH.
    -  by apply color_refine_good_hm; apply good_mark=> //; apply in_part_in_bnodes.
    -  by move=> /=; rewrite finePn1.
    Qed.

    Lemma uniq_template (g : seq (triple I B L)) (ug: uniq g) : uniq (template g).
    Proof.
    rewrite /template; case: ifP=> H.
    + rewrite sort_uniq; apply uniq_label_is_fine=> //.
      by move=> h; rewrite color_good_hm.
    by apply uniq_distinguish=> //= ; rewrite ?H//; apply color_good_hm.
    Qed.

    Lemma mem_nilP (T : eqType) (s : seq T) : s =i [::] <-> s = [::].
    Proof.
    case: s=> [//| h tl]; split=> [mem|//].
    have := in_nil h.
    by rewrite -mem in_cons eqxx //.
    Qed.

    Lemma mem_eq_terms_ts (g h : seq (triple I B L)) :
      g =i h -> terms_ts g =i terms_ts h.
    Proof.
    move=> mem_eq t.
    suffices imp ts1 ts2:
      (forall (t : triple I B L), t \in ts1 -> t \in ts2) ->
        (forall (trm : term I B L), trm \in terms_ts ts1 -> trm \in terms_ts ts2).
      by apply /idP/idP; apply imp; move=> ?; rewrite -mem_eq.
    move=> /= {}mem_eq {}t; rewrite /terms_ts !mem_undup.
    move=> /flatten_mapP /=[t' t'ing tinterm].
    by apply /flatten_mapP=> /=; exists t'=> //; apply mem_eq.
    Qed.

    Lemma mem_eq_bnodes_ts (g h : seq (triple I B L)) :
      g =i h -> bnodes_ts g =i bnodes_ts h.
    Proof.
    move=> /mem_eq_terms_ts mem_eq b; rewrite /bnodes_ts !mem_undup.
    by rewrite !mem_filter mem_eq.
    Qed.

    Lemma mem_eq_get_bts (g h : seq (triple I B L)) :
      g =i h -> get_bts g =i get_bts h.
    Proof.
    move=> /mem_eq_bnodes_ts mem_eq b.
    by apply eq_mem_pmap.
    Qed.


    Lemma piso_sort (g: seq (triple I B L)) (mu : B -> B) :
      is_pre_iso_ts g (sort le_triple (relabeling_seq_triple mu g)) mu
      <-> is_pre_iso_ts g (relabeling_seq_triple mu g) mu.
    Proof.
    rewrite /is_pre_iso_ts/bnode_map_bij !uniq_get_bts/=.
    split=> H.
    + apply uniq_perm.
      - by rewrite (perm_uniq H) uniq_get_bts.
      - by rewrite uniq_get_bts.
      - move=> b; rewrite (perm_mem H).
        by apply mem_eq_get_bts=> b'; rewrite mem_sort.
    + apply uniq_perm.
      - by rewrite (perm_uniq H) uniq_get_bts.
      - by rewrite uniq_get_bts.
      - move=> b; rewrite (perm_mem H).
        by apply mem_eq_get_bts=> b'; rewrite mem_sort.
    Qed.

    Lemma uniq_map_pre_iso (mu : B -> B) (ts : seq (triple I B L)) :
      uniq (map mu (get_bts ts)) ->
        is_pre_iso_ts ts (relabeling_seq_triple mu ts) mu.
    Proof.
    move=> umu; rewrite /is_pre_iso_ts/bnode_map_bij !uniq_get_bts /=.
    apply perm_eq_bts_relabel_inj_in; last by apply perm_refl.
    by apply /in_map_injP=> //; apply uniq_get_bts.
    Qed.


    Lemma piso_funof (g : seq (triple I B L)) (hm: hash_map) :
      bnodes_hm hm =i get_bts g ->
        is_fine (gen_partition hm) ->
          is_pre_iso_ts g (relabeling_seq_triple (fun_of_hash_map hm) g) (fun_of_hash_map hm).
    Proof.
    by move=> mem_eq fine; apply uniq_map_pre_iso; apply uniq_get_bts_is_fine.
    Qed.

    Lemma init_hash_nil : init_hash [::] = [::].
    Proof.
    move: (good_init [::]).
    case: (init_hash [::]) ; first by [].
    move=> [b n] l; rewrite /get_bts/==> contr.
    have := in_nil b.
    by rewrite -contr in_cons eqxx.
    Qed.

    Lemma color_nil_nil : color [::] [::] = [::].
    Proof.
    move: (color_good_hm [::] [::]).
    rewrite /get_bts/=.
    have /(_ B) H : [::] =i [::] by move=> b.
    move=> /(_ H){H}.
    case: (color [::] [::]) ; first by [].
    move=> [b n] l contr.
    have := in_nil b.
    by rewrite -contr in_cons eqxx.
    Qed.

    Lemma template_nil_nil : template [::] = [::].
    Proof.
    rewrite /template/=; case: ifP; first by [].
    rewrite init_hash_nil. rewrite color_nil_nil.
    by autorewrite with gen_partition.
    Qed.


    Lemma foldl_default (gs : seq (seq (triple I B L))) (x0 x1: seq (triple I B L)):
        foldl choose_graph x0 gs = x1 ->
        (x0 == x1) = false ->
        forall (x2 : seq (triple I B L)),
          cmp x2 x0 ->
          foldl choose_graph x0 gs = foldl choose_graph x2 gs.
    Proof.
    elim: gs=> [/=->| hd tl IHtl] /=; first by rewrite eqxx.
    rewrite {2 4 6}/choose_graph.
    case_eq (x0 == hd); first by move=> /eqP <-; rewrite cmp_refl=> H F x2 ->.
    case: ifP.
    + by move=> cmp_x0hd neq_x0hd H F x2 cmp_x2x0; rewrite (cmp_trans cmp_x2x0 cmp_x0hd).
    move=> cmp_x0hdPn neq_x0hd foldl_eq neq_x0x1 x2 cmp_x2x0.
    case: ifP => [cmp_x2hd|cmp_x2hdPn]; last by apply IHtl.
    apply IHtl=> //.
    by move: (cmp_total hd x0); rewrite cmp_x0hdPn orbF=> ->.
    Qed.

    Lemma foldl_can_in_choose (l : seq (seq (triple I B L))) (x : seq (triple I B L)):
      (forall y : seq (triple I B L), y \in l -> cmp x y) ->
        foldl choose_graph x l = x -> (l == [::]) || (x \in l).
    Proof.
    elim: l x=> [//| hd t IHt] x cmp_in.
    rewrite /=; rewrite /choose_graph cmp_in; last by rewrite in_cons eqxx.
    suffices cmp_inW : forall y : seq (triple I B L), y \in t -> cmp x y.
      case_eq (hd == x); first by move=> /eqP ->; rewrite in_cons eqxx.
      move=> neq_hdx eq_fold.
      have cmpd : cmp x hd by apply cmp_in; rewrite in_cons eqxx.
      move: (distinguish_choice_default t hd)=> [].
      by move=> eqH; rewrite eqH in eq_fold; rewrite eq_fold eqxx // in neq_hdx.
      by rewrite eq_fold in_cons=> ->; rewrite orbT.
    by move=> y yin; apply cmp_in; rewrite in_cons yin orbT.
    Qed.

    (* Hypothesis cmp_can : *)
    (*   forall (hm : hash_map) (g y : seq (triple I B L)), *)
    (*     y \in [seq canonicalize g hm i | i <- choose_part hm] -> cmp can y. *)

    Hypothesis choose_from_not_fine :
      forall (hm : hash_map),
        ~~ is_fine (gen_partition hm) -> choose_part hm == [::] = false.

    Lemma nil_is_nil (g : seq (triple I B L)) (hm : hash_map):
      bnodes_hm hm =i get_bts g ->
      ~~ is_fine (gen_partition hm) ->
      (* ~~ is_fine (gen_partition (color g (init_hash g))) -> *)
      (* distinguish g (color g (init_hash g)) = can -> g = can. *)
      distinguish g hm = can -> g = can.
    Proof.
    (* set hm := (color g (init_hash g)). *)
    have : M hm < S (M hm) by apply ltnSn.
    (* have : bnodes_hm hm =i get_bts g by apply color_good_hm; apply good_init. *)
    move: hm (M hm).+1.
    (* move: hm (M hm). *)
    move=> hm n; move: n hm=> n.
    elim: n => [//| n IHn hm measure mem_eq_bhm neq_fine].
    rewrite distinguish_fold_map.
    move=> /(foldl_can_in_choose _ _)/orP[]; first by move=> ?; rewrite can_extremum //.
    + by rewrite map_nil_is_nil choose_from_not_fine.
    rewrite /canonicalize; move=> /mapP[/= b bin].
    case: ifP=> [_|].
    + rewrite -{1}sort_can=> /rdf_leP.
      rewrite can_nil perm_sym.
      by move=> /perm_nilP/eqP; rewrite map_nil_is_nil=> /eqP->.
    + move=> H /eqP; rewrite eq_sym=> /eqP.
      apply IHn=> //; last by rewrite H.
      + apply: Order.POrderTheory.le_lt_trans (color_refineP _ _) _.
        by apply: Order.POrderTheory.lt_le_trans (markP _ _ _) measure.
      + by apply color_refine_good_hm; apply good_mark=> //; apply in_part_in_bnodes.
    Qed.
    (* prove this *)

    Lemma distinguish_piso (g : seq (triple I B L)) (ug: uniq g):
      ~~ is_fine (gen_partition (color g (init_hash g))) ->
        exists mu : B -> B,
          distinguish g (color g (init_hash g)) = sort le_triple (relabeling_seq_triple mu g)
          /\ is_pre_iso_ts g (distinguish g (color g (init_hash g))) mu.
    Proof.
    set hm := (color g (init_hash g)).
    have : M hm < S (M hm) by apply ltnSn.
    have : bnodes_hm hm =i get_bts g by apply color_good_hm; apply good_init.
    move: hm (M hm).+1.
    move=> hm n; move: n hm=> n.
    elim: n => [//| n IHn hm' ghm hmM] finePn.
    move: (distinguish_choice g hm')=> /=[].
    + move=> H; rewrite H; move/(nil_is_nil g _ ghm finePn) : H ->.
      exists id; split; first by rewrite relabeling_seq_triple_id sort_can.
      rewrite /is_pre_iso_ts /= /bnode_map_bij.
      by rewrite (uniq_get_bts _) /= map_id perm_refl.
    + move=> /mapP/=[bn inp ->].
      case_eq  (is_fine (gen_partition (color_refine g (mark bn.1 hm'))))=> H.
      - exists (fun_of_hash_map (color_refine g (mark bn.1 hm'))).
        rewrite /canonicalize; split=> //; rewrite H //.
        apply piso_sort; apply piso_funof; last by apply H.
        apply color_refine_good_hm; apply good_mark=> //.
        by apply in_part_in_bnodes.
      - rewrite /canonicalize H; apply IHn=> //; last by rewrite H.
        apply color_refine_good_hm; apply good_mark=> //.
        by apply in_part_in_bnodes.
      eapply Order.POrderTheory.le_lt_trans; first by apply color_refineP.
      by apply (Order.POrderTheory.lt_le_trans (markP _ _ inp) hmM).
    Qed.

    Lemma preiso_out_template (g : seq (triple I B L)) (ug : uniq g) :
      exists mu, (template g) = sort le_triple (relabeling_seq_triple mu g)
                 /\ is_pre_iso_ts g (template g) mu.
    Proof.
    move/eqP : (eq_refl (template g)).
    rewrite {2}/template.
    case: ifP=> is_fine ->.
    exists (fun_of_hash_map (color g (init_hash g))); split=> //.
    + apply piso_sort; apply piso_funof=> //.
      by apply color_good_hm; apply good_init.
    by apply distinguish_piso=> //; rewrite is_fine.
    Qed.

    Lemma eiso_sort (g: seq (triple I B L)) (mu : B -> B) :
      is_effective_iso_ts g (relabeling_seq_triple mu g) mu ->
      is_effective_iso_ts g (sort le_triple (relabeling_seq_triple mu g)) mu.
    Proof.
    move=> /and3P/= [piso urel peq].
    apply /and3P; split=> //; first by apply piso_sort.
    apply uniq_perm=> //; first by rewrite sort_uniq.
    by move=> b; rewrite mem_sort.
    Qed.

    Lemma eiso_out_template (g : seq (triple I B L)) (ug : uniq g) :
      effective_iso_ts g (template g).
    Proof.
    rewrite /iso_ts.
    move: (uniq_template g ug).
    suffices [mu  [-> piso utg]]:
      exists mu, (template g) = sort le_triple (relabeling_seq_triple mu g)
                 /\ is_pre_iso_ts g (template g) mu.
      rewrite sort_uniq in utg.
      exists mu; apply eiso_sort.
      have {}piso : is_pre_iso_ts g (relabeling_seq_triple mu g) mu by apply piso_sort.
      by move : (ts_pre_iso_effective_iso utg piso)=> eiso //.
    by apply preiso_out_template.
    Qed.

    Hypothesis iso_color_fine :
      forall (g h : seq (triple I B L)),
        uniq g -> uniq h ->
          effective_iso_ts g h ->
            is_fine (gen_partition (color g (init_hash g)))
            = is_fine (gen_partition (color h (init_hash h))).

    (* Hypothesis distinguish_complete : *)
    (*   forall (g h : seq (triple I B L)), *)
    (*     uniq g -> uniq h -> *)
    (*       effective_iso_ts g h -> *)
    (*         is_fine (gen_partition (color g (init_hash g))) = false -> *)
    (*           distinguish g (color g (init_hash g)) =i distinguish h (color h (init_hash h)). *)

    Hypothesis eiso_mem_eq_canonicalize :
      forall (g h : seq (triple I B L)) (ug: uniq g) (uh: uniq h),
        effective_iso_ts g h ->
          is_fine (gen_partition (color g (init_hash g))) = false ->
            map (canonicalize g (color g (init_hash g))) (choose_part (color g (init_hash g)))
            =i map (canonicalize h (color h (init_hash h))) (choose_part (color h (init_hash h))).

    Lemma eiso_correct_complete (g h : seq (triple I B L)) (ug: uniq g) (uh: uniq h) :
      effective_iso_ts g h <-> (template g) == (template h).
    Proof.
    split; last first.
    + move=> /eqP eqmgmh.
      have := eiso_out_template g ug.
      rewrite eqmgmh=> mgh.
      have /(effective_iso_ts_sym uh) hmh := eiso_out_template h uh.
      by apply: (effective_iso_ts_trans mgh hmh).
    rewrite /template=> eiso.
    rewrite -(iso_color_fine _ _ eiso) //.
    case: ifP=> [fineP|finePn].
    + apply /eqP/rdf_leP.
      apply uniq_perm.
      - by apply uniq_label_is_fine=> //; apply color_good_hm; apply good_init.
      - rewrite (iso_color_fine _ _ eiso) // in fineP.
        by apply uniq_label_is_fine=> //; apply color_good_hm; apply good_init.
        by apply iso_color_fine_can.
    + rewrite !distinguish_fold_map /distinguish_fold.
      set cang := (map _ (choose_part (color g (init_hash g)))).
      set canh := (map _ (choose_part (color h (init_hash h)))).
      suffices mem_eq : cang =i canh.
        by rewrite !foldl_idx (eq_big_idem _ _ choose_graph_idem mem_eq) eqxx.
      by apply eiso_mem_eq_canonicalize.
    Qed.

    Lemma eiso_correct_complete' (g h : seq (triple I B L)) (ug: uniq g) (uh: uniq h) :
      perm_eq (template g) (template h) <-> effective_iso_ts g h.
    Proof.
    split.
    + move=> eqmgmh.
    have gmg := eiso_out_template g ug.
    suffices mgmh : effective_iso_ts (template g) (template h).
      have /(effective_iso_ts_sym uh) hmh := eiso_out_template h uh.
      apply: (effective_iso_ts_trans gmg _).
      by apply: (effective_iso_ts_trans mgmh hmh).
    have [mu [eiso _]]:= eqiso_ts (uniq_template _ ug) eqmgmh.
    by exists mu.
    rewrite /template=> eiso.
    rewrite -(iso_color_fine _ _ eiso) //.
    case: ifP=> [fineP|finePn].
    + apply /rdf_leP.
      rewrite (sorted_sort (@le_triple_trans _ _ _ _)); last by rewrite sort_sorted.
      rewrite (@sorted_sort _ _ (@le_triple_trans _ _ _ _) (sort le_triple _)); last by rewrite sort_sorted.
    + apply /rdf_leP.
      apply uniq_perm.
    - by apply uniq_label_is_fine=> //; apply color_good_hm; apply good_init.
    - rewrite (iso_color_fine _ _ eiso) // in fineP.
      by apply uniq_label_is_fine=> //; apply color_good_hm; apply good_init.
      by apply iso_color_fine_can.
      + rewrite !distinguish_fold_map /distinguish_fold.
        set cang := (map _ (choose_part (color g (init_hash g)))).
        set canh := (map _ (choose_part (color h (init_hash h)))).
        suffices mem_eq : cang =i canh.
          by rewrite !foldl_idx (eq_big_idem _ _ choose_graph_idem mem_eq) perm_refl.
        by apply eiso_mem_eq_canonicalize.
    Qed.

    Definition template_rdf (g : rdf_graph I B L) :=
      mkRdfGraph (uniq_template _ (ugraph g)).

    Lemma template_isocan : (@effective_isocanonical_mapping I B L template_rdf).
    Proof.
    split; first by move=> [g ug]; apply eiso_out_template.
    by move=> [g ug] [h uh]; apply eiso_correct_complete'.
    Qed.

  End Distinguish.

End Template.
Section kmap_template.
  Variable disp : unit.
  (* TODO : check that order is needed, since below comes a comparison comp on graphs *)
  Variable I B L : orderType disp.
  Notation le_triple := (@le_triple disp I B L).


  (* Enumeration of b-nodes *)
  Hypothesis nat_inj : nat -> B.
  Hypothesis nat_inj_ : injective nat_inj.
  Definition template_isocan_ := @template_isocan disp I B L nat_inj nat_inj_
    (@le_st disp I B L) (@le_st_anti disp I B L) (@le_st_total disp I B L) (@le_st_trans disp I B L)
    nil isT erefl erefl (@nil_minimum disp I B L).

  Check template_isocan_.

  Definition init_hash_kmap (ts : seq (triple I B L)) : hash_map B :=
    let bs := get_bts ts in
    zip bs (nseq (size bs) 0).

  Lemma zip_proj1 (T S : Type) (s1 : seq T) (s2 : seq S) :
    size s1 = size s2 ->
    map fst (zip s1 s2) = s1.
  Proof.
  elim: s1 s2=> [| hd tl IHtl] s2; first by case: s2.
  case: s2=> [//|hd2 tl2] /=[]eq_size.
  by congr cons; apply IHtl.
  Qed.

  Lemma good_init_kmap (g : seq (triple I B L)) : bnodes_hm (init_hash_kmap g) =i get_bts g.
  Proof. by move=> x; rewrite /init_hash_kmap/bnodes_hm zip_proj1 // size_nseq. Qed.

  Definition choose_part_kmap (hm : hash_map B) : part B :=
    let P := gen_partition (hm) in
    let pred := predC (@is_trivial disp B) in
    if has pred P then
      nth [::] P (find pred P)
    else [::].

  Lemma in_part_in_bnodes_kmap (bn : B * nat) (hm : hash_map B):
    bn \in choose_part_kmap hm -> bn \in hm.
  Proof.
  rewrite /choose_part_kmap/=.
  case: ifP=> [|//].
  rewrite has_find=> size_find.
  suffices /partition_memP : nth [::] (gen_partition hm) (find (predC (is_trivial (B:=B))) (gen_partition hm)) \in (gen_partition hm).
    by move=> /mem_subseq eq bn_in; rewrite eq.
  by apply mem_nth.
  Qed.

  Definition color_kmap : seq (triple I B L) -> hash_map B -> hash_map B := fun _ hm=> hm.
  Definition color_refine_kmap : seq (triple I B L) -> hash_map B -> hash_map B := fun _ hm=> hm.
  Lemma color_good_hm_kmap (g : seq (triple I B L)) (hm : hash_map B):
    bnodes_hm hm =i get_bts g -> bnodes_hm (color_kmap g hm) =i get_bts g.
  Proof. by []. Qed.

  Lemma color_refine_good_hm_kmap (g : seq (triple I B L)) (hm : hash_map B) :
    bnodes_hm hm =i get_bts g -> bnodes_hm (color_refine_kmap g hm) =i get_bts g.
  Proof. by []. Qed.

  Fixpoint mark_hash_kmap (b : B) (n : nat) (hm : hash_map B) :=
    match hm with
    | nil => nil
    | bn :: bns =>
        if eq_bnode B b bn
        then (b,n)::bns
        else bn:: mark_hash_kmap b n bns
    end.

  Definition mark_kmap (b : B) (hm : hash_map B) :=
    mark_hash_kmap b (count (@is_trivial disp B) (gen_partition hm)).+1 hm.

  Lemma mark_hash_kmap_bnodes (hm : hash_map B) :
    forall (b : B) (n : nat),
    bnodes_hm (mark_hash_kmap b n hm) = bnodes_hm hm.
  Proof.
  elim: hm => [//|hd tl IHtl] b n /=.
  case: ifP.
  + by rewrite /eq_bnode/pred_eq/==> /eqP ->.
  + by move=> _; rewrite /= IHtl.
  Qed.

  Lemma good_mark_kmap (g : seq (triple I B L)) (hm : hash_map B):
    bnodes_hm hm =i get_bts g ->
      forall b : B, b \in bnodes_hm hm -> bnodes_hm (mark_kmap b hm) =i get_bts g.
  Proof.
  move=> mem_eq b bin.
  by rewrite mark_hash_kmap_bnodes; apply mem_eq.
  Qed.

  Definition M_kmap (hm :hash_map B) : nat :=
    count (@is_trivial disp B) (gen_partition hm).


  Definition template_isocan__ := @template_isocan_
                                    init_hash_kmap good_init_kmap choose_part_kmap in_part_in_bnodes_kmap
                                    color_kmap color_refine_kmap color_good_hm_kmap color_refine_good_hm_kmap
                                    mark_kmap good_mark_kmap M_kmap.

  Check template_isocan__.

  Lemma markP_kmap (bn : B * nat) (hm : hash_map B):
    bn \in choose_part_kmap hm -> M_kmap (mark_kmap bn.1 hm) < M_kmap hm.
  Proof.
  Admitted.

  Lemma color_refineP_kmap (g : seq (triple I B L)) (hm : hash_map B) : M_kmap (color_refine_kmap g hm) <= M_kmap hm.
  Proof. by []. Qed.

  Lemma iso_color_fine_can_kmap (g h : seq (triple I B L)) :
    uniq g ->
    uniq h ->
    effective_iso_ts g h ->
    relabeling_seq_triple (fun_of_hash_map nat_inj (color_kmap g (init_hash_kmap g))) g
    =i relabeling_seq_triple (fun_of_hash_map nat_inj (color_kmap h (init_hash_kmap h))) h.
  Proof.
  move=> ug uh [mu /and3P[/and3P[_ _ piso] urel peq]] /= t.
  rewrite /color_kmap.
  have /eq_mem_map/= peq_m := perm_mem peq.
  rewrite -peq_m relabeling_triple_map_comp.
  apply relabeling_ext_in=> /= t' t'ing.
  have := map_f (relabeling_triple mu) t'ing.
  rewrite (perm_mem peq)=> mut'inh.
  apply: eq_in_bs_ing; last by apply t'ing.
  move=> b bin /=.
  have mub_in := map_f mu bin.
  rewrite (perm_mem piso) in mub_in.
  rewrite /fun_of_hash_map.
  rewrite !bnodes_hm_has_eq_bnodes; rewrite ?good_init_kmap //.
  congr nat_inj; rewrite /init_hash_kmap !map_snd_zip_size ?size_nseq //.
  by rewrite !nth_nseq; case: ifP; case: ifP.
  Qed.

  Lemma choose_part_not_nil_kmap (hm : hash_map B): ~~ is_fine (gen_partition hm) -> (choose_part_kmap hm == [::]) = false.
  Proof.
  move=> finePn; apply: negPf; move: finePn; apply contraNN.
  rewrite /choose_part_kmap.
  case: ifP.
  + rewrite has_find=> triv_in /eqP nth_eq.
    suffices : [::] \in gen_partition hm.
      by move=> /part_size.
    apply /(nthP [::])=> /=.
    by exists (find (predC (is_trivial (B:=B))) (gen_partition hm)).
  move=> all_triv.
  have : ~~ (has (predC (is_trivial (B:=B))) (gen_partition hm)) by rewrite all_triv.
  by rewrite has_predC; rewrite negbK.
  Qed.

  Lemma same_is_fine (g h : seq (triple I B L)) :
    uniq g ->
      uniq h ->
        effective_iso_ts g h ->
          is_fine (gen_partition (color_kmap g (init_hash_kmap g)))
          = is_fine (gen_partition (color_kmap h (init_hash_kmap h))).
  Proof.
  move=> ug uh [mu /and3P[piso urel peq]].
  rewrite /color_kmap/init_hash_kmap.
  apply /idP/idP.
  (* rewrite /is_fine. *)
  apply contraTT.
  move=> /allPn/=[p pin not_triv].
  apply /allPn=> /=.
  exists (zip (map (mu \o fst) p) (map snd p)).
  admit.
  rewrite /is_trivial.
  by rewrite size_zip !size_map minn_refl not_triv.
  Admitted.

  Check template_isocan__.

  Check template_rdf.
  Definition template_rdf_kmap_ t := @template_rdf disp I B L nat_inj nat_inj_
      (@le_st disp I B L) (@le_st_anti disp I B L) (@le_st_total disp I B L) (@le_st_trans disp I B L)
      nil isT erefl erefl (@nil_minimum disp I B L) init_hash_kmap good_init_kmap
      choose_part_kmap in_part_in_bnodes_kmap
      color_kmap color_refine_kmap color_good_hm_kmap color_refine_good_hm_kmap
      mark_kmap good_mark_kmap M_kmap
      t color_refineP_kmap iso_color_fine_can_kmap.

  Check template_rdf_kmap_.

  Goal (forall (p : (forall (bn : B * nat) (hm : hash_map B), bn \in choose_part_kmap hm -> M_kmap (mark_kmap bn.1 hm) < M_kmap hm)),
       effective_isocanonical_mapping (template_rdf_kmap_ p)).
    move=> p. apply template_isocan__. apply choose_part_not_nil_kmap. apply same_is_fine.
    move=> g h ug uh [mu /and3P[piso urel peq]] finePn.
    move=> /= cand.
    (* rewrite /color_kmap/color_refine_kmap /=. *)
    rewrite /canonicalize.
    apply /idP/idP.
    move=> /mapP[/= bn bnin].
    case: ifP.
 Admitted.



End kmap_template.














