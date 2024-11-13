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

  Lemma part_all_eq_hash_mem (hd : B * nat) (tl : seq (B * nat)) (hm : hash_map) :
  hd \in tl -> (tl \in gen_partition hm) -> all (eq_hash hd.2) (tl).
  Proof.
  funelim (gen_partition hm)=> [//|].
  rewrite in_cons=> in_tl /orP[].
  + move=> /eqP eq.
    suffices eqhash : bn.2 = hd.2.
      by rewrite eq eqhash; apply filter_all.
    by move: in_tl; rewrite eq mem_filter /eq_hash/pred_eq=> /andP[/eqP->].
  by move=> inP; apply H=> //.
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
  move: allPn; case: hm measure => [//|c l].
  autorewrite with gen_partition.
  rewrite in_cons=> measure allPn /orP[].
  + rewrite /=. rewrite eq_hash_refl=> /eqP[-> _].
    by move: allPn=> /=/andP[]; rewrite eq_hash_sym; case: (eq_hash c.2 a).
  apply IHn; last by rewrite /=eq_hash_refl/=; apply (leq_ltn_trans (size_filter_le _ l) measure).
  move: allPn; set hs := c :: l; rewrite all_filter=> allPn.
  apply /allP=> /=.
  move=> bn bnin; apply /implyP=> _.
  by have /=-> := in_all bnin allPn.
  Qed.

  Lemma part_filter (hd : B * nat) (tl : seq (B * nat)) (hm : hash_map) :
    (hd :: tl \in gen_partition hm) -> hd :: tl = (partitionate hd.2 hm).1.
  Proof.
  have : size hm < S (size hm) by apply ltnSn.
  move: hm (size hm).+1.
  move=> hm n; move: n hm=> n.
  elim: n hd => [//| n' IHn hd hm] measure.
  case: hm measure => [//|a l]/=.
  autorewrite with gen_partition; rewrite in_cons=> measure /orP[]; rewrite /= eq_hash_refl/=.
  + by move=> /eqP[-> ->]; rewrite eq_hash_refl.
  move => pin.
  have neq_hash := (gen_partition_filter _ _ _ _ pin).
  rewrite neq_hash (IHn _ _ _ pin) /=; last by apply (leq_ltn_trans (size_filter_le _ _) measure).
  + rewrite -filter_predI; apply eq_filter=> bn /=.
    move: neq_hash; rewrite /eq_hash/pred_eq/negb eq_sym.
    by case_eq (hd.2 == bn.2)=> // /eqP -> ->.
  Qed.

  Lemma partP (hm : hash_map):
    forall (p : part), p \in (gen_partition hm) ->
      exists (bn : B * nat), p = (partitionate bn.2 hm).1.
  Proof.
  move=> p pin; have /part_size := pin; move: pin.
  by case: p=> [//|hd tl] /part_filter ->; exists hd.
  Qed.

  Lemma partition_memP (hm : hash_map) :
    forall (p: part), p \in (gen_partition hm) -> subseq p hm.
  Proof.
  by move=> p /partP[bn ->]; apply filter_subseq.
  Qed.

  Lemma partP' (hm : hash_map):
    forall (p : part), p \in (gen_partition hm) ->
      exists (bn : B * nat), bn \in p /\ p = (partitionate bn.2 hm).1.
  Proof.
  move=> p pin; have /part_size := pin; move: pin.
  case: p=> [//|hd tl] in_P.
  have /partition_memP in_hm := in_P.
  move/part_filter : in_P=> ->; exists hd; split=> [|//].
  rewrite mem_filter eq_hash_refl /=.
  by apply (mem_subseq in_hm); rewrite in_cons eqxx.
  Qed.

  Lemma all_mem_hash (p : part) (n : nat):
    all (eq_hash n) p -> constant (map snd p).
  Proof.
  move=> all_eq_hash.
  apply /(constantP 0)=> /=.
  exists n; move: all_eq_hash.
  elim: p=> [//|hd tl IHtl].
  by rewrite /=/eq_hash/pred_eq=> /andP[/eqP <- /IHtl <-].
  Qed.

  Lemma mem_constant (T : eqType) (t1 t2: T) (s : seq T):
    t1 \in s -> t2 \in s -> constant s -> t1 = t2.
  Proof.
  move=> t1in t2in /(constantP t1)[]x eq; move: t1in t2in.
  by rewrite eq !mem_nseq=> /andP[_ /eqP ->] /andP[_ /eqP ->].
  Qed.

  Lemma mem_partP (hm : hash_map):
    forall (bn : B * nat) (p : part),
      bn \in p -> p \in (gen_partition hm) ->
        p = (partitionate bn.2 hm).1.
  Proof.
  move=> bn p bnin pin.
  have pin' := pin.
  move/partP' : pin'=> [/= bn' [bn'_in ->]].
  suffices -> : bn.2 = bn'.2 by [].
  have /all_mem_hash cst_p2 := part_all_eq_hash_mem _ _ _ bnin pin.
  suffices /andP[in_cns1 in_cns2]: (bn.2 \in map snd p) && (bn'.2 \in map snd p).
    by apply (mem_constant _ _ _ _ in_cns1 in_cns2 cst_p2).
  apply /andP; split.
  + move: bnin; rewrite {1}(hm_zip p).
    by case: bn=> b n /in_zip/andP[_ ->].
  + move: bn'_in; rewrite {1}(hm_zip p).
    by case: bn'=> b n /in_zip/andP[_ ->].
  Qed.

  Definition is_trivial (p : part) : bool := size p == 1.
  Definition is_fine (P : partition) : bool := all is_trivial P.
  Definition hashes_hm (hm : hash_map): seq nat :=
    map snd hm.

  Definition mult1 {T : eqType} (s : seq T) (t : T) :=
    count_mem t s == 1.

  Definition num_uniq_hash (hm : hash_map) :=
    count (mult1 (hashes_hm hm)) (hashes_hm hm).

  Lemma hashes_hm_cat (hm1 hm2 : hash_map):
    hashes_hm (hm1 ++ hm2) = hashes_hm hm1 ++ hashes_hm hm2.
  Proof. exact: map_cat. Qed.

  Lemma num_uniq_hash_cat (hm1 hm2 hm3 : hash_map) :
    perm_eq (hashes_hm hm2) (hashes_hm hm3) ->
    num_uniq_hash (hm1 ++ hm2) = num_uniq_hash (hm1 ++ hm3).
  Proof.
  elim: hm1=> [/=/permP eq| hd tl IHtl]; rewrite /num_uniq_hash.
  + by rewrite eq; apply eq_in_count=> /= h hin; rewrite /mult1 eq.
  rewrite /num_uniq_hash (hashes_hm_cat (hd::tl) hm2) (hashes_hm_cat (hd::tl) hm3) !count_cat.
  set s1:= hashes_hm (hd::tl).
  set s2:= hashes_hm hm2.
  set s3:= hashes_hm hm3.
  move=> /permP peq.
  congr addn; last first.
  + by rewrite /mult1/=; rewrite peq; apply eq_in_count=> /= s sin; rewrite !count_cat peq.
  apply eq_in_count=> /= n nin.
  rewrite /mult1 /=.
  set htl := hashes_hm tl.
  rewrite !count_cat.
  set m := hd.2 == n.
  set o := (count_mem n htl).
  by rewrite peq.
  Qed.

  Lemma num_uniq_hash_catC (hm1 hm2 : hash_map):
    num_uniq_hash (hm1 ++ hm2) = num_uniq_hash (hm2 ++ hm1).
  Proof.
  rewrite /num_uniq_hash.
  set s1 := hashes_hm (hm1 ++ hm2).
  set s2 := hashes_hm (hm2 ++ hm1).
  suffices /permP peq : perm_eq s1 s2.
    rewrite peq; apply eq_in_count.
    by move=> /= h hin; rewrite /mult1 peq.
  rewrite /s1 /s2 !hashes_hm_cat.
  by apply /permPl; apply perm_catC.
  Qed.

  Definition distinguished (hm : hash_map) : nat :=
    count is_trivial (gen_partition hm).

  Lemma size_gen_partition (hm : hash_map) : size (gen_partition hm) <= size hm.
  Proof.
  have : size hm < S (size hm) by apply ltnSn.
  move: hm (size hm).+1.
  move=> hm n; move: n hm=> n.
  elim: n => [//| n' IHn [//|hd tl]] measure.
  autorewrite with gen_partition.
  rewrite /= eq_hash_refl .
  suffices : (size (gen_partition (partitionate hd.2 (hd :: tl)).2)) <= size (filter (negb \o eq_hash hd.2) (hd::tl)).
    rewrite /= eq_hash_refl /==> le_part.
    suffices H: (size (gen_partition [seq x <- tl | (negb \o eq_hash hd.2) x])) <= (size tl).
      by apply H.
    by apply (leq_trans le_part (size_filter_le _ _)).
  rewrite /= eq_hash_refl /=; apply IHn.
  have {}measure : size tl < n'. by apply measure.
  by apply: (leq_ltn_trans (size_filter_le _ _) measure).
  Qed.

  Lemma proj1_set_nth_prod (hm : hash_map) (b0 : B) (n0 i: nat):
    i < size hm ->
    hashes_hm (set_nth (b0, n0) hm i (b0, n0)) = set_nth n0 (hashes_hm hm) i n0.
  Proof.
  rewrite !set_nthE size_map -nat_coq_nat=> ->.
  by rewrite hashes_hm_cat {1 2}/hashes_hm map_take /= map_drop.
  Qed.

  Lemma partitionate_sndE (hd : B * nat) (tl : seq (B * nat)):
    (partitionate hd.2 (hd :: tl)).2 = [seq x <- hd :: tl | (negb \o eq_hash hd.2) x].
  Proof. by []. Qed.

  Lemma count_mult (hm : hash_map) (n : nat):
    count (eq_hash n) hm = count_mem n (hashes_hm hm).
  Proof.
  elim: hm=> [//|hd tl IHtl] /=.
  rewrite /eq_hash/pred_eq eq_sym.
  by congr addn; apply IHtl.
  Qed.

  Lemma mult1_filter (n m : nat) (s: seq nat):
    n != m -> mult1 s m = mult1 (filter (predC1 n) s) m.
  Proof. by rewrite /mult1=> /(@count_mem_filter _ _ s) ->. Qed.

  Lemma count_mult1_opt (hd : B * nat) (tl : seq (B * nat)):
    let ps := (partitionate hd.2 (hd :: tl)).2 : seq (B * nat) in
    count (mult1 (hashes_hm ps)) (hashes_hm ps) = count (mult1 (hashes_hm (hd :: tl))) (hashes_hm tl).
  Proof.
  rewrite partitionate_sndE.
  move=> ps; set fhs := hashes_hm _.
  have /permEl := perm_filterC (negb \o eq_hash hd.2) tl.
  move=> /(perm_map snd)/permP <-.
  rewrite map_cat count_cat.
  set s_neq_hd := map _ _; set s_eq_hd := map _ _.
  have -> : fhs = s_neq_hd by rewrite /fhs/hashes_hm/ps/= eq_hash_refl/=.
  move=> {ps fhs}.
  suffices ->: count (mult1 (hashes_hm (hd :: tl))) s_eq_hd = 0.
    rewrite addn0; apply eq_in_count=>/= h /mapP[/= [b n]].
    rewrite mem_filter=> /andP[neq_hd in_tl] ->.
    move: neq_hd; rewrite /= /eq_hash/pred_eq/=.
    move=> /(mult1_filter _ _ (hd.2:: hashes_hm tl)) ->.
    suffices -> :s_neq_hd = [seq x <- hd.2 :: hashes_hm tl | predC1 hd.2 x] by [].
    rewrite {}/s_neq_hd=> {s_eq_hd in_tl}.
    elim: tl=> [/=|a tl' IHtl2]; first by case: ifP; move=> /negPf; rewrite eqxx.
    rewrite /= {4}/negb eqxx {4}/negb /eq_hash/pred_eq.
    case_eq (a.2 == hd.2); rewrite eq_sym /==> -> /=.
    by rewrite IHtl2; rewrite /predC1/= eqxx /=.
    by congr cons; rewrite IHtl2 /= eqxx /=.
  apply /eqP; rewrite -allPn_count.
  apply /allP=> /= shd /mapP[/= bn].
  rewrite mem_filter=> /andP[eq_hd mem_tl] ->.
  rewrite /mult1=> {s_neq_hd s_eq_hd shd}.
  move: eq_hd.
  rewrite /predC/= negbK/eq_hash/pred_eq=> ->.
  rewrite add1n /negb /=.
  move/perm_to_rem : mem_tl=> /(perm_map snd)/permP->.
  by rewrite /= eqxx add1n; case: (count_mem _ _).
  Qed.

  Lemma num_triv_distinguished (hm : hash_map):
    distinguished hm = num_uniq_hash hm.
  Proof.
  rewrite /distinguished /num_uniq_hash.
  have : size hm < S (size hm) by apply ltnSn.
  move: hm (size hm).+1.
  move=> hm n; move: n hm=> n.
  elim: n => [//| n' IHn [//|hd tl]].
  autorewrite with gen_partition.
  move=> size_ltn.
  set p1 := (partitionate _ _).1.
  set ps := (partitionate _ _).2.
  set P := gen_partition _.
  set Pc := mult1 _.
  rewrite /=.
  congr addn; rewrite /Pc.
  + rewrite /is_trivial /p1 /= eq_hash_refl /=.
    by rewrite size_filter count_mult /mult1 /= eqxx add1n.
  suffices ps_size : size ps < n'.
     by rewrite IHn // count_mult1_opt.
  rewrite /ps partitionate_sndE.
  rewrite /= eq_hash_refl/=.
  apply: (leq_ltn_trans (size_filter_le _ _)).
  apply size_ltn.
  Qed.

  Lemma size_mem_filter_undup (T : eqType) (s : seq T) (t : T):
      t \in s -> size (undup s) = (size (undup (filter (negb \o (pred_eq t)) s))).+1.
    Proof.
    elim: s=> [//|hd tl IHtl].
    rewrite /= in_cons=> /orP[].
    + move=> /eqP H /=; rewrite H {1}/pred_eq eqxx /=.
      case: ifP; first by move=> x; rewrite IHtl H.
      move=> neqin /=; rewrite -filter_undup size_filter.
      suffices /eq_in_count -> : {in (undup tl), (negb \o pred_eq hd) =1 predT}.
        by congr S.
      move=> a /= a_in; rewrite /pred_eq.
      suffices : count_mem a (undup tl) != count_mem hd (undup tl).
        by move=> /neq_count_mem; rewrite /negb eq_sym.
      move: neqin; rewrite -mem_undup=> /count_memPn ->.
      move/count_mem_inP: a_in=> /=.
      by rewrite -lt0n.
    + move=> t_in; have /IHtl {}IHtl:= t_in.
      rewrite /pred_eq /= {1}/negb.
      case_eq (t == hd); first by move=> /eqP <-; rewrite t_in IHtl.
      rewrite /==> t_hd_neq.
      suffices -> : (hd \in tl = (hd \in [seq x <- tl | (negb \o [eta eq_op t]) x])).
        by case: ifP; rewrite /= ?IHtl //.
      by rewrite mem_filter /= /negb t_hd_neq.
    Qed.


    Lemma size_perm_gen_partition (hm p : hash_map):
      perm_eq (hashes_hm hm) (hashes_hm p) -> size (gen_partition hm) = size (gen_partition p).
    Proof.
    suffices rewr: forall (hm : hash_map), size (gen_partition hm) = size (undup (hashes_hm hm)).
      by rewrite !rewr=> /perm_mem/perm_undup/perm_size ->.
    move=> {p}hm.
    have : size hm < S (size hm) by apply ltnSn.
    move: hm (size hm).+1.
    move=> hm n; move: n hm=> n.
    elim: n => [//| n' IHn [//|hd tl]] /= measure.
      autorewrite with gen_partition=> /=; rewrite eq_hash_refl /=.
      case: ifP.
      + move=> /size_mem_filter_undup ->.
        congr S. rewrite IHn ?filter_map //.
        by apply: (leq_ltn_trans (size_filter_le _ _) measure).
      + move=> neq_in /=.
        have Hn : size [seq x <- tl | (negb \o eq_hash hd.2) x] < n'.
          by apply: (leq_ltn_trans (size_filter_le _ _) measure).
        rewrite IHn //; congr S; congr size; congr undup.
        elim: tl neq_in {measure Hn}=> [//|a tl' IHtl] /=.
        rewrite in_cons -[_ || _]negbK -[false]negbK=> /negb_inj; rewrite negb_or /=.
        move=> /andP[neqhda hdnin]; rewrite /eq_hash/pred_eq neqhda /= IHtl //.
        by move: hdnin; rewrite /negb; case: ifP.
    Qed.

    Lemma perm_hash_eq_fine (hm p : hash_map):
      perm_eq (hashes_hm hm) (hashes_hm p) -> is_fine (gen_partition hm) = is_fine (gen_partition p).
    Proof.
    move=> count_hashes.
    rewrite /is_fine.
    rewrite !all_count.
    suffices -> : count is_trivial (gen_partition hm) = count is_trivial (gen_partition p).
      by apply /idP/idP=> /eqP ->; apply /eqP; apply size_perm_gen_partition=> //; rewrite perm_sym.
    set c1 := count _ _.
    set c2 := count _ _.
    have -> : c1 = distinguished hm by [].
    have -> : c2 = distinguished p by [].
    rewrite !num_triv_distinguished /num_uniq_hash.
    rewrite -(permP count_hashes); apply eq_in_count; move=> h hin.
    by rewrite /mult1 -(permP count_hashes).
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

  (* comparison on graphs, morally an order relation. *)

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

  (* The blank nodes of a hash map *)
  Definition bnodes_hm (hm : hash_map): seq B := map fst hm.

  Arguments eq_hash {B} _ _.
  Arguments eq_bnode {B} _ _.

  Definition fun_of_hash_map (hm : hash_map) : B -> B :=
    fun b =>
      if has (eq_bnode b) hm then
        let the_label := nth O (map snd hm) (find (eq_bnode b) hm) in
        nat_inj the_label
      else
        b.

  Coercion fun_of_hash_map : hash_map >-> Funclass.

  (* blank nodes of g and blank nodes of hm are set equal *)
  Definition hash_map_for (g : seq (triple I B L)) (hm : hash_map) :=
    bnodes_hm hm =i get_bts g.

  (* passes the hash_map's keys under mu *)
  Definition map1 (mu : B -> B) (h : hash_map) : hash_map :=
    zip (map mu (map fst h)) (map snd h).

  Definition good_hash_map_for (g : seq (triple I B L)) (hm : hash_map) :=
    forall (mu : B -> B),
      {in get_bts g &, injective mu} ->
        {in get_bts g, ((map1 mu hm) \o mu) =1 hm}.

    (* forall (h : seq (triple I B L)) (mu : B -> B), *)
    (*   is_effective_iso_ts g h mu -> *)
    (*   perm_eq (relabeling_seq_triple hm g) (relabeling_seq_triple (map1 mu hm) h). *)

  (* Initial hash map from a graph *)
  Variable (init_hash : seq (triple I B L) -> hash_map).

  (* init_hash g has the same bnodes as the graph g *)
  (* TODO: use hash_map_for *)
  Hypothesis good_init :
    forall (g : seq (triple I B L)), bnodes_hm (init_hash g) =i get_bts g.

  Hypothesis color_init_inv : forall (g : seq (triple I B L)),
    good_hash_map_for g (init_hash g).

  (* Pick a part p from a failed attempt at computing a fine partition from the input hashmap hm. Expected:
     - (map fst p) is included in (map fst hm)
     - elements of p have the same hash
     - p is non empty and non singleton *)
  Variable choose_part : hash_map -> part.
  (* all nodes in choose_part hm lead to bnodes of hm. NOTE that the assumption does not prevent choose_part from duplicating elements. *)
  Variable choose_hash : hash_map -> nat.

  (* TODO : relate choose_part and choose_hash *)
  Hypothesis choose_part_order :
    forall (hm1 hm2 : hash_map),
      perm_eq (hashes_hm hm1) (hashes_hm hm2) ->
        perm_eq (choose_part hm1) (choose_part hm2).
  (* choose_hash hm1 = choose_hash hm2. *)

  Hypothesis in_part_in_bnodes' :
    forall (bn : B * nat) hm, bn \in choose_part hm -> bn \in hm.

  (* TODO : change into ... != [::] *)
  Hypothesis choose_from_not_fine :
    forall (hm : hash_map),
      ~~ is_fine (gen_partition hm) -> choose_part hm == [::] = false.

  Lemma in_part_in_bnodes (bn : B * nat) hm: bn \in choose_part hm -> bn.1 \in bnodes_hm hm.
  Proof.
  move/in_part_in_bnodes'; rewrite /bnodes_hm; rewrite {1}(hm_zip hm).
  by case: bn=> [b n] /in_zip/andP[->].
  Qed.

  (* update a hashmap from an input graph, without increasing the measure *)
  Variables (color color_refine : seq (triple I B L) -> hash_map -> hash_map).

  (* coloring a hashmap of a graph using the same graph does not change its bnodes
     TODO : Pick one of the versions, color_bnodes is stronger but may be not needed. *)
  (* TODO : use hash_map_for *)
  Hypothesis color_good_hm :
    forall (g : seq (triple I B L)) hm,
      bnodes_hm hm =i get_bts g -> bnodes_hm (color g hm) =i get_bts g.

  (* Hypothesis color_bnodes : forall (g : seq (triple I B L)) hm, bnodes_hm (color g hm) =i bnodes_hm hm. *)
  Hypothesis color_inv : forall (g : seq (triple I B L)) (hm : hash_map),
      good_hash_map_for g hm -> good_hash_map_for g (color g hm).


  (* Same for color_refine *)
  (* TODO : use hash_map_for *)
  Hypothesis color_refine_good_hm :
    forall (g : seq (triple I B L)) hm,
      bnodes_hm hm =i get_bts g -> bnodes_hm (color_refine g hm) =i get_bts g.

  Hypothesis color_refine_inv : forall (g : seq (triple I B L)) (hm : hash_map),
      good_hash_map_for g hm -> good_hash_map_for g (color_refine g hm).

  (* Spec of a good color function *)
  Hypothesis iso_color_fine :
      forall (g h : seq (triple I B L)),
        uniq g -> uniq h ->
          effective_iso_ts g h ->
            is_fine (gen_partition (color g (init_hash g)))
            = is_fine (gen_partition (color h (init_hash h))).


  (* Marks a bnode in a hashmap*)
  Variable (mark : B -> hash_map -> hash_map).
  (* Marking a hashmap with one of its bnodes does not change its bnodes (but only the hashes)*)
  (* TODO : use hash_map_for *)
  Hypothesis good_mark :
    forall (g : seq (triple I B L)) (hm : hash_map),
      bnodes_hm hm =i get_bts g ->
      forall b, b \in bnodes_hm hm -> bnodes_hm (mark b hm) =i get_bts g.

  Hypothesis mark_inv :
    forall (g : seq (triple I B L)) (hm : hash_map) (b : B),
      b \in (get_bts g) ->
        good_hash_map_for g hm ->
          good_hash_map_for g (mark b hm).


  (* TODO : to be simplified into
    Hypothesis good_mark : forall (hm : hash_map),
     forall b, b \in bnodes_hm hm -> bnodes_hm (mark b hm) =i bnodes_hm hm.
   *)

  (* Measure on hash_map*)
  Variable (M : hash_map -> nat).

  (* Mark decreases the measure *)
  Hypothesis markP :
    forall (bn : B * nat) (hm : hash_map),
      (* TODO: add this hypothesis *)
      ~~ is_fine (gen_partition hm) ->
      uniq (bnodes_hm hm) ->
      bn \in choose_part hm -> M (mark bn.1 hm) < M hm.
  (* color_refine does not increase the measure *)

  Hypothesis color_refineP :
    forall (g : seq (triple I B L)) (hm : hash_map),
      M (color_refine g hm) <= M hm.



  Hypothesis iso_color_fine_can :
    forall (g h : seq (triple I B L)),
      uniq g -> uniq h ->
      effective_iso_ts g h ->
         relabeling_seq_triple (color g (init_hash g)) g
      =i relabeling_seq_triple (color h (init_hash h)) h.

  Hypothesis color_post_relabeling : forall (g : seq (triple I B L)) (mu : B -> B) (hm : hash_map),
    {in (get_bts g)&, injective mu} ->
      {in (bnodes_hm hm)&, injective mu} ->
        perm_eq (color (relabeling_seq_triple mu g) (map1 mu hm)) (map1 mu (color g hm)).
  Hypothesis color_perm_graph : forall (g h : seq (triple I B L)) (hm : hash_map),
      perm_eq g h -> perm_eq (color g hm) (color h hm).
  Hypothesis init_hash_inj_rel : forall (g : seq (triple I B L)) (mu: B -> B),
      {in (get_bts g)&, injective mu} -> perm_eq (map1 mu (init_hash g)) (init_hash (relabeling_seq_triple mu g)).
  Hypothesis color_perm_hm : forall (hm p : hash_map),
      perm_eq p hm -> forall (g : seq (triple I B L)), perm_eq (color g hm) (color g p).
  Hypothesis init_hash_perm_graph : forall (g h : seq (triple I B L)), perm_eq g h -> perm_eq (init_hash g) (init_hash h).
  Hypothesis choose_part_post_relabeling : forall (hm: hash_map)(mu : B -> B), choose_part (map1 mu hm) = map1 mu (choose_part hm).
  Hypothesis color_refine_perm_hm : forall (g : seq (triple I B L)) (hm p: hash_map), perm_eq hm p -> perm_eq (color_refine g hm) (color_refine g p).

  Hypothesis color_refine_post_relabeling : forall (g : seq (triple I B L)) (hm : hash_map) (mu : B -> B),
           {in (get_bts g)&, injective mu} ->
           {in (bnodes_hm hm)&, injective mu} ->
           perm_eq (color_refine (relabeling_seq_triple mu g) (map1 mu hm))
                   (map1 mu (color_refine g hm)).
  Hypothesis color_refine_perm_graph : forall (g h: seq (triple I B L)) (hm : hash_map), perm_eq g h -> perm_eq (color_refine g hm) (color_refine h hm).

  Hypothesis mark_post_rel: forall (b : B) (hm : hash_map) (mu : B -> B),
         {in (bnodes_hm hm)&, injective mu} ->
         perm_eq (mark (mu b) (map1 mu hm)) (map1 mu (mark b hm)).

  Hypothesis mark_perm_hm : forall (b : B) (hm p : hash_map), perm_eq hm p -> perm_eq (mark b hm) (mark b p).

  Hypothesis init_hash_ubs : forall (g : seq (triple I B L)), uniq (bnodes_hm (init_hash g)).
  Hypothesis color_ubs : forall (hm: hash_map) (g : seq (triple I B L)), (uniq (bnodes_hm hm)) -> uniq (bnodes_hm (color g hm)).
  Hypothesis mark_ubs : forall (hm: hash_map),
      (uniq (bnodes_hm hm))
      -> forall (b : B), b \in (bnodes_hm hm)
                               -> uniq (bnodes_hm (mark b hm)).
  Hypothesis color_refine_ubs : forall (hm: hash_map) (g : seq (triple I B L)), (uniq (bnodes_hm hm)) -> uniq (bnodes_hm (color_refine g hm)).

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

  Definition in_eq (T U: eqType) (s : seq U) (f g : T -> forall (u : U), u \in s -> T) := (forall (t : T)(u : U), f t u =1 g t u).

  Lemma eq_foldl_in {T U: eqType} (s : seq U) (t: T) (f g : T -> forall (u : U), u \in s -> T):
    in_eq T U s f g ->
     foldl_In s f t = foldl_In s g t.
  Proof.
    move: t f g.
    elim: s=> [//|hd tl IHtl t f g].
  move=> H; autorewrite with foldl_In; rewrite H.
  set P1 := foldl_In_obligation_2 _ _ _ _ _ _ _.
  set P2 := foldl_In_obligation_2 _ _ _ _ _ _ _.
  move: P1 P2=> P1 P2.
  have -> : g t hd P1 = g t hd P2 by rewrite (eq_irrelevance P1).
  apply IHtl.
  move=> t' u' t''; rewrite H.
  set P1' := foldl_In_obligation_1 _ _ _ _ _ _ _ _ _ _.
  set P2' := foldl_In_obligation_1 _ _ _ _ _ _ _ _ _ _.
  have -> : P1' = P2' by rewrite (eq_irrelevance P1').
  by [].
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

    Lemma find_index_eq_hash (bs: seq B) (s: seq nat) (bn : nat) :
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
        (n \in hashes_hm hm) =
          (n \in hashes_hm (filter (negb \o (fun p0 : B * nat => m == p0.2)) hm)).
    Proof.
    set p := negb \o (fun p0 : B * nat => m == p0.2).
    move=> neq.
    apply /idP/idP.
    elim: hm=> [//| h tl IHtl] /=.
    rewrite in_cons=> /orP[/eqP eq| in_tl].
    + by rewrite /p/= -eq neq /= in_cons eq eqxx.
    + case: h=> b n'; rewrite /p/=.
      case_eq (m != n')=> H; last by apply IHtl.
      by rewrite /=; apply inweak; apply IHtl.
    + move=> /mapP[/= bn ]. rewrite mem_filter=> /andP[].
      rewrite /p=>/= pbn bnin ->; move: bnin.
      elim: hm=> [//|hd tl IHtl].
      rewrite in_cons=> /orP[/eqP->|]; first by rewrite in_cons eqxx.
      by rewrite in_cons=> /IHtl ->; rewrite orbT.
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
    have : size hm < (size hm).+1 by apply ltnSn.
    move: hm (size hm).+1.
    move=> hm n1; move: n1 hm=> n1.
    elim: n1 => [//| n1 IHn hm].
    case: hm=> //p tl/=. 
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
      + by rewrite -hashes_filter_neq=> //; rewrite eq_sym neq_np.
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
    rewrite (hm_zip hm); set hm' := zip _ _.
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
    rewrite (hm_zip hm) !find_index_eq_bnode // -!hm_zip /eqP.
    have /=[n nin]:= bnodes_hm_exists hm b bin.
    have /=[n' n'in]:= bnodes_hm_exists hm b' b'in.
    suffices [inb inb'] :
      (index b [seq i.1 | i <- hm] < size hm)%N /\ (index b' [seq i.1 | i <- hm] < size hm)%N.
      rewrite (nth_map (b,O)) // (nth_map (b',O)) //.
      have [n'' n''P]: exists n, (nth (b, O) hm (index b [seq i.1 | i <- hm])) = (b,n).
        by apply (nth_funof g)=> //; rewrite -mem_eq.
      rewrite n''P.
      have [n''' n'''P]: exists n, (nth (b', O) hm (index b' [seq i.1 | i <- hm])) = (b',n).
        by apply (nth_funof g)=> //; rewrite -mem_eq.
      rewrite n'''P.
      move=> /(funof_snd_inj g hm mem_eq fine).
      by rewrite -{1}n''P -{1}n'''P => /(_ (mem_nth _ inb) (mem_nth _ inb'))=> [[-> ]].
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
    by rewrite map_inj_in_uniq=> //; apply inj_get_bts_inj_ts.
    Qed.

    Definition ifb {T : Type} (b : bool) (f : b = true -> T) (g : b = false -> T) :=
      (if b then f else g) erefl.

    Definition tT (b : bool) : b = true -> is_true b :=
      id.

    Definition nF (b : bool) : b = false -> is_true (~~ b).
      by move=> p; apply/negPf.
    Defined.

    Definition Fn (b : bool) :is_true (~~ b) -> b = false.
      by move=> /negPf.
    Defined.

    Definition pres_ubs (hm : hash_map) : uniq (bnodes_hm hm) ->
                                          forall  (b : B), b \in (bnodes_hm hm) ->
                                                  forall (g : seq (triple I B L)),
                                                     uniq (bnodes_hm (color_refine g (mark b hm))).
    Proof.
    move=> ubs b bin g.
    by apply color_refine_ubs; apply mark_ubs=> //.
    Qed.

(*TODO : merge distinguish__ and distinguish by gbot <- can *)
    Equations? distinguish__
      (g : seq (triple I B L))
        (hm : hash_map)
        (gbot : seq (triple I B L))
       (finePn : ~~ is_fine (gen_partition hm))
       (ubs : uniq (bnodes_hm hm))
      (* (hm : ) *)
        : seq (triple I B L) by wf (M hm) lt :=
      distinguish__ g hm gbot finePn ubs :=
      let p := choose_part hm in
	    let d := fun (bn : B * nat) (inP : bn \in p) =>
	               let hm' := color_refine g (mark bn.1 hm) in
                 let fine := is_fine (gen_partition hm') in
                 @ifb _ fine (fun h=> sort le_triple (relabeling_seq_triple (fun_of_hash_map hm') g))
	                 (* if fine then *)
	                 (*   let candidate := sort le_triple (relabeling_seq_triple (fun_of_hash_map hm') g) in *)
	                 (* candidate *)
	               (fun h=> distinguish__ g hm' gbot (nF h) (pres_ubs hm ubs bn.1 (in_part_in_bnodes _ _ inP) g)) in
	  (* else (distinguish__ g hm' gbot) in *)
      let f := fun gbot (bn : B * nat) (inP : bn \in p) =>
                 let candidate := d bn inP in
                 if cmp gbot candidate then candidate else gbot in
      foldl_In p f gbot.
      Proof.
      by apply /ltP; apply (leq_ltn_trans (color_refineP _ _)); rewrite nat_coq_nat; apply: (markP _ _ _ _ inP).
      Qed.

     (*  Equations? distinguish__v2 *)
     (*  (g : seq (triple I B L)) *)
     (*    (hm : hash_map) *)
     (*    (gbot : seq (triple I B L)) *)
     (*   (finePn : ~~ is_fine (gen_partition hm)) *)
     (*   (ubs : uniq (bnodes_hm hm)) *)
     (*  (* (hm : ) *) *)
     (*    : seq (triple I B L) by wf (M hm) lt := *)
     (*  distinguish__v2 g hm gbot finePn ubs := *)
     (*  let p := choose_part hm in *)
	   (*  let d := fun (bn : B * nat) (inP : bn \in p) => *)
	   (*             let hm' := color_refine g (mark bn.1 hm) in *)
     (*             if insub hm' : {? x | ~~ is_fine (gen_partition x) } is Some fineS then *)
     (*               distinguish__v2 g (\val fineS) gbot (pres_ubs (\val fineS) _ bn.1 _ g) _ *)
     (*               else *)
     (*                 sort le_triple (relabeling_seq_triple (fun_of_hash_map hm') g) *)
     (* in *)
     (*  let f := fun gbot (bn : B * nat) (inP : bn \in p) => *)
     (*             let candidate := d bn inP in *)
     (*             if cmp gbot candidate then candidate else gbot in *)
     (*  foldl_In p f gbot. *)
     (*  Proof. *)
     (*    exact: fineS. *)
     (*    apply H. *)
     (*    apply pres_b *)
     (*  by apply /ltP; apply (leq_ltn_trans (color_refineP _ _)); rewrite nat_coq_nat; apply: (markP _ _ _ _ inP). *)
     (*  Qed. *)

    Definition distinguish (g : seq (triple I B L)) (hm : hash_map) :
       ~~ is_fine (gen_partition hm) -> uniq (bnodes_hm hm) -> seq (triple I B L) :=
      distinguish__ g hm can.

    Definition p1andb (b1 b2 : bool) : b1 && b2 -> b1.
    Proof. by move=> /andP[->]. Defined.

    Definition p2andb (b1 b2 : bool) : b1 && b2 -> b2.
    Proof. by move=> /andP[_ ->]. Defined.

    Definition distinguish_ (g : seq (triple I B L)) (hm : hash_map) : seq (triple I B L) :=
      let p := choose_part hm in
	    let d := fun (bn : B * nat) =>
	    (* let d := fun (bn : B * nat)(inP : bn \in p) => *)
	               let hm' := color_refine g (mark bn.1 hm) in
                 if insub hm' : {? x | ~~ is_fine (gen_partition x) && uniq (bnodes_hm x)} is Some fineS then
                   let P := valP fineS in
	                 (distinguish g (\val fineS) (p1andb _ _ P) (p2andb _ _ P)) else
	    (* if is_fine (gen_partition hm') then *)
	                  sort le_triple (relabeling_seq_triple (fun_of_hash_map hm') g)
	               (* else (distinguish g hm') *)
      in
      let f := fun gbot (bn : B * nat) =>
                 let candidate := d bn in
                 if cmp gbot candidate then candidate else gbot in
    foldl f can p.

    Lemma eq_distinguish (g : seq (triple I B L)) (hm : hash_map) (finePn : ~~ is_fine (gen_partition hm)) (ubs : uniq (bnodes_hm hm))
      : distinguish g hm finePn ubs = distinguish_ g hm.
    Proof.
    rewrite /distinguish_/distinguish -foldl_foldl_eq.
    autorewrite with distinguish__.
    rewrite /=.
    apply eq_foldl_in.
    move=> /= t u uP=> /=.
    set u' := match insub (color_refine _ _) with Some _ => _ | None => _ end.
    set u'' := ifb _ _.
    apply (f_equal (fun u => if cmp t u then u else t)).
    rewrite {}/u''{}/u'.
    rewrite /ifb.
    set hm' := (color_refine g _).
    set P := gen_partition hm'.
    move: erefl.
    set y := is_fine P.
    rewrite {1}/y.
    remember (is_fine P) as fine in |-.
    case: fine Heqfine.
    Admitted.

    Definition canonicalize (g : seq (triple I B L)) (hm : hash_map)
      (bn : (B * nat)) :=
	      let hm' := color_refine g (mark bn.1 hm) in
	      if is_fine (gen_partition hm') then
	        let candidate := sort le_triple (relabeling_seq_triple (fun_of_hash_map hm') g) in (* TODO simplfy let *)
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
      bnodes_hm hm =i get_bts g -> (negb \o (is_fine (B:=B))) (gen_partition hm) -> uniq (distinguish g hm).
    Proof.
    have : M hm < S (M hm) by apply ltnSn.
    move: hm (M hm).+1.
    move=> hm n; move: n hm=> n.
    elim: n => [//| n IHn hm].
    case: (distinguish_choice g hm); first by move=> ->; rewrite ucan.
    move=> /mapP/= [bn pin ->].
    move=> MH eqbns finePn.
    rewrite /canonicalize.
    case: ifP=> [fine|finePn1].
    -  rewrite sort_uniq; apply uniq_label_is_fine=> //; apply color_refine_good_hm.
       by apply (good_mark _ _ eqbns); apply in_part_in_bnodes.
    - apply IHn.
      + apply: Order.POrderTheory.le_lt_trans (color_refineP _ _) _.
        by apply: Order.POrderTheory.lt_le_trans (markP _ _ _) MH.
      + by apply color_refine_good_hm; apply good_mark=> //; apply in_part_in_bnodes.
      + by move=> /=; rewrite finePn1.
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
    move=> /mem_eq_terms_ts/= mem_eq b.
    by rewrite !mem_undup !mem_filter mem_eq.
    Qed.

    Lemma mem_eq_get_bts (g h : seq (triple I B L)) :
      g =i h -> get_bts g =i get_bts h.
    Proof.
    move=> /mem_eq_bnodes_ts/= mem_eq b.
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

        (* This is where we use the fact that can is nil *)
    Lemma nil_is_nil (g : seq (triple I B L)) (hm : hash_map):
      bnodes_hm hm =i get_bts g ->
      ~~ is_fine (gen_partition hm) ->
      distinguish g hm = can -> g = can.
    Proof.
    have : M hm < S (M hm) by apply ltnSn.
    move: hm (M hm).+1.
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

    
    (* Hypothesis distinguish_complete : *)
    (*   forall (g h : seq (triple I B L)), *)
    (*     uniq g -> uniq h -> *)
    (*       effective_iso_ts g h -> *)
    (*         is_fine (gen_partition (color g (init_hash g))) = false -> *)
    (*           distinguish g (color g (init_hash g)) =i distinguish h (color h (init_hash h)). *)


    (* Hypothesis eiso_mem_eq_canonicalize :
    forall (g h : seq (triple I B L)) (ug: uniq g) (uh: uniq h),
      effective_iso_ts g h ->
      let color_g := color g (init_hash g) in 
      let color_h := color h (init_hash h) in 
        ~~ is_fine (gen_partition color_g) ->
          map (canonicalize g color_g) (choose_part color_g)
          =i map (canonicalize h color_h) (choose_part color_h). *)

    Lemma simpl_fun_of_hm (hm : hash_map):
      uniq (bnodes_hm hm) ->
        {in (bnodes_hm hm),
         hm =1 (nat_inj \o (fun b : B => (nth 0 (map snd hm) (index b (bnodes_hm hm)))))}.
    Proof.
    move=> ubn b /bnodes_hm_has_eq_bnodes bin.
    rewrite /fun_of_hash_map bin /=.
    congr nat_inj; congr (nth 0 (hashes_hm hm)).
    have eq_size : size [seq i.1 | i <- hm] = size [seq i.2 | i <- hm] by rewrite !size_map.
    by rewrite (hm_zip hm) /bnodes_hm map_fst_zip_size // find_index_eq_bnode.
    Qed.

    Lemma in_hm (hm : hash_map):
      uniq (bnodes_hm hm) ->
      {in hm,
            (fun (bn :B * nat) => (nth 0 [seq i.2 | i <- hm] (index bn.1 (bnodes_hm hm)))) =1 snd}.
    Proof.
    move=> /= ubs bn bnin.
    suffices -> : (index bn.1 (bnodes_hm hm)) = (index bn hm).
      by rewrite (nth_map bn) ?nth_index ?index_mem.
    apply index_map_in=> //.
    apply /in_map_injP=> //.
    by rewrite (hm_zip hm); apply zip_uniq_l.
    Qed.

    Lemma nth_hash (hm: hash_map):
      (uniq (bnodes_hm hm)) ->
      [seq nth 0 [seq i.2 | i <- hm] (index b (bnodes_hm hm)) | b <- bnodes_hm hm] = hashes_hm hm.
    Proof.
    elim: hm=> [//|hd tl IHtl] ubns.
    rewrite /= eqxx /=; congr cons.
    rewrite -IHtl; last by apply: uniq_tail ubns.
    apply eq_in_map => b bin.
    set i := index _ _.
    set s := map _ tl.
    suffices -> : hd.1 == b = false.
      by case: s.
    move: ubns=> /=/andP[/memPnC /(_ b bin)].
    by case: (hd.1 == b).
    Qed.

    Lemma peq_map_hm_bnodes (hm1 hm2: hash_map):
      uniq (bnodes_hm hm1) ->
      uniq (bnodes_hm hm2) ->
      (perm_eq (map hm1 (bnodes_hm hm1)) (map hm2 ((bnodes_hm hm2)))) ->
      (perm_eq (hashes_hm hm1) (hashes_hm hm2)).
    Proof.
    rewrite /fun_of_hash_map=> u1 u2.
    have /eq_in_map -> := simpl_fun_of_hm _ u1.
    have /eq_in_map -> := simpl_fun_of_hm _ u2.
    rewrite (map_comp nat_inj) (map_comp nat_inj _ (bnodes_hm hm2)) !nth_hash //.
    by apply perm_map_inj; apply nat_inj_.
    Qed.

    Lemma hashes_of_map1 (hm : hash_map) (mu : B -> B):
      (* map snd (map1 mu hm) = map snd hm. *)
      hashes_hm (map1 mu hm) = hashes_hm hm.
    Proof. by elim: hm=> [//|hd tl /= ->]. Qed.

    Lemma map1_map (mu : B -> B):
      (map1 mu) =1 (map (fun p=> (mu p.1,p.2))).
    Proof.
    move=> hm; elim: hm=> [//|[b n] tl IHtl] /=.
    by rewrite /map1/= -IHtl.
    Qed.

    Lemma distinguish_perm_hm : forall (hm p : hash_map) g, perm_eq hm p -> distinguish g hm = distinguish g p.
    Proof.
    move=> hm p g peq.
    rewrite !distinguish_fold_map/distinguish_fold.
    set cang := map _ _.
    set canh := map _ _.
    suffices eq_mem_ch : cang =i canh.
      by rewrite !foldl_idx/= (eq_big_idem _ _ choose_graph_idem eq_mem_ch).
    rewrite {}/cang{}/canh=>/= c.
    suffices peq_cp : perm_eq (choose_part hm) (choose_part p).
      rewrite -(eq_mem_map _ (perm_mem peq_cp)).
      suffices /eq_in_map -> : {in choose_part hm, canonicalize g hm =1 canonicalize g p} by [].
    move=> bn bnin.
    rewrite /canonicalize.
    have /perm_mem := peq.
    
    (* rewrite eqxx.  eqxx. *)


    Admitted.

    Lemma distinguish_perm_graph : forall (hm : hash_map) (g h : seq (triple I B L)),
        perm_eq g h -> distinguish g hm = distinguish h hm.
    Admitted.

    Section wip.

      Definition post_rel (f : seq (triple I B L) -> hash_map -> hash_map) :=
        forall (G : seq (triple I B L)) (hm : hash_map) (mu : B -> B),
          {in (get_bts G)&, injective mu} ->
          {in (bnodes_hm hm)&, injective mu} ->
          perm_eq (f (relabeling_seq_triple mu G) (map1 mu hm)) (map1 mu (f G hm)).

      Definition perm_graph (f : seq (triple I B L) -> hash_map -> hash_map) :=
        forall (G H: seq (triple I B L)), perm_eq G H -> forall (hm : hash_map), perm_eq (f G hm) (f H hm).

      Definition perm_hm (f : seq (triple I B L) -> hash_map -> hash_map) :=
        forall (hm p : hash_map), perm_eq hm p -> forall (G : seq (triple I B L)), perm_eq (f G hm) (f G p).


      Lemma perm_graph_in_hm (f g : seq (triple I B L) -> hash_map -> hash_map):
        perm_hm f ->
        perm_graph g ->
        forall (G H : seq (triple I B L)),
          perm_eq G H ->
          forall (I : seq (triple I B L)) (hm : hash_map),
                 perm_eq (f I (g G hm)) (f I (g H hm)).
     Proof.
     move=> f_perm_hm g_perm_graph G H peq i hm.
     by apply f_perm_hm; apply g_perm_graph.
     Qed.

     Lemma post_rel_in_hm (f g : seq (triple I B L) -> hash_map -> hash_map):
        perm_hm f ->
        post_rel g ->
        forall (G H : seq (triple I B L)) (hm : hash_map) (mu : B -> B),
            {in (get_bts G)&, injective mu} ->
              {in (bnodes_hm hm)&, injective mu} ->
            perm_eq (f H (g (relabeling_seq_triple mu G) (map1 mu hm))) (f H (map1 mu (g G hm))).
     Proof.
     move=> f_perm_hm g_post_rel G H hm mu mu_injG mu_injhm.
     by apply f_perm_hm; apply g_post_rel.
     Qed.

     Lemma perm_post_rel_in_hm (f : seq (triple I B L) -> hash_map -> hash_map):
       perm_graph f ->
       post_rel f ->
       forall (G H : seq (triple I B L)) (mu: B -> B),
         perm_eq (relabeling_seq_triple mu G) H ->
         {in (get_bts G)&, injective mu} ->
         forall (hm : hash_map), {in (bnodes_hm hm)&, injective mu} ->
           perm_eq (f H (map1 mu hm)) (map1 mu (f G hm)).
     Proof.
     move=> f_perm_graph f_post_rel G H mu peq mu_injG hm mu_injHm.
     have step : perm_eq (f H (map1 mu hm)) (f (relabeling_seq_triple mu G) (map1 mu hm)).
       by apply f_perm_graph; rewrite perm_sym.
     apply: (perm_trans step).
     by apply f_post_rel.
     Qed.

     Lemma perm_graph_post_rel_in_hm (f g : seq (triple I B L) -> hash_map -> hash_map):
       perm_hm f ->
       perm_graph g ->
       post_rel g ->
       forall (G H : seq (triple I B L)) (mu: B -> B),
         perm_eq (relabeling_seq_triple mu G) H ->
           {in (get_bts G)&, injective mu} ->
             forall (hm : hash_map), {in (bnodes_hm hm)&, injective mu} ->
               perm_eq (f H (g H (map1 mu hm))) (f H (map1 mu (g G hm))).
     Proof.
     move=> f_perm_hm g_perm_graph g_post_rel G H mu peq mu_injG hm mu_injHm.
     by apply f_perm_hm; apply perm_post_rel_in_hm.
     Qed.

     Definition pres_bnodes (f : seq (triple I B L) -> hash_map -> hash_map) :=
       forall (G : seq (triple I B L))(hm : hash_map),
         bnodes_hm hm =i get_bts G -> bnodes_hm (f G hm) =i get_bts G.

     Lemma post_rel_graph_hm (f g : seq (triple I B L) -> hash_map -> hash_map):
       perm_hm f ->
       perm_graph f ->
       post_rel f ->
       perm_graph g ->
       post_rel g ->
       pres_bnodes g ->
       forall (G H : seq (triple I B L)) (mu: B -> B),
         perm_eq (relabeling_seq_triple mu G) H ->
           {in (get_bts G)&, injective mu} ->
             forall (hm : hash_map),
              bnodes_hm hm =i get_bts G ->
              perm_eq (f H (g H (map1 mu hm))) (map1 mu (f G (g G hm))).
     Proof.
     move=> f_perm_hm f_perm_graph f_post_rel g_perm_graph g_post_rel g_pres_bnodes G H mu peq mu_injG hm mem_eq.
     have /perm_trans -> // : perm_eq (f H (g H (map1 mu hm))) (f H (map1 mu (g G hm))).
       apply f_perm_hm; apply perm_post_rel_in_hm=> // b bin; rewrite !mem_eq; apply mu_injG.
     apply perm_post_rel_in_hm => //.
     move: g_pres_bnodes=> /(_ _ _ mem_eq) f_mem_eq.
     by move => b bin; rewrite !f_mem_eq; apply mu_injG.
     Qed.

    End wip.

    Definition init_hash' (g : seq (triple I B L)): hash_map -> hash_map :=
      fun hm => init_hash g.

    Lemma init_hash_shape (g : seq (triple I B L)) (hm : hash_map) :
      init_hash g = init_hash' g hm.
    Proof. by []. Qed.

    Lemma init_hash_post_rel : post_rel init_hash'.
    Proof.
    move=> G hm mu mu_injG mu_injhm.
    by rewrite -init_hash_shape perm_sym; apply init_hash_inj_rel.
    Qed.

    Lemma init_hash_is_perm_graph: perm_graph init_hash'.
    Proof.
    by move=> G H peq hm; rewrite -init_hash_shape; apply init_hash_perm_graph.
    Qed.

    Lemma init_hash_is_perm_hm: perm_hm init_hash'.
    by move=> hm p _ g; rewrite -init_hash_shape.
    Qed.

    Lemma color_post_rel : post_rel color.
    Proof.
    move=> G hm mu mu_injG mu_injhm.
    by apply color_post_relabeling.
    Qed.

    Lemma color_is_perm_graph: perm_graph color.
    Proof.
    by move=> G H peq hm; apply color_perm_graph.
    Qed.

    Lemma color_is_perm_hm: perm_hm color.
    by move=> hm p peq g; rewrite perm_sym; apply color_perm_hm.
    Qed.

    Lemma color_pres_bnodes : pres_bnodes color.
    Proof. by move=> G hm; apply color_good_hm. Qed.

    Hint Resolve init_hash_post_rel.
    Hint Resolve init_hash_is_perm_graph.
    Hint Resolve init_hash_is_perm_hm.
    Hint Resolve color_post_rel.
    Hint Resolve color_is_perm_graph.
    Hint Resolve color_is_perm_hm.
    Hint Resolve color_pres_bnodes.

    Lemma color_refine_post_rel : post_rel color_refine.
    Proof.
    move=> G hm mu mu_injG mu_injhm.
    by apply color_refine_post_relabeling.
    Qed.

    (* Lemma color_refine_is_perm_graph: perm_graph color_refine. *)
    (* Proof. *)
    (* by move=> G H peq hm; apply color_refine_perm_graph. *)
    (* Qed. *)

    (* Lemma color_refine_is_perm_hm: perm_hm color_refine. *)
    (* by move=> hm p peq g; rewrite perm_sym; apply color_refine_perm_hm. *)
    (* Qed. *)


    Lemma fun_of_hash_perm : forall (hm p : hash_map),
                uniq (bnodes_hm hm) ->
                perm_eq hm p ->
                {in (bnodes_hm hm), fun_of_hash_map hm =1 p}.
    Proof.
    move=> hm p ubs peq b bin_hm.
    have bin_p : b \in bnodes_hm p.
      by move/(perm_map fst): peq=> peq; rewrite -(perm_mem peq).
    rewrite /fun_of_hash_map !bnodes_hm_has_eq_bnodes //.
    congr nat_inj.
    rewrite !(nth_map (b,O)).
    rewrite {2}(hm_zip hm) {2}(hm_zip p) !find_index_eq_bnode ?size_proj //.
    have := bin_hm.
    move=> /(in_zip_l)=> /(_ _ (hashes_hm hm)).
    rewrite /bnodes_hm/hashes_hm/=; move=> []; first by rewrite size_proj.
    move=> bn.
    rewrite -(hm_zip hm)=> [[bnin [<- ]] ] [n n_eq].
    have fst_inj_in_p: {in p &, injective fst}.
      apply /in_map_injP.
      + by rewrite -(perm_uniq peq); rewrite (hm_zip hm); apply zip_uniq_l.
      by move/(perm_map fst): peq=> /perm_uniq <-.
    rewrite !index_map_in //.
    rewrite !nth_index //.
    + by rewrite -(perm_mem peq).
      by rewrite -(perm_mem peq).
      by move=> bn1 bn2; rewrite !(perm_mem peq); apply fst_inj_in_p.
      rewrite {1}(hm_zip p) find_index_eq_bnode.
      move: bin_p.
      by rewrite -index_mem size_map=> ->.
      by rewrite size_proj.
      rewrite {1}(hm_zip hm) find_index_eq_bnode.
      move: bin_hm.
      by rewrite -index_mem size_map=> ->.
      by rewrite size_proj.
    Qed.

    Lemma peq_get_bts (ts1 ts2: seq (triple I B L)): perm_eq ts1 ts2 -> perm_eq (get_bts ts1) (get_bts ts2).
    Proof.
    move=> peq; rewrite /get_bts/get_bs.
    by apply perm_pmap; apply peq_bnodes.
    Qed.

    Lemma eiso_correct_complete (g h : seq (triple I B L)) (ug: uniq g) (uh: uniq h) :
      effective_iso_ts g h <-> (template g) == (template h).
    Proof.
    split; last first.
    + move=> /eqP eqmgmh.
      have := eiso_out_template g ug.
      rewrite eqmgmh=> mgh.
      have /(effective_iso_ts_sym uh) hmh := eiso_out_template h uh.
      by apply: (effective_iso_ts_trans mgh hmh).
    rewrite /template=> eiso; rewrite -(iso_color_fine _ _ eiso) //.
    case: ifP=> [fineP|finePn].
    + apply /eqP/rdf_leP.
      apply uniq_perm.
      - by apply uniq_label_is_fine=> //; apply color_good_hm; apply good_init.
      - rewrite (iso_color_fine _ _ eiso) // in fineP.
        by apply uniq_label_is_fine=> //; apply color_good_hm; apply good_init.
        by apply iso_color_fine_can.
    + set col_g := color _ _.
      set col_h := color _ _.
      case: eiso=> mu /and3P[piso urel peq].
      have mu_inj := is_pre_iso_ts_inj piso.
      have peq_col : perm_eq col_h (map1 mu col_g).
        rewrite /col_h/col_g (init_hash_shape _ (map1 mu [::])) (init_hash_shape _ [::]).
        have /perm_trans -> // : (perm_eq (color h (init_hash' h (map1 mu [::]))) (color h (map1 mu (init_hash' g [::])))).
          by apply perm_graph_post_rel_in_hm.
        by apply perm_post_rel_in_hm=> // b bin; rewrite !good_init; apply mu_inj.
      rewrite -(distinguish_perm_graph _ _ _ peq) (distinguish_perm_hm _ _ _ peq_col).
      have : good_hash_map_for g col_g. by apply color_inv; apply color_init_inv.
      have : uniq (bnodes_hm col_g).
        by apply color_ubs; apply init_hash_ubs.
      have : M col_g < S (M col_g) by apply ltnSn.
      have : bnodes_hm col_g =i get_bts g by apply color_good_hm; apply good_init.
      move: col_g (M col_g).+1 {peq_col}.
      move=> hm n; move: n hm=> n.
      elim: n => [//| n' IHn hm] mem_eq_bs measure ubs_hm ghm_f.
      rewrite !distinguish_fold_map /distinguish_fold.
      set cang := (map _ _).
      set canh := (map _ _).
      suffices mem_eq_cands : cang =i canh.
        by rewrite !foldl_idx (eq_big_idem _ _ choose_graph_idem mem_eq_cands) eqxx.
      rewrite /cang/canh.
      rewrite choose_part_post_relabeling.
      set pp := map1 _ _.
      rewrite map1_map -map_comp {}/pp.
      set can_g := canonicalize _ _.
      set can_h := canonicalize _ _.
      suffices -> :
        [seq can_g i | i <- choose_part hm] = [seq ((can_h) \o (fun p => (mu p.1, p.2))) i | i <-  choose_part hm] by [].
      suffices step (bn : B * nat) : bn \in choose_part hm -> can_g bn = can_h (mu bn.1, bn.2) by apply/eq_in_map.
        rewrite /can_g /can_h /canonicalize => hb /=.
        set hmg := (X in is_fine (gen_partition X)).
        set test_g := is_fine _.
        set hmh := (X in is_fine (gen_partition X)).
        set test_h := is_fine _.
        have -> : test_h = test_g.
         suffices /perm_hash_eq_fine : (perm_eq (hashes_hm hmg) (hashes_hm hmh)).
           by rewrite /test_g => ->.
         rewrite /hmh -(hashes_of_map1 hmg mu); apply perm_map.
         have /(perm_trans _) -> // : perm_eq (color_refine (relabeling_seq_triple mu g) (mark (mu bn.1) (map1 mu hm))) hmh.
           by apply color_refine_perm_hm; apply mark_perm_hm.
         have /(perm_trans _) -> //: perm_eq (color_refine (relabeling_seq_triple mu g) (map1 mu (mark bn.1 hm))) (color_refine (relabeling_seq_triple mu g) (mark (mu bn.1) (map1 mu hm))).
           apply color_refine_perm_hm; rewrite perm_sym.
           by apply mark_post_rel=> b1 b2; rewrite !mem_eq_bs; apply mu_inj.
         have mu_inj_mhm: {in bnodes_hm (mark bn.1 hm) &, injective mu}.
           by move=> b1 b2; rewrite !(good_mark g) // ?in_part_in_bnodes //; apply mu_inj.
         by rewrite /hmg perm_sym; apply color_refine_post_rel=> //.
        case: ifP => [htest | hNtest].
        have ubs_hmg : (uniq (bnodes_hm hmg)).
            apply color_refine_ubs.
            apply mark_ubs=> //.
            by apply in_part_in_bnodes.
        have hmg_inj : {in get_bts g &, injective (color_refine g (mark bn.1 hm))}.
            move=> b1 b2 bin1 bin2.
          have eq_bs: (bnodes_hm (color_refine g (mark bn.1 hm))) =i get_bts g.
            by apply color_refine_good_hm; apply good_mark; [apply mem_eq_bs | apply in_part_in_bnodes].
          have hm_inj := funof_snd_inj _ _ eq_bs htest.
          rewrite !simpl_fun_of_hm ?eq_bs //.
          rewrite -/hmg.
          move=> /nat_inj_.
          have -> : b1 = (b1,nth 0 [seq i.2 | i <- hmg] (index b1 (bnodes_hm hmg))).1 by [].
          have -> : b2 = (b2,nth 0 [seq i.2 | i <- hmg] (index b2 (bnodes_hm hmg))).1 by [].
          suffices SU : forall (T U : eqType)(hm : seq (T * U)), uniq hm -> forall (t : T), t \in map fst hm ->
                                                                                                  forall (u : U),
                                                                                                    (t,(nth u (map snd hm) (index t (map fst hm)))) \in hm.
          have H: (b1, nth 0 [seq i.2 | i <- hmg] (index b1 (bnodes_hm hmg))) \in hmg.
            apply SU; last by rewrite eq_bs.
            by rewrite (hm_zip hmg); apply zip_uniq_l.
          have H2: (b2, nth 0 [seq i.2 | i <- hmg] (index b2 (bnodes_hm hmg))) \in hmg.
            apply SU; last by rewrite eq_bs.
            by rewrite (hm_zip hmg); apply zip_uniq_l.
          rewrite !in_hm //.
          by move=> /(hm_inj)=> /(_ H H2) [->].
          move=> T U tus utus t tin u.
          move: tin utus.
          elim: tus=> [//| [b' n''] tl IHtl] /=.
          rewrite in_cons=> /orP[].
          by move=> /eqP ->; rewrite eqxx /= in_cons eqxx.
          case_eq (b' == t).
          + by move=> /eqP ->; rewrite /= in_cons eqxx.
          + move=> H tin /andP[nin utl]; rewrite in_cons.
            suffices -> : ((t, nth u (n'' :: [seq i.2 | i <- tl]) (index t [seq i.1 | i <- tl]).+1) \in tl).
              by rewrite orbT.
            by apply IHtl=> //.
        - apply /rdf_leP.
          have in_hm_inj : {in bnodes_hm hm &, injective mu}.
            by move=> b1 b2; rewrite !mem_eq_bs; apply mu_inj.
          apply uniq_perm.
          rewrite /test_g/hmg in htest.
          apply /in_map_injP=> //.
          by apply inj_get_bts_inj_ts.
        - set cr := color_refine _ _.
          suffices : forall (hm p : hash_map),
                uniq (bnodes_hm hm) ->
                perm_eq hm p ->
                {in (bnodes_hm hm), fun_of_hash_map hm =1 p}.
            have ubs_cr : uniq (bnodes_hm cr).
              have /eq_map eq_mapC : fst \o (fun p : B * nat => (mu p.1,p.2)) =1 mu \o fst.
                by [].
              have mu_inj_hm: {in [seq i.1 | i <- hm] &, injective mu}.
                move=> b1 b2; rewrite !mem_eq_bs.
                by apply mu_inj.
              apply color_refine_ubs; apply mark_ubs.
              rewrite map1_map /bnodes_hm -map_comp.
              rewrite eq_mapC map_comp.
              rewrite map_inj_in_uniq //.
              rewrite map1_map/bnodes_hm -map_comp eq_mapC map_comp.
              by move/in_part_in_bnodes : hb=> /(map_f mu).
            have peq_cr: perm_eq cr (map1 mu (color_refine g (mark bn.1 hm))).
              rewrite /cr.
              have /(perm_trans) -> // : perm_eq (color_refine (relabeling_seq_triple mu g) (mark (mu bn.1) (map1 mu hm))) (color_refine (relabeling_seq_triple mu g) (map1 mu (mark bn.1 hm))).
                apply color_refine_perm_hm.
                by apply mark_post_rel => b1 b2; rewrite !mem_eq_bs; apply mu_inj.
              apply color_refine_post_rel=> //.
              move=> b1 b2.
              rewrite !(good_mark g) //. apply mu_inj.
              by apply in_part_in_bnodes.
              by apply in_part_in_bnodes.
            move=> /(_ _ _ ubs_cr peq_cr) eq_hm.
            apply /in_map_injP=> //.
            apply inj_get_bts_inj_ts.
            move=> b1 b2 bin1 bin2.
            rewrite /cr !eq_hm.
            suffices /andP[/mapP /=[bb1 bb1in ->] /mapP/= [bb2 bb2in ->]]: (b1 \in (map mu (get_bts g))) && (b2 \in (map mu (get_bts g))).
            have -> : map1 mu (color_refine g (mark bn.1 hm)) (mu bb1) = (map1 mu (color_refine g (mark bn.1 hm)) \o mu) bb1 by [].
            have -> : map1 mu (color_refine g (mark bn.1 hm)) (mu bb2) = (map1 mu (color_refine g (mark bn.1 hm)) \o mu) bb2 by [].
            have ghm : good_hash_map_for g hmg.
              by apply color_refine_inv; apply mark_inv; first by rewrite -mem_eq_bs; apply in_part_in_bnodes.
            rewrite !ghm //.
            by move /hmg_inj=> /(_ bb1in bb2in) ->.
            have := perm_refl (relabeling_seq_triple mu g).
            move=> /peq_get_bts.
            move=> /perm_eq_bts_relabel_inj_in=> /(_ mu_inj) peq_rel.
            by rewrite !(perm_mem peq_rel); apply /andP; split.
          rewrite color_refine_good_hm //.
          have /perm_mem peq_mark:= mark_post_rel bn.1 hm in_hm_inj.
          move=> b. rewrite (eq_mem_map _ peq_mark).
          rewrite map1_map -map_comp.
          have := perm_refl (relabeling_seq_triple mu g).
          move=> /peq_get_bts.
          move=> /perm_eq_bts_relabel_inj_in=> /(_ mu_inj) peq_rel.
          rewrite -(perm_mem peq_rel).
          have eq_bs_mark: (bnodes_hm (mark bn.1 hm)) =i get_bts g. by apply good_mark=> //; apply in_part_in_bnodes.
          rewrite -(eq_mem_map _ eq_bs_mark) /bnodes_hm -map_comp.
          by congr (in_mem b).
          *
          rewrite color_refine_good_hm //.
          have /perm_mem peq_mark:= mark_post_rel bn.1 hm in_hm_inj.
          move=> b. rewrite (eq_mem_map _ peq_mark).
          rewrite map1_map -map_comp.
          have := perm_refl (relabeling_seq_triple mu g).
          move=> /peq_get_bts.
          move=> /perm_eq_bts_relabel_inj_in=> /(_ mu_inj) peq_rel.
          rewrite -(perm_mem peq_rel).
          have eq_bs_mark: (bnodes_hm (mark bn.1 hm)) =i get_bts g.
            by apply good_mark=> //; apply in_part_in_bnodes.
          rewrite -(eq_mem_map _ eq_bs_mark) /bnodes_hm -map_comp.
          by congr (in_mem b).
          by apply fun_of_hash_perm.
          ++
            rewrite relabeling_seq_triple_comp.
            apply relabeling_ext_in.
            apply eq_in_bs_ing.
            have: perm_eq (color_refine (relabeling_seq_triple mu g) (mark (mu bn.1) (map1 mu hm))) (color_refine (relabeling_seq_triple mu g) (map1 mu (mark bn.1 hm))).
              by apply color_refine_perm_hm; apply mark_post_rel; move=> b1 b2; rewrite !mem_eq_bs; apply mu_inj.
            move=> peq' b1 b1in.
            have eq_bs_cr : bnodes_hm (color_refine g (mark bn.1 hm)) =i get_bts g.
              by apply color_refine_good_hm; apply good_mark=> //; apply in_part_in_bnodes.
            rewrite /=.
            suffices peq_cr : perm_eq (color_refine (relabeling_seq_triple mu g) (mark (mu bn.1) (map1 mu hm))) (map1 mu (color_refine g (mark bn.1 hm))).
              rewrite (fun_of_hash_perm _ _ _ peq_cr).
              have -> : map1 mu (color_refine g (mark bn.1 hm)) (mu b1) = (map1 mu (color_refine g (mark bn.1 hm)) \o mu) b1 by [].
              rewrite (color_refine_inv) //.
              apply mark_inv=> //.
              by rewrite -mem_eq_bs; apply in_part_in_bnodes.
            rewrite /bnodes_hm.
            move: peq_cr=> /(perm_map fst)/perm_uniq ->.
            have /eq_map eq_mapC : fst \o (fun p : B * nat => (mu p.1,p.2)) =1 mu \o fst by [].
            rewrite map1_map -map_comp eq_mapC map_comp.
            apply /in_map_injP.
            apply color_refine_ubs. apply mark_ubs. done. by apply in_part_in_bnodes.
            move=> b1' b2'. rewrite !eq_bs_cr. apply mu_inj.
            rewrite (eq_mem_map _ (perm_mem peq_cr)) map1_map -map_comp.
            have /eq_map eq_mapC : fst \o (fun p : B * nat => (mu p.1,p.2)) =1 mu \o fst.
                by [].
            rewrite eq_mapC.
            rewrite map_comp.
            move: b1in.
            rewrite -eq_bs_cr.
            by move=> /(map_f mu).
            have /perm_trans -> //: perm_eq (color_refine (relabeling_seq_triple mu g) (mark (mu bn.1) (map1 mu hm)))
                     (color_refine (relabeling_seq_triple mu g) (map1 mu (mark bn.1 hm))).
              by apply color_refine_perm_hm; apply mark_post_rel=> //.
            apply color_refine_post_relabeling=> //.
              move=> b1' b2'.
              suffices mem_bs_mark : (bnodes_hm (mark bn.1 hm)) =i bnodes_hm hm.
                by rewrite !mem_bs_mark; apply in_hm_inj.
              move=> bb; rewrite (good_mark g) ?mem_eq_bs //.
              by rewrite -mem_eq_bs; apply in_part_in_bnodes.
        - set hh := mark _ _.
          have /(color_refine_perm_hm (relabeling_seq_triple mu g)) : perm_eq (mark (mu bn.1) (map1 mu hm)) (map1 mu (mark bn.1 hm)).
            by apply mark_post_rel=> b1 b2; rewrite !mem_eq_bs; apply mu_inj.
          move=> /(distinguish_perm_hm _ _ _) ->.
          have : perm_eq (color_refine (relabeling_seq_triple mu g) (map1 mu (mark bn.1 hm))) (map1 mu (color_refine g (mark bn.1 hm))).
            by apply color_refine_post_rel=> // b1 b2; rewrite !(good_mark g) // ?in_part_in_bnodes //; apply mu_inj.
          move=> /(distinguish_perm_hm _ _ _) ->.
          apply /eqP.
          apply IHn.
          apply color_refine_good_hm.
          by apply good_mark; last by apply in_part_in_bnodes.
          eapply Order.POrderTheory.le_lt_trans; first by apply color_refineP.
            by apply (Order.POrderTheory.lt_le_trans (markP _ _ hb) measure).
          apply color_refine_ubs.
          apply mark_ubs=> //.
          by apply in_part_in_bnodes.
          by apply color_refine_inv; apply mark_inv=> //; rewrite -mem_eq_bs; apply in_part_in_bnodes.
 Qed.

    Lemma eiso_correct_complete' (g h : seq (triple I B L)) (ug: uniq g) (uh: uniq h) :
      perm_eq (template g) (template h) <-> effective_iso_ts g h.
    Proof.
    split; last by move=> /(eiso_correct_complete _ _ ug uh)/eqP ->; apply perm_refl.
    + move=> eqmgmh.
    have gmg := eiso_out_template g ug.
    suffices mgmh : effective_iso_ts (template g) (template h).
      have /(effective_iso_ts_sym uh) hmh := eiso_out_template h uh.
      apply: (effective_iso_ts_trans gmg _).
      by apply: (effective_iso_ts_trans mgmh hmh).
    have [mu [eiso _]]:= eqiso_ts (uniq_template _ ug) eqmgmh.
    by exists mu.
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

  Lemma good_init_kmap (g : seq (triple I B L)) : bnodes_hm (init_hash_kmap g) =i get_bts g.
  Proof. by move=> x; rewrite /init_hash_kmap/bnodes_hm zip_proj1 // size_nseq. Qed.

  Definition choose_part_kmap (hm : hash_map B) : part B :=
    let P := gen_partition (hm) in
    let pred := predC (@is_trivial B) in
    if has pred P then
      nth [::] P (find pred P)
    else [::].

  Lemma in_part_in_bnodes_kmap (bn : B * nat) (hm : hash_map B):
    bn \in choose_part_kmap hm -> bn \in hm.
  Proof.
  rewrite /choose_part_kmap/=.
  case: ifP=> [|//].
  rewrite has_find=> size_find.
  suffices /partition_memP :
    nth [::] (gen_partition hm) (find (predC (is_trivial (B:=B))) (gen_partition hm)) \in (gen_partition hm).
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

  Definition mark_hash_kmap_2 (b : B) (n : nat) (hm : hash_map B) :=
    set_nth (b,n) hm (find (eq_bnode B b) hm) (b,n).

  Definition fresh (hm : hash_map B) : nat :=
    (foldl maxn 0 (hashes_hm hm)).+1.

  Definition M_kmap (hm :hash_map B) : nat :=
    (size hm) - (distinguished hm).

  (* Definition mark_kmap (b : B) (hm : hash_map B) := *)
  (*   mark_hash_kmap b (fresh hm) hm. *)

  Definition mark_kmap_2 (b : B) (hm : hash_map B) :=
    mark_hash_kmap_2 b (fresh hm) hm.

  Lemma mark_hash_kmap_bnodes (hm : hash_map B) :
    forall (b : B) (n : nat),
    b \in bnodes_hm hm ->
    bnodes_hm (mark_hash_kmap_2 b n hm) = bnodes_hm hm.
  Proof.
  move=> b n.
  rewrite /mark_hash_kmap_2.
  rewrite set_nthE.
  rewrite (hm_zip hm).
  set hm' := zip _ _.
  rewrite find_index_eq_bnode; last by apply size_proj.
  rewrite -index_mem size_map /bnodes_hm.
  have eq_size_proj : size [seq i.1 | i <- hm] = size [seq i.2 | i <- hm].
    by rewrite size_proj.
  rewrite zip_proj1 // {1}/hm' size_zip eq_size_proj minn_refl.
  move=> b_in; rewrite b_in.
  rewrite /= {}/hm' -(hm_zip hm).
  move: b_in {eq_size_proj}.
  elim: hm=> [//| hd tl IHtl] /=.
  case_eq (hd.1 == b).
  by move=> /eqP ->; rewrite /= eqxx /= drop0.
  by move=> -> /==> /IHtl ->.
  Qed.

  Lemma good_mark_kmap (g : seq (triple I B L)) (hm : hash_map B):
    bnodes_hm hm =i get_bts g ->
      forall b : B, b \in bnodes_hm hm -> bnodes_hm (mark_kmap_2 b hm) =i get_bts g.
  Proof.
  move=> mem_eq b bin.
  by rewrite mark_hash_kmap_bnodes //; apply mem_eq.
  Qed.

  (* Definition template_isocan__ := @template_isocan_
                                    init_hash_kmap good_init_kmap choose_part_kmap in_part_in_bnodes_kmap
                                    color_kmap color_refine_kmap color_good_hm_kmap color_refine_good_hm_kmap
                                    mark_kmap_2 good_mark_kmap M_kmap.

  Check template_isocan__. *)

  Lemma mark_size (b : B) (hm : hash_map B) :
    b \in (bnodes_hm hm) ->
    size (mark_kmap_2 b hm) = size hm.
  Proof.
  rewrite /mark_kmap_2/mark_hash_kmap_2.
  elim: hm (fresh hm)=> [//| hd tl IHtl] n.
  rewrite /= /mark_kmap_2/mark_hash_kmap_2. case: ifP=> [//|].
  rewrite in_cons /eq_bnode/pred_eq/==> -> /= in_tl.
  by rewrite IHtl.
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

  Lemma not_fine_chosen_part_in_P (hm : hash_map B):
    ~~ is_fine (gen_partition hm) -> choose_part_kmap hm \in gen_partition hm.
  Proof.
  move=> finePn'; rewrite /choose_part_kmap.
  have H'': has (predC (is_trivial (B:=B))) (gen_partition hm).
    by rewrite has_predC; exact: finePn'.
  by rewrite H''; apply mem_nth; rewrite -has_find.
  Qed.

  Lemma fresh_not_in_hashes (hm : hash_map B):
    fresh hm \notin (hashes_hm hm).
  Proof.
  rewrite /fresh.
  set s := hashes_hm hm.
  set max := foldl maxn 0 s.
  move: (foldl_max s 0); rewrite -/max=> [[max0|]].
  + suffices all0 : all (pred1 0) s.
      apply/memPn=> /= n nin; rewrite max0.
      by move: (in_all nin all0)=> /eqP ->.
    move/max_foldlP : max0=> /andP[_ ].
    move: s {max}=> s all_gt0.
    apply /allP=> /= n; rewrite -leqn0.
    by move: n; apply /allP.
  + rewrite /max{max}.
    elim: s 0=> [//| hd tl IHtl] n /=.
    set n' := maxn n hd.
    rewrite in_cons=> /orP[eq_hd|in_tl].
    - rewrite /negb in_cons (eqP eq_hd) gtn_eqF //=.
      move/eqP : eq_hd=> /max_foldlP/andP[_ all_gt_hd].
      suffices : all (<%O^~ hd.+1) tl.
        elim: tl {IHtl all_gt_hd}=> [//|hd2 tl2 IHtl2].
        by rewrite /= in_cons=> /andP[/gtn_eqF -> /IHtl2] /= ->.
      move: all_gt_hd.
      elim: tl{IHtl}=> [//| hd2 tl2 IHtl2].
      rewrite /= -nat_coq_le_nat -nat_coq_nat ltnS.
      by move=> /andP[-> /IHtl2 ->].
    - move: IHtl=> /(_ _ in_tl).
      rewrite /negb in_cons; case: ifP=> [//|_ _]; rewrite orbF.
      set N := foldl _ _ _.
      have /eqP/max_foldlP := eq_refl N.
      rewrite /n' -nat_coq_le_nat geq_max.
      move=> /andP[/andP[_ ]].
      case_eq (N.+1 == hd)=> [|//].
      by move=> /eqP <-; rewrite ltnn.
  Qed.

  Lemma mem_choose_part_kmap_mult1Pn (hm : hash_map B):
    ~~ is_fine (gen_partition hm) ->
     forall (bn : B * nat),
       bn \in choose_part_kmap hm ->
         ~~ mult1 (hashes_hm hm) bn.2.
  Proof.
  set p := choose_part_kmap hm.
  move=> finePn bn bn_inp.
  have all_eq_hash_p : all (eq_hash B bn.2) p.
    apply: (part_all_eq_hash_mem _ _ hm bn_inp _).
    by apply not_fine_chosen_part_in_P.
  suffices : size p > 1.
    rewrite /mult1/negb.
    move: all_eq_hash_p.
    rewrite all_count=> /eqP <-.
    have in_P : p \in gen_partition hm.
      by apply not_fine_chosen_part_in_P.
    by rewrite (mem_partP _ _ _ bn_inp in_P) -count_filter count_mult=> /gtn_eqF ->.
  suffices H''' : forall (T : eqType) (p : seq T), p != [::] -> (size p == 1) = false -> 1 < size p.
    apply H'''.
    - by rewrite /negb; rewrite choose_part_not_nil_kmap //.
    - have H'': has (predC (is_trivial (B:=B))) (gen_partition hm).
        by rewrite has_predC; exact: finePn.
      rewrite /p/choose_part_kmap H''.
      move : H''.
      set p' := nth _ _ _.
      by move=> /(nth_find [::]); rewrite /=/is_trivial/negb; case: ifP=> //.
  by move=> T [//| hd' [//|tl']] //.
  Qed.

  Lemma distinguished_mark (bn: B * nat) (hm : hash_map B):
    uniq (bnodes_hm hm) ->
    ~~ is_fine (gen_partition hm) ->
       bn \in choose_part_kmap hm ->
         distinguished hm < distinguished (mark_kmap_2 bn.1 hm).
  Proof.
  rewrite /mark_kmap_2=> ubs_hm finePn in_part.
  have fst_inj : {in hm &, injective fst}.
  by apply /in_map_injP => //; rewrite (hm_zip hm) zip_uniq_l //.
  have has_bn :  (find (eq_bnode B bn.1) hm < size (hashes_hm hm))%N.
  rewrite {1}(hm_zip hm) find_index_eq_bnode; last by apply size_proj.
  rewrite index_map_in //; last by apply in_part_in_bnodes_kmap.
  + rewrite size_map.
    by move/in_part_in_bnodes_kmap : in_part; rewrite index_mem.
    suffices H : forall (hm' : hash_map B),
    distinguished hm' = num_uniq_hash hm'.
    rewrite !H /num_uniq_hash.
    set hm' := mark_hash_kmap_2 _ _ _.
    set h1 := hashes_hm hm.
    set h2 := hashes_hm hm'.
    have -> : h2 = hashes_hm (set_nth (bn.1,(fresh hm)) hm (find (eq_bnode B bn.1) hm) (bn.1,(fresh hm))). by [].
    suffices -> :
      hashes_hm (set_nth (bn.1,(fresh hm))  hm             (find (eq_bnode B bn.1) hm) (bn.1,(fresh hm)))
      =          set_nth       (fresh hm)   (hashes_hm hm) (find (eq_bnode B bn.1) hm)       (fresh hm).
      (**  *)
     rewrite count_set_nth_ltn //.
     set h2' := set_nth _ _ _ _.
     rewrite -/h1.
     set n1 := count (mult1 h2') h1.
     set n2 := mult1 h2' (fresh hm).
     set bn1 := ((nth _ _ _):nat in X in _ < X).
     set n3 := mult1 h2' _.
     suffices -> : n2 = true.
       suffices subp :subpred (mult1 h1) (mult1 h2').
     case_eq n3.
         rewrite addnK=> n3T.
         rewrite /n1.
         have bn1_in : bn1 \in h1.
           by rewrite /bn1; apply mem_nth; rewrite has_bn.
         apply (lt_count_subpred _ _ subp)=> /=.
         exists bn1; apply /and3P;split=> //.
         suffices -> : bn1 = bn.2.
           by apply mem_choose_part_kmap_mult1Pn=> //.
           rewrite /bn1.
           suffices : nth (bn.1 ,fresh hm) hm (find (eq_bnode B bn.1) hm) = bn.
           rewrite {2}(hm_zip hm).
           rewrite nth_zip ?size_proj //.
           by case: bn {in_part hm' h2 has_bn h2' n1 n2 n3 subp n3T bn1 bn1_in} => bb nn [_ ->].
           rewrite {3}(hm_zip hm).
           rewrite find_index_eq_bnode ?size_proj //.
           suffices bn_in : bn \in hm.
           by rewrite index_map_in // nth_index.
           by apply in_part_in_bnodes_kmap.
           (** EO Proof depende on mem_choose_part_kmap_mult1Pn  *)

       move=> _.
       (* suffices -> : n3 = false. *)
         rewrite addn1 subn0.
         suffices leq : count (mult1 h1) h1 <= n1.
           by apply : (leq_ltn_trans leq (ltnSn _)).
         rewrite /n1 -/h1.
           by apply (sub_count subp).

           (** subpred *)
         move=>/= n; rewrite /mult1 /h1/h2'.
         set hs := hashes_hm hm.
         rewrite count_set_nth_ltn //.
         set n0 := pred1 n _.
         move=> /eqP eq; rewrite eq.
         set n0' := pred1 _ _.
         suffices -> : n0' = false.
           suffices -> : n0 = false.
             by rewrite eqxx.
           rewrite /n0.
             suffices nin : n \in hs.
               suffices /count_memPn : (fresh hm) \notin hs.
                 rewrite /=.
                 move: eq.
                 case_eq (fresh hm == n)=> [|//].
                 by rewrite eq_sym=> /eqP -> -> //.
               by apply fresh_not_in_hashes.
             by apply count_mem_1_in.
           rewrite /n0'.
           set b := nth _ _ _.
           suffices count_mem_b : count_mem b hs > 1.
             apply: negPf; apply (neq_count_mem hs).
             by apply /negPf; apply gtn_eqF; rewrite eq.
           set p := choose_part_kmap hm.
           have in_P: p \in gen_partition hm.
             by apply not_fine_chosen_part_in_P.
           suffices all_eqb_p : all (eq_hash B bn.2) p.
             suffices size_p_gt1 : size p > 1.
               suffices count_bn_gt1 : count (eq_hash B bn.2) hm > 1.
                 suffices eq_count : count (eq_hash B bn.2) hm = count_mem bn.2 (hashes_hm hm).
                   suffices -> : b = bn.2.
                     by rewrite -eq_count; apply count_bn_gt1.
                   rewrite /b.
                   suffices : nth (bn.1 ,fresh hm) hm (find (eq_bnode B bn.1) hm) = bn.
                     rewrite {2}(hm_zip hm).
                     rewrite nth_zip ?size_proj //.
                     by case: bn {in_part hm' h2 has_bn h2' n1 n2 n3 n0' b all_eqb_p count_bn_gt1 eq_count bn1} => bb nn [_ ->].
                   rewrite {3}(hm_zip hm).
                   rewrite find_index_eq_bnode ?size_proj //.
                   suffices bn_in : bn \in hm.
                     by rewrite index_map_in // nth_index.
                   by apply in_part_in_bnodes_kmap.
                 by rewrite count_mult.
               apply: (leq_trans size_p_gt1).
               suffices -> : size p = count (eq_hash B bn.2) p.
                 apply leq_count_subseq.
                 apply partition_memP.
                 by apply not_fine_chosen_part_in_P.
                 rewrite /p (mem_partP _ _ _ in_part in_P) /=.
                 by rewrite size_filter count_filter.
      suffices H''' : forall (T : eqType) (p : seq T), p != [::] -> (size p == 1) = false -> 1 < size p.
        apply H'''.
        - by rewrite /negb; rewrite choose_part_not_nil_kmap //.
        - have H'': has (predC (is_trivial (B:=B))) (gen_partition hm).
            by rewrite has_predC; exact: finePn.
          rewrite /p/choose_part_kmap H''.
          move : H''.
          set p' := nth _ _ _.
          by move=> /(nth_find [::]); rewrite /=/is_trivial/negb; case: ifP=> //.
        by move=> T [//| hd' [//|tl']] //.
        rewrite /p.
      by apply (part_all_eq_hash_mem _ _ _ in_part in_P).
      rewrite /n2/mult1.
      rewrite count_set_nth_ltn //= eqxx /=.
      (* EO subpred *)
      (**  *)
      rewrite /n3.
      rewrite /mult1.
      suffices fresh_nin : count_mem (fresh hm) (hashes_hm hm) = 0.
        have : (nth (fresh hm) (hashes_hm hm) (find (eq_bnode B bn.1) hm)) \in hashes_hm hm. by apply mem_nth.
          move=> /count_mem_inP nth_in.
          have /neq_count_mem/negPf : count_mem (fresh hm) h1 != count_mem (nth (fresh hm) h1 (find (eq_bnode B bn.1) hm)) h1.
            rewrite fresh_nin.
            apply /negPf.
            suffices /ltn_eqF -> : 0 < count_mem (nth (fresh hm) h1 (find (eq_bnode B bn.1) hm)) h1.
              by [].
            by apply: (leq_ltn_trans _ nth_in).
        by rewrite eq_sym=> -> ; rewrite subn0 fresh_nin add0n eqxx.
        by apply /count_memPn; apply fresh_not_in_hashes.
      set n0 := fresh hm.
      set b0 := bn.1.
      set i := find (eq_bnode B b0) hm.
      rewrite proj1_set_nth_prod //.
      by move: has_bn; rewrite size_map.
      apply num_triv_distinguished.
      Qed.

  Lemma markP_kmap (bn : B * nat) (hm : hash_map B) (ubns : uniq (bnodes_hm hm)):
    ~~ is_fine (gen_partition hm) -> bn \in choose_part_kmap hm
                                            -> M_kmap (mark_kmap_2 bn.1 hm) < M_kmap hm.
  Proof.
  rewrite /M_kmap/mark_kmap_2.
  set x := mark_hash_kmap_2 _ _ _.
  move=> finePn bn_in_choose.
  have bn1_in : bn.1 \in bnodes_hm hm.
    move/in_part_in_bnodes_kmap: bn_in_choose=> {x}.
    by case: bn=> b n; rewrite {1}(hm_zip hm)=> /in_zip/=/andP[->].
  have -> : size x = size hm.
    by rewrite mark_size.
  suffices : distinguished hm < distinguished x.
    move=> lt_dhm_dx.
    rewrite -nat_coq_nat ltn_sub2lE //.
    rewrite /distinguished.
    suffices le_part_size : count (is_trivial (B:=B)) (gen_partition x) <= size x.
      apply (leq_trans le_part_size).
      by rewrite mark_size // leqnn.
    suffices le_size_partition_x : (size (gen_partition x)) <= (size x).
      have leq_count_size : count (is_trivial (B:=B)) (gen_partition x) <= size (gen_partition x).
        by rewrite -nat_coq_le_nat; apply count_size.
      by apply (leq_trans leq_count_size le_size_partition_x).
    by apply size_gen_partition.
  by apply distinguished_mark.
  Qed.


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

  Lemma map_mu_mem_partition (T U: eqType) (s : seq (T * nat)) (s' : seq T) (s'' : seq nat) (f : T -> U):
    s \in gen_partition (zip s' s'') ->
          zip (map (f \o fst) s) (map snd s) \in gen_partition (zip (map f s') s'').
  Proof.
  elim: s'' s'=> [|hd tl IHtl] s'; first by case: s'; autorewrite with gen_partition.
  case: s'=> [|hd2 tl2] /=; autorewrite with gen_partition; first by [].
  rewrite in_cons.
  case_eq (s == (partitionate (hd2, hd).2 ((hd2, hd) :: zip tl2 tl)).1)=> H.
  + move/eqP: H=> -> _.
    rewrite /= /eq_hash/pred_eq eqxx /= in_cons /=.
    admit.
    rewrite /= /eq_hash/pred_eq eqxx /=.
    Admitted.

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
  admit.
  apply contraTT.
  move=> /allPn/=[p pin not_triv].
  apply /allPn=> /=.
  exists (zip (map (mu \o fst) p) (map snd p)).
  suffices <- : gen_partition (zip (map mu (get_bts g)) (nseq (size (map mu (get_bts g))) 0))
                =i gen_partition (zip (get_bts h) (nseq (size (get_bts h)) 0)).
    apply map_mu_mem_partition.
    by rewrite size_map.
  move/and3P: piso=> [_ _ piso].
  suffices mem_gen_part : forall (hm1 hm2 : hash_map B), perm_eq hm1 hm2 -> gen_partition hm1 =i gen_partition hm2.
    apply mem_gen_part.
    apply uniq_perm. apply zip_uniq_l.
    by rewrite (perm_uniq piso) uniq_get_bts.
    by apply: zip_uniq_l (uniq_get_bts _).
  suffices eq_mem_zip_nseq :
    forall (T : eqType) (s1 s2 : seq T) (n : nat), perm_eq s1 s2 -> zip s1 (nseq (size s1) n) =i zip s2 (nseq (size s1) n).
  move=> /= bn.
  have ->: (size (get_bts h)) = (size [seq mu i | i <- get_bts g]).
    by rewrite -(perm_size piso).
    apply eq_mem_zip_nseq.
    exact: piso.
  move=> T s1 s2 n peqq /= [b n'].
  apply /idP/idP.
  move=> /nthP/= /(_ (b,n)) [i iin].
  rewrite nth_zip. move=> <-.
  apply /(nthP (b,n)).
  exists (index (nth b s1 i) s2).
  rewrite size_zip size_nseq (perm_size peqq) minn_refl index_mem.
  rewrite -(perm_mem peqq).
  apply mem_nth.
  move: iin.
  by rewrite size_zip size_nseq minn_refl.
  set bnth := nth b _ _.
  rewrite nth_nseq.
  rewrite nth_zip.
  congr pair; last by rewrite nth_nseq; case: ifP; case: ifP.
  rewrite nth_index //.
  rewrite -(perm_mem peqq).
  apply mem_nth.
  move: iin.
  by rewrite size_zip size_nseq minn_refl.
  by rewrite size_nseq; apply perm_size; rewrite perm_sym.
  by rewrite size_nseq; apply perm_size.
  move=> /nthP/= /(_ (b,n)) [i iin].
  rewrite nth_zip. move=> <-.
  apply /(nthP (b,n)).
  exists (index (nth b s2 i) s1).
  rewrite size_zip size_nseq (perm_size peqq) minn_refl -(perm_size peqq) index_mem.
  rewrite (perm_mem peqq).
  apply mem_nth.
  move: iin.
  by rewrite size_zip size_nseq -(perm_size peqq) minn_refl.
  set bnth := nth b _ _.
  rewrite nth_nseq.
  rewrite nth_zip.
  congr pair; last by rewrite nth_nseq; case: ifP; case: ifP.
  rewrite nth_index //.
  rewrite (perm_mem peqq).
  apply mem_nth.
  move: iin.
  by rewrite size_zip size_nseq (perm_size peqq) minn_refl.
  by rewrite size_nseq; apply perm_size.
  by rewrite size_nseq; apply perm_size; rewrite perm_sym.
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














