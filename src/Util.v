From mathcomp Require Import all_ssreflect fingraph.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma all_undup (T : eqType) (s : seq T) p : all p (undup s) = all p s.
Proof.
  suffices /eq_all_r -> : (undup s) =i s by [].
  exact: mem_undup.
Qed.

Lemma inweak (T: eqType) (l:seq T) t u : t \in l -> t \in (u::l).
Proof. by rewrite -!has_pred1 /has; case (pred1 t u)=> [//| -> ]. Qed.

Definition undup_in (T : eqType) (t : T) (s : seq T) :
  t \in s -> t \in undup s.
Proof. elim: s=> [//| h hs IHts].
       + rewrite /= in_cons. case/orP.
       - move=> /eqP<-; case e: (t \in hs) IHts; first by move=>->.
         by rewrite mem_head.
       - case e: (h \in hs); first by apply IHts.
         move=> /IHts tin_hs; apply: inweak tin_hs.
Qed.

Definition undup_idem (T : eqType) (s : seq T) :
  undup (undup s) = undup s.
Proof.
  elim: s=> [//| t ts IHts] /=.
  by case e: (t \in ts); rewrite // /= mem_undup e IHts.
Qed.

Definition undup_cat_r (T: eqType) (s q : seq T) :
  undup (s ++ undup q) = undup (s ++ q).
Proof.
  elim: s=> [//| aq qs IHqs] /=; first exact: undup_idem.
  by rewrite !mem_cat mem_undup IHqs.
Qed.

Definition undup_cat_l (T: eqType) (s q : seq T) :
  undup (undup s ++ q) = undup (s ++ q).
Proof.
  by rewrite !undup_cat undup_idem.
Qed.

Lemma empty_permutations (T:eqType) : @permutations T [::] = [:: [::]]. Proof. by []. Qed.

Lemma map_inv (T U: eqType) (s:seq T) (f: T -> U):
  forall (u: U), u \in map f s -> exists t, u = (f t).
Proof. elim : s => [| a t IHts] u /=; first by rewrite in_nil.
       + rewrite in_cons; case/orP => [/eqP -> | y].
         by exists a.
                   - by apply: IHts y.
Qed.

Lemma foldl_min (disp: unit) (T: porderType disp) (l: seq T) (x0 : T) :
  foldl Order.min x0 l = x0 \/ foldl Order.min x0 l \in l.
Proof. elim: l x0 => [ | t ts IHts] x0; first by left.
       + rewrite in_cons /=; case: (IHts (Order.min x0 t))=> [ -> |intail] /=.
       - rewrite Order.POrderTheory.minEle; case: ifP=> _; first by left.
         * by right; rewrite eqxx.
       - by right; rewrite intail orbT.
Qed.

Lemma min_seq (disp : unit) (T: orderType disp) (s: seq T) (hd:T) :
  exists (minimum: T), forall (t: T), t \in (hd::s) -> (<=%O minimum t).
Proof. elim: (hd::s)=> [| a t [minimum IHts]]; first by exists hd=> t; rewrite in_nil.
                                                               + case e: (<=%O minimum a); [exists minimum | exists a]
                                                                      => a0; rewrite in_cons; case/orP=> [/eqP ->| /IHts ain] //.
                                                               - have /Order.POrderTheory.ltW amin: (<%O a minimum). admit.
                                                                 apply (Order.POrderTheory.le_trans amin ain).
Admitted.

Lemma foldl_max (disp: unit) (T: porderType disp) (l: seq T) (x0 : T) :
  foldl Order.max x0 l = x0 \/ foldl Order.max x0 l \in l.
Proof. elim: l x0 => [ | t ts IHts] x0; first by left.
       + rewrite in_cons /=; case: (IHts (Order.max x0 t))=> [ -> |intail] /=.
       - rewrite Order.POrderTheory.maxEle; case: ifP=> _; first by right; rewrite eqxx.
         * by left.
       - by right; rewrite intail orbT.
Qed.

Definition build_finfun (T : choiceType) (f : T -> T) (s : seq T) : (seq_sub s) -> T :=
  fun ssub => f (ssval ssub).

Remark zip0s (S T : Type) (s:seq T) : zip (@nil S) s = [::]. by case s. Qed.
Remark zips0 (S T : Type) (s:seq S) : zip s (@nil T) = [::]. by case s. Qed.

Lemma in_zip (S T : eqType) (ss : seq S) (ts : seq T) s t:
  (s,t) \in zip ss ts -> (s \in ss) && (t \in ts).
Proof.
  elim : ts ss t s=> [|t' ts' IHts] /= ss t s; first by case: ss; rewrite in_nil.
  + case: ss=> [//|s' ss'].
    rewrite in_cons; case/orP; first by rewrite !in_cons xpair_eqE=> /andP [-> ->].
    by rewrite in_cons=> /IHts/andP [-> ->]; rewrite !Bool.orb_true_r.
Qed.

Lemma in_zip_sym (S T : eqType) (ss : seq S) (ts : seq T) s t:
  (s,t) \in zip ss ts = ((t, s) \in zip ts ss).
Proof.
  elim: ts ss=> [[//|//]| t' ts' IHts] ss.
  + case: ss=> [| s' ss']; first by rewrite zip0s.
  - rewrite /= !in_cons. f_equal; first by rewrite !xpair_eqE Bool.andb_comm.
    by rewrite IHts.
Qed.

Lemma notin_zip_l (S T: eqType) (ss: seq S) (ts : seq T) s t :
  s \notin ss -> (s,t) \notin zip ss ts.
Proof.
  rewrite /negb.
  by case e: (s \in ss); case e2: ((s, t) \in zip ss ts); move: e2=> // /in_zip; rewrite e.
Qed.

Lemma notin_zip_r (S T: eqType) (ss: seq S) (ts : seq T) s t :
  t \notin ts -> (s,t) \notin zip ss ts.
Proof.
  by rewrite in_zip_sym; apply notin_zip_l.
Qed.

Lemma zip_uniq_sym (S T : eqType) (ss : seq S) (ts : seq T) : uniq (zip ss ts) = uniq (zip ts ss).
Proof.
  elim: ts ss=> [[//|//]| t ts' IHts] ss.
  + case: ss => [| s ss' /=]; first by rewrite zip0s.
  - f_equal; last by apply IHts.
    by rewrite in_zip_sym.
Qed.

Lemma zip_uniq_l (S T : eqType) (ss : seq S) (ts : seq T) : uniq ss -> uniq (zip ss ts).
Proof.
  elim: ts ss=> [[//|//]| t' ts' IHts] ss uniq_ss.
  + case: ss uniq_ss => [| s ss']; first by rewrite zip0s.
    rewrite /==> /andP[nin_ss uniq_ss]; apply /andP; split; first by apply (notin_zip_l _ _ nin_ss).
    by apply: IHts uniq_ss.
Qed.

Lemma zip_uniq_r (S T : eqType) (ss : seq S) (ts : seq T) : uniq ts -> uniq (zip ss ts).
Proof.
  by rewrite zip_uniq_sym; apply zip_uniq_l.
Qed.

Lemma uniq_zip_iota (T : eqType) (s: seq T) n m: uniq (zip s (iota n m)).
Proof. by apply: zip_uniq_r _ (iota_uniq _ _). Qed.

Lemma uniq_zip_map (T U V: eqType) (s: seq T) (u: seq U)
  (f : (T*U) -> V) (injF: injective f) : uniq (zip s u) -> uniq (map f (zip s u)).
Proof. by rewrite (map_inj_uniq injF). Qed.

Lemma in_all (T : eqType) (s : seq T) t f : t \in s -> all f s -> f t.
Proof. elim: s=> [| hd tl IHtl]; first by rewrite in_nil.
       by rewrite in_cons; case/orP=> [/eqP->/andP [//]| /IHtl _/andP[//]].
Qed.

Lemma size_0_nil (T : Type) (s : seq T) : size s = 0 -> s = [::].
Proof. by case s. Qed.

Lemma seq1_empty_seq (A : Type) (hd:A) d s : hd :: s = [:: d] -> s = [::].
Proof. by case s. Qed.
