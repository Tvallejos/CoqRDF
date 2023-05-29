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

Lemma undup_in (T : eqType) (t : T) (s : seq T) :
  t \in s -> t \in undup s.
Proof. elim: s=> [//| h hs IHts].
       + rewrite /= in_cons. case/orP.
       - move=> /eqP<-; case e: (t \in hs) IHts; first by move=>->.
         by rewrite mem_head.
       - case e: (h \in hs); first by apply IHts.
         move=> /IHts tin_hs; apply: inweak tin_hs.
Qed.

Lemma undup_idem (T : eqType) (s : seq T) :
  undup (undup s) = undup s.
Proof.
  elim: s=> [//| t ts IHts] /=.
  by case e: (t \in ts); rewrite // /= mem_undup e IHts.
Qed.

Lemma map_undup_idem (T1 T2: eqType) (f : T1 -> T2) (s : seq T1):
  map f (undup (undup s)) = map f (undup s).
Proof. elim: s=> [//|h t IHts] /=.
       case e: (h \in t); first by rewrite IHts.
       by move: e; rewrite -mem_undup /= -IHts=> ->.
Qed.

Lemma undup_cat_r (T: eqType) (s q : seq T) :
  undup (s ++ undup q) = undup (s ++ q).
Proof.
  elim: s=> [//| aq qs IHqs] /=; first exact: undup_idem.
  by rewrite !mem_cat mem_undup IHqs.
Qed.

Lemma undup_cat_l (T: eqType) (s q : seq T) :
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

Lemma sizeO_filter T (s : seq T) p: size (filter p s) == 0 = all (negb \o p) s.
Proof. by elim s=> //= h t <-; case (p h). Qed.

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

Definition map_fintype (T U: eqType) (s : seq T) (f : T -> U) (arg : seq_sub s) : seq_sub (map f s).
Proof. suffices: f (ssval arg) \in (map f s). by apply SeqSub.
       by apply (map_f f); apply (ssvalP arg).
Qed.

Definition is_some {T : Type} (ot : option T) : bool :=
  match ot with Some _ => true | None => false end.

Fixpoint someT_to_T {T : Type} (os : seq (option T)) : seq T :=
  match os with
  | nil => nil
  | Some t :: oss => t :: someT_to_T oss
  | None :: oss => someT_to_T oss
  end.

Fixpoint app_n (T: Type)(f : T -> T) (x : T) (n:nat) :=
  match n with
  | O => x
  | S n' => f (app_n f x n')
  end.

Definition mapi {A B : Type} (f : A -> nat ->  B) (s : seq A) : seq B :=
  map (fun an => (f an.1) an.2) (zip s (iota 0 (size s))).

Definition fun_to_fin (T : eqType) (s : seq T) (f : T -> T) : seq_sub s -> T:=
  fun s0=> let (ssval,_) := s0 in (f ssval).

Lemma eq_to_fin (T: eqType) (ft ft' : finType)
  (f : T -> T) (injF: injective f)
  (funt : ft -> T) (injFt: injective funt)
  (funt' : T -> ft') (injFt' : injective funt')
  : exists (f'' : ft -> ft'), injective f''.
Proof. exists (fun argT => (funt' (f (funt argT)))).
       by apply: (inj_comp injFt') (inj_comp injF injFt).
Qed.

Lemma max_sym disp (T: orderType disp) : symmetric Order.max.
Proof. by move=> x y; rewrite Order.POrderTheory.maxEle Order.POrderTheory.maxElt Order.TotalTheory.leNgt; case: (y < x)%O.
Qed.

Lemma min_sym : symmetric Order.min.
Proof. by move=> x y; rewrite Order.POrderTheory.minEle Order.POrderTheory.minElt Order.TotalTheory.leNgt; case: (y < x)%O.
Qed.

Lemma max_distr_foldl disp (T: porderType disp) (l : seq T) (x y : T) :
  foldl Order.max (Order.max x y) l = Order.max y (foldl Order.max x l).
Proof. elim: l=> [//| hd t IHt] /=.
       (*  Error: The LHS of Order.TotalTheory.leNgt *)
       (* (_ <= _) *)
       (* does not match any subterm of the goal *)
       (* rewrite Order.POrderTheory.maxEle Order.POrderTheory.maxElt Order.TotalTheory.leNgt; case: (y < x). *)
       (* Error: The LHS of max_sym *)
       (*     (Order.max _ _) *)
       (* does not match any subterm of the goal *)
       (* rewrite max_sym. *)
Admitted.

Lemma foldl_foldl_max disp (T: orderType disp) (l : seq T) (x0 : T) :
  foldl Order.max x0 l == foldr Order.max x0 l.
Proof. elim: l x0=> [//| hd t IHt] x0 /=.
       have <- :  ((foldl Order.max x0 t) = (foldr Order.max x0 t)). by apply /eqP; apply IHt.
       by rewrite max_distr_foldl.
Qed.

Lemma has_not_default T (s : seq T) p :
  has p s -> forall x0 x1,  nth x0 s (find p s) = nth x1 s (find p s).
Proof. elim: s=> [//| hd tl IHtl] /= hps x1.
       by case/orP: hps=> [-> //| /IHtl hptl]; case: (p hd)=> //; apply hptl.
Qed.

Lemma perm_map_comp (T1 T2 T3 : eqType) (f: T1 -> T2) (g : T2 -> T3) s1 s2 s3 :
  perm_eq (map f s1) s2 ->
  perm_eq (map g s2) s3 ->
  perm_eq (map (g \o f) s1) s3.
Proof. by move=> /(perm_map g); rewrite -map_comp; apply perm_trans. Qed.

Lemma can_in_pcan_in (T1 T2 : eqType) (f : T1 -> T2) (g : T2 -> T1) (s : seq T2): {in s, cancel g f} -> {in s, pcancel g (fun y => Some (f y))}.
Proof. by move=> can y yin; congr (Some _); apply can. Qed.

Lemma pcan_in_inj (T1 T2 : eqType) (f : T1 -> T2) (g : T2 -> option T1) (s : seq T1) :
  {in s, pcancel f g} -> {in s &, injective f}.
Proof. by move=> fK x y xin yin=> /(congr1 g); rewrite !fK // => [[]]. Qed.

Lemma inj_in_inamp (T1 T2 : eqType) (f : T1 -> T2) (s : seq T1): {in s, injective f} -> {in s &, injective f}.
Proof. by move=> injf x y xin /injf H /eqP; rewrite eq_sym=> /eqP/H ->. Qed.

Lemma can_in_inj (T1 T2 : eqType) (f : T1 -> T2) (g : T2 -> T1) (s : seq T1) : {in s, cancel f g} -> {in s &, injective f}.
Proof. move/can_in_pcan_in. move=> pcan. eapply pcan_in_inj. exact: pcan. Qed.
(* from coq ssr ssrfun *)


Lemma mem_in_map (T1 T2 : eqType) (f : T1 -> T2) (s : seq T1) : {in s, injective f} -> forall (x : T1), (f x \in [seq f i | i <- s]) = (x \in s).
Proof. move=> H x. apply /mapP/idP; last by exists x.
                                             by move=> [y yin] /eqP; rewrite eq_sym=> /eqP/H <-.
Qed.

Lemma map_nil_is_nil (A C: eqType) (f : A -> C) (s : seq A) : (map f s == [::]) = (s == [::]).
Proof. by case s. Qed.

Lemma mem_eq_is_nil (A : eqType) (s : seq A) : s =i [::] -> s = [::].
Proof. case: s=> [// | h t] H.
       + have: h \in [::]. rewrite -H in_cons eqxx //.
         by rewrite in_nil.
Qed.

Lemma perm_eq_nil_cons (T: eqType) t (s : seq T) : perm_eq [::] (t :: s) = false.
Proof. by rewrite /perm_eq /= eqxx. Qed.

Lemma mem_cons (T : eqType) (x y : T) (s : seq T) : x \in s -> x \in y :: s.
Proof. by rewrite in_cons orbC=> ->. Qed.

Lemma mem_map_undup (T1 T2 : eqType) (f : T1 -> T2) (s : seq T1):
  map f s =i map f (undup s).
Proof. elim: s=> [//| h t IHl].
       case e: (h \in t)=> x /=.
       have ->: (x \in f h :: [seq f i | i <- t]) = (x \in [seq f i | i <- t]).
       by rewrite -mem_undup /= ; rewrite map_f // mem_undup.
       by rewrite e -IHl.
       by rewrite e !in_cons -IHl.
Qed.
