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

Lemma mem_filter_map (T : eqType) f p a (s : seq T) :
  (forall b, p b = p (f b)) -> (a \in (map f (filter p s))) = (a \in filter p (map f s)).
Proof. elim: s=> [//|h t IHts] pres.
       by case e: (p h); rewrite /= e; rewrite pres in e; rewrite e /= ?in_cons IHts //.
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

Lemma perm_map_cancel (T1 T2: eqType) (s : seq T1) (f: T1 -> T2) (g: T2 -> T1) :
  cancel f g -> perm_eq (map (g \o f) s) s.
Proof. move=> can. elim: s=>[//| h t IHts] /=. by rewrite can perm_cons IHts. Qed.

Lemma perm_map_in_cancel (T: eqType) (s : seq T) (f g: T -> T) :
  {in s, cancel f g} -> perm_eq (map (g \o f) s) s.
Proof. elim: s=>[//| h t IHts] /=.
       move=> can. rewrite can. rewrite perm_cons IHts //.
       move=> x y. rewrite can //. by rewrite in_cons y orbT. by rewrite in_cons eqxx.
Qed.

Lemma perm_undup_map_inj (T1 T2: eqType) (f : T1 -> T2) s1 s2 :
  {in s1 &,injective f} ->  uniq s1 -> perm_eq (undup (map f s1)) s2 -> perm_eq (map f s1) s2.
Proof. move=> injf ? peq.
       have equ: uniq (undup (map f s1)) = uniq (map f s1).
       by rewrite map_inj_in_uniq // undup_uniq.
       suffices eq : perm_eq (map f s1) (undup (map f s1)).
       by apply: perm_trans eq peq.
       apply uniq_perm.
       + by rewrite -equ undup_uniq.
       + by rewrite undup_uniq.
       + by move=> x; rewrite mem_undup.
Qed.

Open Scope order_scope.

Lemma max_foldlP:
  forall [disp : unit] [T : orderType disp] (l : seq T) (x y : T),
    (foldl Order.max x l) = y -> (x <= y) && all (fun z=> z <= y) l.
Proof. move=> d T l x y.
       elim: l x=> [z /= -> //| hd t IHt]; first by rewrite Order.POrderTheory.lexx.
       move=> x. rewrite /= Order.POrderTheory.maxEle.
       case e: (x <= hd); move=> /IHt/andP[hdmax ->]; rewrite hdmax !andbT /=.
       + by apply (Order.POrderTheory.le_le_trans e hdmax (Order.POrderTheory.lexx _)).
       + rewrite Order.TotalTheory.leNgt /= Bool.negb_false_iff in e.
         by apply (Order.POrderTheory.le_le_trans (Order.POrderTheory.ltW e) hdmax (Order.POrderTheory.lexx _)).
Qed.

Lemma max_foldl_minimum:
  forall [disp : unit] [T : porderType disp] (l : seq T) (x : T),
    (forall y, x <= y) -> foldl Order.max x l = x -> ((l == [::]) || (x \in l)).
Proof. move=> d T l x minimum.
       elim: l=> [//| hd t IHt].
       rewrite /= Order.POrderTheory.maxEle minimum.
       case: (foldl_max t hd).
       by move=> -> ->; rewrite in_cons eqxx.
       by move=> H <-; rewrite in_cons H orbT.
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
  + case: ss uniq_ss => [| s ss]; first by rewrite zip0s.
    rewrite /==> /andP[nin_ss uniq_ss]; apply /andP; split; first by apply (notin_zip_l _ _ nin_ss).
    by apply: IHts uniq_ss.
Qed.

Lemma zip_uniq_r (S T : eqType) (ss : seq S) (ts : seq T) : uniq ts -> uniq (zip ss ts).
Proof.
  by rewrite zip_uniq_sym; apply zip_uniq_l.
Qed.

Lemma all_zip1 (T1 T2: Type) (s1: seq T1) (s2 : seq T2) p : all p s1 -> all (fun t=> p t.1) (zip s1 s2).
Proof. elim: s1 s2=> [|hd tl IHtl] s2; first by case s2.
       + move=> /andP[phd ptl] /=. case: s2=> //= b btl.
         by rewrite phd /= IHtl.
Qed.

Lemma all_zip_sym (T1 T2 : Type) (s1: seq T1) (s2 : seq T2) p :
  all (fun t=> p t.1) (zip s1 s2) = all (fun t => p t.2) (zip s2 s1).
Proof. by apply /idP/idP; elim: s1 s2=> [| x s IHs] [| y t]//= /andP[-> ts2] /=; rewrite IHs. Qed.

Lemma all_zip2 (T1 T2: Type) (s1: seq T1) (s2 : seq T2) p : all p s2 -> all (fun t=> p t.2) (zip s1 s2).
Proof. by move=> allp2; rewrite -all_zip_sym all_zip1. Qed.

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

Lemma neq_funapp (T1 T2: eqType) (f: T1 -> T2) : forall t t', f t != f t' -> t != t'.
Proof. by move=> t t'; apply contraPneq=> ->; rewrite eqxx. Qed.

Lemma neq_funapp_inj (T1 T2: eqType) (f: T1 -> T2) : injective f -> forall t t', t != t' -> f t != f t'.
Proof. by move=> inj_f t t'; apply contraPneq=> /inj_f ->; rewrite eqxx. Qed.

Lemma neq_funapp_inj_in (T1 T2: eqType) (f: T1 -> T2) (s : seq T1) :
  {in s&, injective f} -> forall t t', t \in s -> t' \in s -> t != t' -> f t != f t'.
Proof. by move=> inj_f t t' tin t'in; apply contraPneq=> /inj_f -> //; rewrite eqxx. Qed.

Lemma pmapP (T1 T2 : eqType) (f : T1 -> option T2) (s : seq T1) (y : T2):
  reflect (exists2 x : T1, x \in s & Some y = f x) (y \in pmap f s).
Proof. by rewrite mem_pmap; apply mapP. Qed.

Lemma sub_pmap (T1 T2: eqType) (s1 s2: seq T1) (f: T1 -> option T2) :
  {subset s1 <= s2} -> {subset pmap f s1 <= pmap f s2}.
Proof. by move=> sub_s y /pmapP [x x_s]; rewrite mem_pmap=> ->; rewrite map_f ?sub_s. Qed.

Lemma eq_mem_pmap (T1 T2 : eqType) (f : T1 -> option T2) (s1 s2 : seq T1):
  s1 =i s2 -> pmap f s1 =i pmap f s2.
Proof. by move=> Es x; apply /idP/idP; apply sub_pmap=> ?; rewrite Es. Qed.

Lemma uniq_neq_nth (T: eqType) (s : seq T) n m x0 x1:
  uniq s -> n < (size s) -> m < (size s) -> n != m -> nth x0 s n != nth x1 s m.
Proof. move/uniqP=> /(_ x1) us nin min.
       by rewrite (set_nth_default x1) //; apply contra_neq=> /us ->.
Qed.

Lemma in_map_injPn (T1 : eqType) (T2 : eqType) (s : seq T1) (f : T1 -> T2) (us: uniq s):
  reflect (exists2 x, x \in s & exists2 y, (y != x) && (y \in s) & f x = f y) (negb (uniq (map f s))).
Proof.
  apply: (iffP idP) => [injf | [x Dx [y Dxy eqfxy]]]; last first.
  move: (rot_to Dx)=>[i E defE].
  rewrite /dinjectiveb -(rot_uniq i) -map_rot defE /=; apply/nandP; left.
  rewrite eqfxy.
  rewrite map_f //.
  suffices : y \in x :: E.
  rewrite in_cons. case/orP=> //. by move: Dxy; rewrite /negb; case (y == x).
  by rewrite -defE mem_rot; move: Dxy=> /andP[_ ->].
  wlog s1 :/ T1.
  by case: s us injf=> // hd tl us injf hwlog; apply hwlog.
  move : injf=> /uniqPn p.
  have s0 := f s1.
  have [i [j [ijle [jsize [ntheq]]]]]:= p s0.
  exists (nth s1 s i). apply mem_nth. rewrite size_map in jsize.
  apply: ltn_trans ijle jsize.
  exists (nth s1 s j). apply /andP; split.
  apply uniq_neq_nth=> //.
  by rewrite size_map in jsize.
  by rewrite size_map in jsize; apply: ltn_trans ijle jsize.
  rewrite Order.NatOrder.ltn_def in ijle.
  by move/andP : ijle=> [].
  by apply mem_nth; rewrite size_map in jsize.
  erewrite <- nth_map.
  suffices <-: nth s0 [seq f i | i <- s] j = f (nth s1 s j).
  by apply ntheq.
  by apply nth_map; rewrite size_map in jsize.
  by rewrite size_map in jsize; apply: ltn_trans ijle jsize.
Qed.

Lemma in_map_injP (T1 : eqType) (T2 : eqType) (s : seq T1) (f : T1 -> T2) (us: uniq s):
  reflect {in s&, injective f} (uniq (map f s)).
Proof. rewrite -[uniq (map f s)]negbK.
       case: in_map_injPn=> // [noinjf | injf]; constructor.
         case: noinjf => x Dx [y /andP[neqxy /= Dy] eqfxy] injf.
         by case/eqP: neqxy; apply: injf.
       move=> x y Dx Dy /= eqfxy; apply/eqP; apply/idPn=> nxy; case: injf.
       by exists x => //; exists y => //=; rewrite /= eq_sym nxy.
Qed.
