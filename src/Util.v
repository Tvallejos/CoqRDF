From mathcomp Require Import all_ssreflect fingraph.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Several problems here:
- why naming a hypothesis if you generalize it right away)
- think about the statement of the lemma (here equality/equivalence holds, not only implication)
- use lemmas in the library (no need for induction here)
*)

Lemma all_undup (T : eqType) (s : seq T) p : all p (undup s) = all p s.
Proof.
  suffices /eq_all_r -> : (undup s) =i s by [].
  exact: mem_undup.
Qed.

Lemma inweak (T: eqType) (l:seq T) t u : t \in l -> t \in (u::l).
Proof.
  by rewrite -!has_pred1 /has; case (pred1 t u)=> [//| -> ].
Qed.

Definition undup_in (T : eqType) (t : T) (s : seq T) :
  t \in s -> t \in undup s.
Proof. elim: s=> [//| h hs IHts].
       + rewrite in_cons. case orP; last by [].
         case=> [ /eqP <- | ih] _.
       - destruct (t \in hs) eqn:E; rewrite /undup E.
         * by apply IHts.
         * by rewrite mem_head.
       - destruct (h \in hs) eqn:E;rewrite /undup E.
         apply: IHts ih.
         apply: inweak. apply: IHts ih.
Qed.

Definition undup_idem (T : eqType) (s : seq T) :
  undup (undup s) = undup s.
Proof. elim: s=> [//| t ts IHts] /=.
       destruct (t \in ts) eqn:E.
       + apply IHts.
       + have h: (t \in (undup ts) = false).
         by rewrite -E; apply mem_undup.
         by rewrite /= h IHts.
Qed.

Definition undup_cat_r (T: eqType) (s q : seq T) :
  undup (s ++ undup q) = undup (s ++ q).
Proof.
  elim: s=> [//| aq qs IHqs] /=.
  + apply undup_idem.
  + destruct (aq \in qs) eqn:E; rewrite !mem_cat E /=.
  - apply IHqs.
  - destruct (aq \in q) eqn:E2.
    have -> : (aq \in undup q) = true. rewrite -E2; apply mem_undup.
    apply IHqs.
    have -> : (aq \in undup q) = false. rewrite -E2; apply mem_undup.
    rewrite IHqs; done.
Qed.

Definition undup_cat_l (T: eqType) (s q : seq T) :
  undup (undup s ++ q) = undup (s ++ q).
Proof.
  elim: s=> [//| aq qs IHqs]; rewrite (undup_cat (aq :: qs)) /=.
  case e: (aq \in qs).
  + by rewrite IHqs undup_cat.
  + by rewrite undup_cat -cat1s undup_cat_r !cat1s {1}/undup e.
Qed.

Lemma empty_permutations (T:eqType) : @permutations T [::] = [:: [::]]. Proof. by []. Qed.

Lemma map_inv (T U: eqType) (s:seq T) (f: T -> U):
  forall (u: U), u \in map f s -> exists t, u = (f t).
Proof. elim : s => [| a t IHts] u /=; first by rewrite in_nil.
       rewrite in_cons; case/orP => [/eqP -> | y].
       - by exists a.
       - by apply: IHts; apply y.
Qed.

Lemma foldl_op (disp: unit) (T: porderType disp) (l: seq T) (x0 : T) : foldl Order.min x0 l = x0 \/ foldl Order.min x0 l \in l.
Proof. elim: l x0 => [ | t ts IHts] x0 /=.
       + by left.
       + rewrite in_cons; case: (IHts (Order.min x0 t))=> [ -> |intail] /=.
       - rewrite Order.POrderTheory.minEle; case: ifP=> _.
         * by left.
         * by right; rewrite eqxx.
       - by right; rewrite intail orbT.
Qed.

Definition build_finfun (T : choiceType) (f : T -> T) (s : seq T) : (seq_sub s) -> T :=
  fun ssub => f (ssval ssub).


Remark zip0s (S T : Type) (s:seq T) : zip (@nil S) s = [::]. by case s. Qed.
Remark zips0 (S T : Type) (s:seq S) : zip s (@nil T) = [::]. by case s. Qed.

Lemma in_zip (S T : eqType) (ss : seq S) (ts : seq T) s t:
  (s,t) \in zip ss ts -> (s \in ss) /\ (t \in ts).
Proof.
  move: t s. elim : ts ss. rewrite /==> ss; by case ss.
  + move=> t' ts' IHts ss t s.
    case: ss; first done.
    move=> s' ss' in_zip; rewrite !in_cons.
    rewrite /= in_cons in in_zip; split;
      move: in_zip; case/orP;
      last by move=> in_zip; apply/orP; right; apply (IHts _ _ _ in_zip).
    by rewrite xpair_eqE=> /andP [seq teq]; apply /orP; left; exact: seq.
    (* room for improve *)
    by move=> in_zip; apply/orP; right; apply (IHts _ _ _ in_zip).
    (* room for improve *)
    by rewrite xpair_eqE=> /andP [seq teq]; apply /orP; left; exact: teq.
Qed.

Lemma notin_zip (S T: eqType) (ss: seq S) (ts : seq T) s t :
  s \notin ss -> (s,t) \notin zip ss ts.
Proof.
  rewrite /negb. case e: (s \in ss); first done.
  case e2: ((s, t) \in zip ss ts); last done.
  by apply in_zip in e2; move: e2=> [/eqP/eqP  contr _]; rewrite contr in e; done.
Qed.

Lemma zip_uniq (S T : eqType) (ss : seq S) (ts : seq T) : uniq ss -> uniq ts -> uniq (zip ss ts).
Proof.
  elim: ts ss=> [| hd2 tl2 IHtl2] ss uniq_ss uniq_ts; first by case ss.
  + case: ss uniq_ss => [| s ss']; first by rewrite zip0s.
    move=> uniq_ss; rewrite /=; apply /andP; split.
    move: uniq_ss=> /==> /andP [nin_ss' _]; apply (notin_zip _ _ nin_ss').
    apply: IHtl2;
      move: uniq_ss => /==> /andP [_ uniq_ss]. exact: uniq_ss. (* why I can not connect using ;?*)
    move: uniq_ts => /==> /andP [_ uniq_ts]. exact: uniq_ts.
Qed.
