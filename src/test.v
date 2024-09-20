From Equations Require Import Equations.
(* From HB Require Import structures. *)
From mathcomp Require Import all_ssreflect.
(* Set Implicit Arguments. *)
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Equations? foldl_In {T R : eqType} (s : seq T) (f : R -> forall (y : T), y \in s -> R) (z : R) : R :=
  foldl_In nil f z := z;
  foldl_In (a :: l) f z := foldl_In l (fun x y inP=> f x y _) (f z a _).
Proof.
  by rewrite in_cons inP orbT.
  by rewrite in_cons eqxx.
Qed.

Lemma foldl_foldl_eq {T R : eqType} (s : list T) (f : R -> T -> R) z :
  @foldl_In _ _ s (fun r t (_ : t \in s) => f r t) z = foldl f z s.
Proof.
  funelim (foldl_In s _ z).
  - by [].
  - autorewrite with foldl_In; apply H.
Qed.

Section ex.

  Variable M : nat -> nat.
  Hypothesis MP: forall n, M n < M (n.+1).

  Variable p : nat -> bool.

  Variable f : nat -> nat.
  Hypothesis fP : forall n, p n -> M (f n) < M n.

  Definition inspect {A} (a : A) : {b | a = b} := exist _ a erefl.
  Notation "x 'eqn:' p" := (exist _ x p) (only parsing, at level 20).

  Equations? ex (n : nat) : nat by wf (M n) lt :=
    ex O := O;
    ex (S n') with inspect (p n') => {
        ex (S n') (true eqn:pN) := ex (f n');
        ex (S n') (false eqn:npN) := ex n'}.
  Proof.
    - apply /ltP; eapply ltn_trans.
    by apply fP.
    by apply MP.
    - by apply /ltP; apply MP.
  Qed.

End ex.
