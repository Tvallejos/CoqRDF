From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Inductive nat : Type :=
| O
| S : nat -> nat.

Fixpoint add n m :=
  match n with
  | O => m
  | S n' => add n' (S m)
  end.

Theorem addO_n : forall (n : nat), add O n = n.
Proof. by []. Qed.

Check addO_n.

Fixpoint eqb_nat n m:=
 match n,m with
 | O,O => true
 | S n', S m' => eqb_nat n' m'
 | _, _ => false
 end.

Inductive opt (A : Type) :=
| Non
| Som : A -> opt A.

 Lemma nat_eqax : Equality.axiom eqb_nat.
 Proof. move=> n.
 elim: n=> [| n' IHn] [| m'].
   + by apply Bool.ReflectT.
  + by apply Bool.ReflectF.
  + by apply Bool.ReflectF.
  + by move=> /=; apply: (equivP (IHn m') _); split=> [->|[->]].
Qed.


Definition nat_eqType := EqType nat (EqMixin nat_eqax).
Canonical nat_eqType.

Variables n m : nat.
Check n == m.

Lemma eqb_nat_trans (n m l : nat) : eqb_nat n m -> eqb_nat m l -> eqb_nat n l.
Proof. by move/eqP=> ->. Qed.

Variable is_prime : nat -> bool.

Record prime : Type := mkPrime {
  p :> nat;
  p_prime : is_prime p
                         }.

Lemma prime_inj (p1 p2 : prime) :
  p p1 = p p2 ->
  p1 = p2.
Proof. case p1; case p2=> prime1 prime1P prime2 prime2P /= eq.
subst; congr mkPrime. 
by apply eq_irrelevance.
Qed.

Check eq_irrelevance.

Definition code (p : prime) : nat :=
  p.

Definition decode (n : nat) : option prime :=
  if insub n : {? x | is_prime x} is Some nn
  then Some (mkPrime (valP nn))
  else None.

Lemma pcancel_code_decode : pcancel code decode.
Proof.
  case=> p pP /=; rewrite /decode.
  case: insubP => [? ? ?|].
  by congr Some; apply prime_inj.
  by rewrite pP.
Qed.

Definition prime_canEqMixin := PcanEqMixin pcancel_code_decode.

Canonical prime_eqType :=
  Eval hnf in EqType prime prime_canEqMixin.


Section inj.

Inductive I : Type :=
| K.

Variable p : I -> bool.
Record r := mkR {
  i : I;
  iP: p i
}.

Lemma i_inj I1 I2: i I1 = i I2 ->
  I1 = I2.
Proof. case I1; case I2=> i1 iP1 i2 iP2 /= eq.
subst; congr mkR. exact: eq_irrelevance.
Qed.

End inj.
