From Coq Require Import Init.Nat.
From Coq Require Import Strings.String.
From Coq Require Import Arith.EqNat.

Definition eqb_string (x y : string) : bool :=
  if string_dec x y then true else false.

 (* literals should be of Datatype type, is not important for the moment*)
Inductive term : Type :=
  | Iri (id: string)
  | Lit (l : nat)
  | Bnode (name : string).

Definition is_lit (n : term) : bool :=
  (match n with
   | Lit _ => true
   | _ => false
   end).

Definition is_iri (n : term) : bool :=
  (match n with
   | Iri _ => true
   | _ => false
   end).

Definition is_bnode (n : term) : bool :=
  (match n with
   | Bnode _ => true
   | _ => false
   end).

Definition eqb_term (n1 n2 : term) : bool :=
  (match n1, n2 with
   | (Iri id), (Iri id2) => eqb id id2
   | (Lit l),(Lit l2) => l =? l2
   | (Bnode b),(Bnode b2) => eqb b b2
   | _,_ => false
   end).

Theorem eq_nat_eq_lit : forall (n1 n2:nat) , (n1 = n2) <-> (Lit n1) = (Lit n2).
Proof. split; intros H.
  - rewrite H. reflexivity.
  - injection H as H2. apply H2.
Qed.

Theorem eq_string_eq_iri : forall (s1 s2:string) , (s1 = s2) <-> (Iri s1) = (Iri s2).
Proof. split; intros H.
  - rewrite H. reflexivity.
  - injection H as H2. apply H2.
Qed.

Theorem eq_string_eq_bnode : forall (s1 s2:string) , (s1 = s2) <-> (Bnode s1) = (Bnode s2).
Proof. split; intros H.
  - rewrite H. reflexivity.
  - injection H as H2. apply H2.
Qed.

Theorem eq_dec_term : forall (t1 t2: term),
  {t1 = t2} + {t1 <> t2}.
Proof. decide equality.
  + apply string_dec.
  + decide equality.
  + apply string_dec.
Qed.

Theorem eqb_term_refl : forall (t1 : term),
  eqb_term t1 t1 = true.
Proof. destruct t1 as []; simpl.
  - apply eqb_refl.
  - symmetry. apply beq_nat_refl.
  - apply eqb_refl.
Qed.

Theorem eqb_eq_term : forall (t1 t2 : term),
  eqb_term t1 t2 = true <-> t1 = t2.
Proof. split; intros H.
  - destruct t1,t2 as [] ; 
    try reflexivity ;
    try discriminate; simpl in H.
    + apply eqb_eq in H. rewrite H. apply eq_string_eq_iri. reflexivity.
    + apply beq_nat_true in H. rewrite H. apply eq_nat_eq_lit. reflexivity.
    + apply eqb_eq in H. apply eq_string_eq_bnode. apply H.
  - rewrite H. apply eqb_term_refl.
Qed.
   
Theorem eqb_neq_term : forall (t1 t2 : term),
  eqb_term t1 t2 = false <-> t1 <> t2.
Proof. split.
  - intros H contra. rewrite contra in H. rewrite eqb_term_refl in H. discriminate H.
  - intros H. unfold not in H. rewrite <- eqb_eq_term in H. destruct (eqb_term t1 t2) as [].
    + exfalso. apply H. reflexivity.
    + reflexivity.
Qed.

