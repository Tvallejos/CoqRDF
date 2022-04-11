From Coq Require Import Init.Nat.
From Coq Require Import Strings.String.

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

Definition eqb_node (n1 n2 : term) : bool :=
  (match n1, n2 with
   | (Iri id), (Iri id2) => eqb id id2
   | (Lit l),(Lit l2) => l =? l2
   | (Bnode b),(Bnode b2) => eqb b b2
   | _,_ => false
   end).
