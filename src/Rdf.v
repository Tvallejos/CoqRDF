From Coq Require Import Lists.ListSet.
From Coq Require Import Init.Nat.
From Coq Require Import Strings.String.
From Coq Require Import Arith.EqNat.

Definition eqb_string (x y : string) : bool :=
  if string_dec x y then true else false.

Inductive node : Type :=
  | Null
  | Const (c : nat)
  | Var (s : string).

Definition is_const (n : node) : bool :=
  (match n with
   | Const _ => true
   | otherwise => false
   end).

Definition is_var (n : node) : bool :=
  (match n with
   | Var _ => true
   | otherwise => false
   end).

Check (Const 5) : node.
Check (Var "x") : node.
Check (Null) : node.

(*
An idea to define triples
Inductive trpl : Type :=
  | triple (s p o : node).
 *)

Definition eqb_node (n1 n2 : node) : bool :=
  (match n1, n2 with
   | (Null), (Null) => true
   | (Const c1), (Const c2) => c1 =? c2
   | (Var s1),(Var s2) => eqb s1 s2
   | e1,e2 => false
   end).

Example eqb_null_node :  eqb_node (Null) (Null) = true.
Proof. reflexivity. Qed.
Example eqb_const_eq_node:  eqb_node (Const 5) (Const 5) = true.
Proof. reflexivity. Qed.
Example eqb_const_neq_node:  eqb_node (Const 5) (Const 0) = false.
Proof. reflexivity. Qed.
Example eqb_var_eq_node :  eqb_node (Var "x") (Var "x") = true.
Proof. reflexivity. Qed.
Example eqb_var_neq_node :  eqb_node (Var "x") (Var "y") = false.
Proof. reflexivity. Qed.

Theorem eq_nat_eq_const : forall (n1 n2:nat) , (n1 = n2) <-> (Const n1) = (Const n2).
Proof. split.
  - intros H. rewrite H. reflexivity.
  - intros H. injection H as H2. apply H2.
Qed.

Theorem eq_string_eq_var : forall (s1 s2:string) , (s1 = s2) <-> (Var s1) = (Var s2).
Proof. split.
  - intros H. rewrite H. reflexivity.
  - intros H. injection H as H2. apply H2.
Qed.

Theorem eqb_node_refl : forall (nod1 : node),
  true = eqb_node nod1 nod1.
Proof. destruct nod1 as [].
  - reflexivity.
  - simpl. apply beq_nat_refl.
  - simpl. symmetry. apply eqb_refl.
Qed.

Theorem eqb_eq_node : forall (nod1 nod2 : node),
  eqb_node nod1 nod2 = true <-> nod1 = nod2.
Proof. split.
  - intros H. destruct nod1,nod2 as [] ; 
    try reflexivity ;
    try discriminate.
    + simpl in H. apply beq_nat_true in H. apply eq_nat_eq_const. apply H.
    + simpl in H. apply eqb_eq in H. apply eq_string_eq_var. apply H.
  - intros H. rewrite H. symmetry. apply eqb_node_refl.
Qed.
   
Theorem eqb_neq_node : forall (nod1 nod2 : node),
  eqb_node nod1 nod2 = false <-> nod1 <> nod2.
Proof. split.
  - intros H contra. rewrite contra in H. rewrite <- eqb_node_refl in H. discriminate H.
  - intros H. unfold not in H. rewrite <- eqb_eq_node in H. destruct (eqb_node nod1 nod2) as [].
    + exfalso. apply H. reflexivity.
    + reflexivity.
Qed.

(* alias for triple of nodes type *)
Definition triple := (node * node * node)%type. 

Check ((Null), (Const 1), (Var "foo")): triple.


(*
   Inductive rdf : Type :=
  | graph (triples : list triple).
 *)

(* Not sure if its a good idea to have a set, 
 may be we want some order on the triples *)
Definition graph := set triple.
Definition app_μ_to_triple (μ : node -> node) (t : triple) :=
  (match t with
   | (n1, n2, n3) => (μ n1 , n2 , μ n3)
   end).

Theorem eq_or_not : forall (n m: node),
  {n = m} + {n <> m}.
Proof. intros n m.
  destruct n,m ; 
  try (left ; reflexivity);
  try (right ; reflexivity);
  try (left ; apply eqb_neq_node ; reflexivity);
  try (right ; apply eqb_neq_node ; reflexivity);
  try (left ; apply eqb_eq_node ; reflexivity);
  try (right ; apply eqb_eq_node ; reflexivity).
  - destruct (c =? c0) eqn:E.
    + left. apply eqb_eq_node. simpl. apply E. 
    + right. apply eqb_neq_node. simpl. apply E.
  - destruct (eqb s s0) eqn:E.
    + left. apply eqb_eq_node. simpl. apply E.
    + right. apply eqb_neq_node. simpl. apply E.
Qed.

Check set_In.
Check (set_add eq_or_not (Var "x") (set_add eq_or_not (Const 5) (empty_set node))).
Example example_in_graph : set_In (Const 12) (set_add eq_or_not (Const 12) (set_add eq_or_not (Const 5) (empty_set node))).
Proof. simpl. destruct (eq_or_not (Const 12) (Const 5)) eqn:E.
  - simpl. left. symmetry. apply e.
  - simpl. right. left. reflexivity.
Qed.

Definition eqb_triple (t1 t2:triple) : bool :=
  (match t1,t2 with
   | (s,p,o),(s2,p2,o2) => (eqb_node s s2) && (eqb_node p p2) && (eqb_node o o2)
   end).

(* 
Theorem eqb_eq_triple: forall (t1 t2 : triple),
  eqb_triple t1 t2 = true <-> t1 = t2.
Proof. intros. split.
 *)
Theorem eq_or_not_triple : forall (t1 t2:triple),
  {t1 = t2} + {t1 <> t2}.
Proof. intros t1 t2. destruct t1, t2.
  - destruct (eq_or_not n n0) eqn:E. Admitted.

    (* 
Definition image (g : graph) (μ : node -> node) : graph :=
  set_map eq_or_not (fun t => app_μ_to_triple μ t) g.

     *)

(* Check [((Const 5),(Const 5), (Const 5))].
   Check (set_add ((Const 5),(Const 5), (Const 5)) empty_set). *)
(* Check (set ((Const 5),(Const 5), (Const 5)),  ((Var "x"),(Const 1),(Const 2))  ) : graph.
 *)
