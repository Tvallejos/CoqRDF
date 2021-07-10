From Coq Require Import Lists.ListSet.
From Coq Require Import Init.Nat.
From Coq Require Import Bool.Bool.
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

Inductive trpl : Type :=
  | triple (s p o : node).

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
(* Definition triple := (node * node * node)%type.  *)

Check (triple (Null) (Const 1) (Var "foo")): trpl.


(*
   Inductive rdf : Type :=
  | graph (triples : list triple).
 *)

(* Not sure if its a good idea to have a set, 
 may be we want some order on the triples *)
Definition graph := set trpl.

Definition app_μ_to_triple (μ : node -> node) (t : trpl) : trpl:=
  (match t with
   | (triple n1 n2 n3) => triple (μ n1) n2 (μ n3)
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

Definition eqb_triple (t1 t2:trpl) : bool :=
  (match t1,t2 with
   | (triple s p o),(triple s2 p2 o2) => (eqb_node s s2) && (eqb_node p p2) && (eqb_node o o2)
   end).

Theorem eqb_eq_triple: forall (t1 t2 : trpl),
  eqb_triple t1 t2 = true <-> t1 = t2.
Proof. intros. split.
  - intros H. destruct t1,t2 as [s2 p2 o2]; f_equal;
    simpl in H; apply andb_true_iff in H; destruct H as [H0 H2]; apply andb_true_iff in H0; destruct H0 as [H H1]; apply eqb_eq_node. 
    + apply H.
    + apply H1.
    + apply H2.
  - intros H. destruct t1,t2 as [s2 p2 o2]. injection H as H1 H2 H3. simpl. rewrite H1. rewrite H2. rewrite H3.
    rewrite <- (eqb_node_refl s2). rewrite <- (eqb_node_refl p2). rewrite <- (eqb_node_refl o2). reflexivity.
Qed.

Theorem eqb_triple_refl : forall (t1: trpl),
  eqb_triple t1 t1 = true.
Proof. intros. destruct t1. simpl. rewrite <- (eqb_node_refl s). rewrite <- (eqb_node_refl p). rewrite <- (eqb_node_refl o). reflexivity.
Qed.

Theorem eqb_neq_triple : forall (t1 t2: trpl),
  eqb_triple t1 t2 = false <-> t1 <> t2.
Proof. intros. split.
  - intros H contra. rewrite contra in H. rewrite eqb_triple_refl in H. discriminate H.
  - intros H. unfold not in H. rewrite <- eqb_eq_triple in H. destruct (eqb_triple t1 t2).
    + exfalso. apply H. reflexivity.
    + reflexivity.
Qed.

(* POC: this WILL be refactored *)
Theorem eq_or_not_triple : forall (t1 t2: trpl),
  {t1 = t2} + {t1 <> t2}.
Proof. intros t1 t2. destruct t1, t2. destruct (eq_or_not s s0,eq_or_not p p0,eq_or_not o o0) as [[[H|H] [H2|H2]] [H3|H3]] eqn:E.
- try (left; try f_equal;
      try apply H;
      try apply H2;
      try apply H3).
- (try (right; 
      try rewrite <- eqb_neq_triple; simpl;
      try rewrite H;
      try rewrite H2;
      try rewrite H3;
      try rewrite <- (eqb_node_refl s0);
      try rewrite <- (eqb_node_refl p0);
      try rewrite <- (eqb_node_refl o0));
    try reflexivity;
    try simpl; 
    rewrite eqb_neq_node;
      try apply H;
      try apply H2;
      try apply H3).
- try right. 
  try rewrite <- eqb_neq_triple. simpl.
      try rewrite H.
      try rewrite H2.
      try rewrite H3.
      try rewrite <- (eqb_node_refl s0).
      try rewrite <- (eqb_node_refl p0).
      try rewrite <- (eqb_node_refl o0).
    try reflexivity.
    try simpl.
    try (rewrite andb_comm;simpl).
    rewrite eqb_neq_node;
      try apply H;
      try apply H2;
      try apply H3.
- try right. 
  try rewrite <- eqb_neq_triple. simpl.
      try rewrite H.
      try rewrite H2.
      try rewrite H3.
      try rewrite <- (eqb_node_refl s0).
      try rewrite <- (eqb_node_refl p0).
      try rewrite <- (eqb_node_refl o0).
    try reflexivity.
    try simpl.
    try (rewrite andb_comm;simpl). 
    apply andb_false_iff. left.
    rewrite eqb_neq_node;
      try apply H;
      try apply H2;
      try apply H3.
- try right. 
  try rewrite <- eqb_neq_triple. simpl.
      try rewrite H.
      try rewrite H2.
      try rewrite H3.
      try rewrite <- (eqb_node_refl s0).
      try rewrite <- (eqb_node_refl p0).
      try rewrite <- (eqb_node_refl o0).
    try reflexivity.
    try simpl.
    try (rewrite andb_comm;simpl).
    apply andb_false_iff. left.
    rewrite eqb_neq_node;
      try apply H;
      try apply H2;
      try apply H3.
- try right. 
  try rewrite <- eqb_neq_triple. simpl.
      try rewrite H.
      try rewrite H2.
      try rewrite H3.
      try rewrite <- (eqb_node_refl s0).
      try rewrite <- (eqb_node_refl p0).
      try rewrite <- (eqb_node_refl o0).
    try reflexivity.
    try simpl.
    try (rewrite andb_comm;simpl).
    apply andb_false_iff. left.
    rewrite eqb_neq_node;
      try apply H;
      try apply H2;
      try apply H3.
- try right. 
  try rewrite <- eqb_neq_triple. simpl.
      try rewrite H.
      try rewrite H2.
      try rewrite H3.
      try rewrite <- (eqb_node_refl s0).
      try rewrite <- (eqb_node_refl p0).
      try rewrite <- (eqb_node_refl o0).
    try reflexivity.
    try simpl.
    try (rewrite andb_comm;simpl).
    apply andb_false_iff. left.
    rewrite eqb_neq_node;
      try apply H;
      try apply H2;
      try apply H3.
- try right. 
  try rewrite <- eqb_neq_triple. simpl.
      try rewrite H.
      try rewrite H2.
      try rewrite H3.
      try rewrite <- (eqb_node_refl s0).
      try rewrite <- (eqb_node_refl p0).
      try rewrite <- (eqb_node_refl o0).
    try reflexivity.
    try simpl.
    try (rewrite andb_comm;simpl).
    apply andb_false_iff. left.
    rewrite eqb_neq_node;
      try apply H;
      try apply H2;
      try apply H3.
Qed.

Check (set_add eq_or_not_triple (triple (Const 1) (Const 1) (Const 1)) (empty_set trpl)): graph.

Definition image (g : graph) (μ : node -> node) : graph :=
  set_map eq_or_not_triple (fun t => app_μ_to_triple μ t) g.

(* image of mapping Const 2 of 1,1,1 => 2,1,2*)
Compute (image (set_add eq_or_not_triple (triple (Const 1) (Const 1) (Const 1)) (empty_set trpl)) 
  (fun _ => Const 2)): graph.

(* Check [((Const 5),(Const 5), (Const 5))].
   Check (set_add ((Const 5),(Const 5), (Const 5)) empty_set). *)
(* Check (set ((Const 5),(Const 5), (Const 5)),  ((Var "x"),(Const 1),(Const 2))  ) : graph.
 *)
