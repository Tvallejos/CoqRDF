From Coq Require Import Lists.ListSet.
From Coq Require Import Lists.List.
From Coq Require Import Init.Nat.
From Coq Require Import Strings.String.
From Coq Require Import Bool.Bool.
From RDF Require Import Node.
From RDF Require Import Triples.
From RDF Require Import Maps.
From RDF Require Import Graph.

Definition image (g : graph) (μ : node -> node) : graph :=
  set_map eq_dec_triple (fun t => app_μ_to_triple μ t) g.

Theorem image_id_refl : forall (g : graph),
  image g id = g.
Proof. induction g as [| h t].
- reflexivity.
- simpl. assert (app: (app_μ_to_triple id h) = h).
  { unfold app_μ_to_triple. destruct h. apply f_equal. reflexivity. }
  rewrite app. rewrite IHt.
  unfold set_add. induction t as [| a tt IHtt]. 
  + reflexivity.
  + Admitted.

(* image of mapping Const 2 of 1,1,1 => 2,1,2*)
Compute (image (set_add eq_dec_triple (triple (Const 1) (Const 1) (Const 1)) (empty_set trpl)) 
  (fun _ => Const 2)): graph.

Inductive world : Type :=
  | res (I L B : set node).

Definition proj_I (w : world) : set node :=
  match w with
  | res i _ _ => i
  end.
Definition proj_L (w : world) : set node :=
  match w with
  | res _ l _ => l
  end.

Definition proj_B (w : world) : set node :=
  match w with
  | res _ _ b => b
  end.
Definition proj_IL (w : world) : set node:=
  set_union eq_dec_node (proj_I w) (proj_L w).

Definition isomorphism (w : world) (g g': graph) :=
  exists μ : node -> node,
  relabelling (proj_IL w) (proj_B w) μ -> (image g μ) = g'.

Theorem isomorphism_refl : forall (w: world) (g : graph),
  isomorphism w g g.
Proof. 
unfold isomorphism. exists id. intros H. induction g as [| h t].
  - reflexivity.
  - simpl. assert (app: (app_μ_to_triple id h) = h).
  { unfold app_μ_to_triple. destruct h. apply f_equal. reflexivity. }
  rewrite app. rewrite -> IHt.  
  destruct (set_add eq_dec_triple h (image t id)) eqn:E.
  + rewrite IHt in E. exfalso. unfold set_add in E. 
    induction t.
    * discriminate E.
    * destruct (eq_dec_triple h a).
      { discriminate E. }
      { discriminate E. }
  + rewrite IHt in *. rewrite E in *. Admitted.




