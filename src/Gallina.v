(* begin hide *)
Require Import Unicode.Utf8.
Require Import Coq.Program.Basics.
Require Import CoqCats.Category.
Require Import CoqCats.Relation.
Require Import Coq.Logic.JMeq.

Set Universe Polymorphism.
Set Polymorphic Inductive Cumulativity.
(* end hide *)

(** * The category of non-dependent Gallina functions.

    For now we'll try this with propositional equality, but I'm
    expecting we'll end up with at least extensional function
    equality.
 *)
Definition Gallina : category :=
  {| object := Type;

     arrow A B := A → B;
     arrow_equiv {A} {B} x := @JMeq A x B;
     arrow_equiv_equiv := eq_equiv;

     identity {_} x := x;

     compose {_ _ _} g f x := g (f x);

     right_identity _ _ _ := JMeq_refl;
     left_identity _ _ _ := JMeq_refl;

     compose_assoc _ _ _ _ _ _ _ := JMeq_refl;
  |}.
