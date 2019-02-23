(* begin hide *)
Require Import Unicode.Utf8.
Require Import Coq.Program.Basics.
Require Import CoqCats.Category.

Set Universe Polymorphism.
Set Polymorphic Inductive Cumulativity.
(* end hide *)

(** * The category of non-dependent Gallina functions.
 *)
Local Open Scope program_scope.
Definition Gallina : category :=
  {| object := Type;

     arrow A B := A → B;

     identity _ x := x;

     compose _ _ _ g f := g ∘ f;

     right_identity _ _ _ := eq_refl;
     left_identity _ _ _ := eq_refl;

     compose_assoc _ _ _ _ _ _ _ := eq_refl;
  |}.
