(* begin hide *)
Require Import Unicode.Utf8.
Require Import Coq.Program.Basics.

Set Universe Polymorphism.
Set Polymorphic Inductive Cumulativity.
Set Implicit Arguments.

(* end hide *)
(** * Universe-polymorphic variants of prelude definitions. *)

Inductive eq (A : Type) (x : A) : A → Prop :=
  eq_refl : x = x :>A
where "x = y :> A" := (@eq A x y) : type_scope.
Notation "x = y" := (x = y :>_) : type_scope.

Arguments eq {A} x _.
Arguments eq_refl {A x} , [A] x.
