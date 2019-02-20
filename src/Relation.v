(* begin hide *)
Require Import Unicode.Utf8.
Require Import Coq.Logic.JMeq.

Set Universe Polymorphism.
Set Polymorphic Inductive Cumulativity.
Set Implicit Arguments.
(* end hide *)
(** * Heterogeneous equivalence relations.

    We want to be able to capture a notion of equivalence between
    members of different types in the same inductive family, e.g. for
    equivalence of arrows in a category where object equivalence
    doesn't directly correspond to Gallina equality.
 *)

Record equivalence (R : ∀ A B, A → B → Type) :=
  { R' {A} {B} := R A B;
    equiv_refl : ∀ {A} {x : A}, R' x x;
    equiv_sym : ∀ {A B} {x : A} {y : B}, R' x y → R' y x;
    equiv_trans: ∀ {A B C} {x : A} {y : B} {z : C},
        R' x y → R' y z → R' x z;
  }.

Definition eq_equiv : equivalence (λ A B x, @JMeq A x B) :=
  {| equiv_refl := @JMeq_refl;
     equiv_sym := @JMeq_sym;
     equiv_trans := @JMeq_trans;
  |}.
