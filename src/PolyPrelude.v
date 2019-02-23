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

Arguments eq_ind [A] x P _ y _.
Arguments eq_rec [A] x P _ y _.
Arguments eq_rect [A] x P _ y _.

Hint Resolve eq_refl: core.

Section Logic_lemmas.
  Section equality.
    Variables A B : Type.
    Variable f : A -> B.
    Variables x y z : A.

    Theorem eq_sym : x = y -> y = x.
    Proof.
      destruct 1; trivial.
    Defined.

    Theorem eq_trans : x = y -> y = z -> x = z.
    Proof.
      destruct 2; trivial.
    Defined.

    Theorem f_equal : x = y -> f x = f y.
    Proof.
      destruct 1; trivial.
    Defined.

    Theorem not_eq_sym : x <> y -> y <> x.
    Proof.
      red; intros h1 h2; apply h1; destruct h2; trivial.
    Qed.
  End equality.
End Logic_lemmas.
