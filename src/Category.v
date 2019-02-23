(* begin hide *)
Require Import Unicode.Utf8.
Require Import Coq.Program.Basics.

Set Universe Polymorphism.
Set Polymorphic Inductive Cumulativity.
(* end hide *)

(** * Foundational representation of categories.

    I use propositional equality here in the hope that one day we will
    have quotient types/HoTT. In the mean time if we restrict
    ourselves to using quotiented versions of constructors when
    dealing with concrete categories we can pretend the non-standard
    forms don't exist.
 *)
Reserved Notation "a ⇝ b" (at level 99, b at level 200, right associativity).
Record category :=
  { object : Type;

    arrow : object → object → Type
    where "a ⇝ b" := (arrow a b);

    identity : ∀ {a}, a ⇝ a
    where "1" := identity;

    compose : ∀ {a b c}, (b ⇝ c) → (a ⇝ b) → (a ⇝ c)
    where "g ∘ f" := (compose g f);

    right_identity : ∀ {a b} {f : a ⇝ b},
        f ∘ 1 = f;
    left_identity : ∀ {a b} {f : a ⇝ b},
        1 ∘ f = f;

    compose_assoc :
      ∀ {a b c d} {f : a ⇝ b} {g : b ⇝ c} {h : c ⇝ d},
        h ∘ g ∘ f = h ∘ (g ∘ f);
  }.

Notation "g ∘ f" := (compose _ g f) : cat_scope.

Notation "1" := (identity _) : cat_scope.

Notation "a ⇝ b" := (arrow _ a b) : cat_scope.

Delimit Scope cat_scope with cat.

Open Scope cat_scope.

Record isomorphism {cat} {a b : object cat} (from : a ⇝ b) :=
  { to : b ⇝ a;
    comm_from : to ∘ from = 1;
    comm_to : from ∘ to = 1;
  }.
