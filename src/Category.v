(* begin hide *)
Require Import Unicode.Utf8.
Require Import Coq.Program.Basics.
Require Import CoqCats.PolyPrelude.

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

Coercion object : category >-> Sortclass.

Delimit Scope cat_scope with cat.

Open Scope cat_scope.

Record isomorphism {cat : category} {a b : cat} (from : a ⇝ b) :=
  { to : b ⇝ a;
    comm_from : to ∘ from = 1;
    comm_to : from ∘ to = 1;
  }.

(** ** Equality properties.

    We define here some high-level properties equality gives us with
    respect to the components of a category, so that we can more
    easily switch back to an arbitrary equivalence relation in the
    future if we want to (assuming everything that operates over
    abstract categories only uses these properties rather than matching
    on the equality proof directly).
 *)
Section equality.
  Variable cat : category.
  Variable a b c : cat.
  Variable f : a ⇝ b.
  Variable g g' : b ⇝ c.
  Definition compose_transport_left (p : g = g') : g ∘ f = g' ∘ f :=
    match p with
      eq_refl => eq_refl
    end.
End equality.
Arguments compose_transport_left {cat} {a} {b} {c} {f} {g} {g'}.
