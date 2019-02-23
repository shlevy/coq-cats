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
Record category :=
  { object : Type;

    arrow : object → object → Type;

    identity : ∀ {a}, arrow a a;
    (* TODO 1_a notation for identity? *)

    compose : ∀ {a b c}, arrow b c → arrow a b → arrow a c
    where "g ∘ f" := (compose g f);

    right_identity : ∀ {a b} {f : arrow a b},
        f ∘ identity = f;
    left_identity : ∀ {a b} {f : arrow a b},
        identity ∘ f = f;

    compose_assoc :
      ∀ {a b c d} {f : arrow a b} {g : arrow b c} {h : arrow c d},
        h ∘ g ∘ f = h ∘ (g ∘ f);
  }.

Notation "g ∘ f" := (compose _ g f) : cat_scope.

Open Scope cat_scope.

Record isomorphism {cat a b} (from : (arrow cat) a b) :=
  { to : (arrow cat) b a;
    comm_from : to ∘ from = identity _;
    comm_to : from ∘ to = identity _;
  }.
