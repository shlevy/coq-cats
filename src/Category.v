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

    compose : ∀ {a b c}, arrow b c → arrow a b → arrow a c;
    (* TODO ∘ notation for composition? *)

    right_identity : ∀ {a b} {f : arrow a b},
        (compose f identity) = f;
    left_identity : ∀ {a b} {f : arrow a b},
        (compose identity f) = f;

    compose_assoc :
      ∀ {a b c d} {f : arrow a b} {g : arrow b c} {h : arrow c d},
        (compose h (compose g f)) = (compose (compose h g) f);
  }.

Record isomorphism {cat a b} (from : (arrow cat) a b) :=
  { to : (arrow cat) b a;
    comm_from : ((compose cat) to from) = identity _;
    comm_to : ((compose cat) from to) = identity _;
  }.
