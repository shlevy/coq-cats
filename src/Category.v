(* begin hide *)
Require Import Unicode.Utf8.
Require Import Coq.Program.Basics.
Require Import CoqCats.Relation.

Set Universe Polymorphism.
Set Polymorphic Inductive Cumulativity.
(* end hide *)

(** * Foundational representation of categories.

    Because I want this module to be a candidate for the lowest level
    of any project needing to work with category theory, this
    construction differs from the naive approach in the following ways:

    - All definitions are maximally universe-polymorphic. This enables
      categories like Cat and other similar constructions, as well as
      allowing the user to decide whether or not to use impredicative
      Prop for propositions.
    - Wherever the relevant laws require an equivalence, the user can
      pass in their own equivalence relation rather than being limited
      to definitional equality in Gallina or the typical notion of
      propositional equality. As such, any types indexed by types with
      the relevant equivalences must respect them (though proofs of
      respecting equivalence will wait until I need them).

    Also, I'm trying to avoid any functions that take proofs and
    return anything other than proofs, relying on type indices
    wherever possible (see e.g. 'compose'). This is to avoid pain
    around having to transport across proofs, proof irrelevance, etc.
 *)

Record category :=
  { object : Type;

    arrow : object → object → Type;

    identity : ∀ {a}, arrow a a;
    (* TODO 1_a notation for identity? *)

    compose : ∀ {a b c}, arrow b c → arrow a b → arrow a c;
    (* TODO ∘ notation for composition? *)

    arrow_equiv : ∀ {A} {B}, A → B → Type;
    arrow_equiv_equiv : equivalence (@arrow_equiv);

    right_identity : ∀ {a b} {f : arrow a b},
        arrow_equiv f (compose f identity);
    left_identity : ∀ {a b} {f : arrow a b},
        arrow_equiv f (compose identity f);

    compose_assoc :
      ∀ {a b c d} {f : arrow a b} {g : arrow b c} {h : arrow c d},
        arrow_equiv (compose h (compose g f)) (compose (compose h g) f);
  }.

Record isomorphism {cat a b} (from : (arrow cat) a b) :=
  { to : (arrow cat) b a;
    comm_from : (arrow_equiv cat)
                  ((compose cat) to from)
                  (identity (a := a) cat);
    comm_to : (arrow_equiv cat)
                ((compose cat) from to)
                (identity (a := b) cat);
  }.
