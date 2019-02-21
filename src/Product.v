(* begin hide *)
Require Import Unicode.Utf8.
Require Import Coq.Program.Basics.
Require Import CoqCats.Category.

Set Universe Polymorphism.
Set Polymorphic Inductive Cumulativity.
(* end hide *)

(** * Categorical products.

    First, the data related by the claim that a categorical product
    exits:
*)
Record product_data :=
  { cat : category;
    (** To recover the familiar binary product, set idx := 2. *)
    idx : Type;
    object_product : object cat;
    components : idx → object cat;
  }.

(** Now, what does it mean to say that the data do exhibit a product?
 *)
Record product (data : product_data) :=
  { c := cat data;
    comp := components data;
    a := arrow c;
    op := object_product data;

    property o := ∀ i, a o (comp i);
    proj : property op;
    commutes {o} (γ : property o) f := ∀ i,
        (arrow_equiv c)
          (γ i)
          ((compose c) (proj i) f);

    morphism_product : ∀ {o}, property o → a o op;
    morphism_product_commutes : ∀ {o γ},
        commutes o γ (morphism_product γ);
    morphism_product_unique : ∀ {o γ f},
        commutes o γ f → (arrow_equiv c) f (morphism_product γ);
  }.
