(* begin hide *)
Require Import Unicode.Utf8.
Require Import CoqCats.Category.
Require Import CoqCats.PolyPrelude.

Set Universe Polymorphism.
Set Polymorphic Inductive Cumulativity.
(* end hide *)

(** * Categorical products.

    I define products of an arbitrarily indexed set of objects. To
    recover the familiar binary product, set idx to 2.
 *)
Record product {cat : category} {idx}
       (object_product : cat) (components : idx → cat) :=
  { (** The property we care about: An arrow to each component. *)
    property o := ∀ i, o ⇝ (components i);
    (** The projections from our object product. *)
    π : property object_product;
    (** Any object with our property has an arrow to our distingiushed
        object prodcut. *)
    morphism_product : ∀ {o}, property o → o ⇝ object_product;
    (** We now have an indexed set of diagrams: Given an arbitrary
        object satisfying our property, we have an arrow from it to
        our object product and for each i, we have an arrow from
        our object product to the relevant component and an arrow from
        the arbitrary object to the relevant component. Abstracting
        away the distingiushed morphism product and replacing it with
        an arbitrary arrow f from the arbitrary object to our object
        product, we say f commutes with this set of diagrams when each
        diagram commutes in the obvious way.
     *)
    commutes o (γ : property o) f := ∀ i, γ i = π i ∘ f;
    morphism_product_commutes : ∀ {o γ},
        commutes o γ (morphism_product γ);
    morphism_product_unique : ∀ {o γ f},
        commutes o γ f → f = morphism_product γ;
  }.

Arguments morphism_product [cat] [idx] [object_product] [components] _ [o].
Arguments π [cat] [idx] [object_product] [components].
Arguments commutes [cat] [idx] [object_product] [components].
Arguments morphism_product_unique [cat] [idx] [object_product] [components] _ [o] [γ] [f].

Section product.
  Variable cat : category.
  Variable idx : Type.
  Variable op : cat.
  Variable comp : idx → cat.
  Variable prod : product op comp.

  (* In prose:
     Lemma: The identity commutes
     Proof: For each i, it's given by the fact that 1 is a right
     identity of ∘.
     Theorem: The identity is the morphism product from the object
     product to itself.
     Proof: The morphism product uniquely commutes, and the identity
     commutes.

     TODO Figure out how tactics work.
   *)
  Definition identity_morphism_product :
    prod.(morphism_product) prod.(π) = 1 :=
    let
      id_commutes i := eq_sym cat.(right_identity)
    in eq_sym (prod.(morphism_product_unique) id_commutes).
End product.
