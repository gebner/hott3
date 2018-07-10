/-
Copyright (c) 2015 Ulrik Buchholtz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ulrik Buchholtz
-/

import ..function
universes u v w
hott_theory
namespace hott

open hott.is_equiv hott.function fiber

namespace arrow

  @[hott] structure arrow :=
    (dom : Type _)
    (cod : Type _)
    (arrow : dom → cod)

  @[hott] def arrow_of_fn {A B : Type _} (f : A → B) : arrow :=
  arrow.mk A B f

  @[hott] instance : has_coe_to_fun arrow :=
  ⟨λf, f.dom → f.cod, arrow.arrow⟩

  -- structure morphism (A B : Type _) :=
  --   (mor : A → B)

  -- @[hott] def morphism_of_arrow (f : arrow) : morphism f.dom f.cod :=
  -- morphism.mk (arrow.arrow f)

  -- attribute [coercion] morphism.mor

  @[hott] structure arrow_hom (f g : arrow) :=
    (on_dom : f.dom → g.dom)
    (on_cod : f.cod → g.cod)
    (commute : Π(x : f.dom), g (on_dom x) = on_cod (f x))

  -- abbreviation on_dom := @arrow_hom.on_dom
  -- abbreviation on_cod := @arrow_hom.on_cod
  -- abbreviation commute := @arrow_hom.commute

  variables {f : arrow} {g : arrow}

  @[hott] def on_fiber (r : arrow_hom f g) (y : f.cod)
    : fiber f y → fiber g (r.on_cod y) :=
  λz, fiber.rec (λx p, fiber.mk (r.on_dom x) (r.commute x ⬝ ap (r.on_cod) p)) z

  @[hott, class] structure is_retraction (r : arrow_hom f g) :=
    (sect : arrow_hom g f)
    (right_inverse_dom : Π(a : g.dom), r.on_dom (sect.on_dom a) = a)
    (right_inverse_cod : Π(b : g.cod), r.on_cod (sect.on_cod b) = b)
    (cohere : Π(a : g.dom), r.commute (sect.on_dom a) ⬝ ap (r.on_cod) (sect.commute a)
                            = ap g (right_inverse_dom a) ⬝ (right_inverse_cod (g a))⁻¹)

  abbreviation arrow_hom.sect := @is_retraction.sect

  @[hott] def retraction_on_fiber (r : arrow_hom f g) [H : is_retraction r]
    (b : g.cod) : fiber f (r.sect.on_cod b) → fiber g b :=
  λz, fiber.rec (λx q, fiber.mk (r.on_dom x) (r.commute x ⬝ ap (r.on_cod) q ⬝ is_retraction.right_inverse_cod r b)) z

  @[hott] def retraction_on_fiber_right_inverse' (r : arrow_hom f g) [H : is_retraction r]
    (a : g.dom) (b : g.cod) (p : g a = b)
    : retraction_on_fiber r b (on_fiber r.sect b (fiber.mk a p)) = fiber.mk a p :=
  begin
    induction p, dsimp [on_fiber, retraction_on_fiber],
    apply @fiber.fiber_eq _ _ g (g a)
      (fiber.mk
        (r.on_dom (r.sect.on_dom a))
        (r.commute (r.sect.on_dom a)
          ⬝ ap (r.on_cod) (r.sect.commute a)
          ⬝ is_retraction.right_inverse_cod r (g a)))
      (fiber.mk a (refl (g a)))
      (is_retraction.right_inverse_dom r a), -- everything but this field should be inferred
    rwr [is_retraction.cohere r a],
    apply inv_con_cancel_right
  end

  @[hott] def retraction_on_fiber_right_inverse (r : arrow_hom f g) [H : is_retraction r]
    : Π(b : g.cod), Π(z : fiber g b), retraction_on_fiber r b (on_fiber r.sect b z) = z :=
  λb z, fiber.rec (λa p, retraction_on_fiber_right_inverse' r a b p) z

  -- @[hott] lemma 4.7.3
  @[hott, instance] def retraction_on_fiber_is_retraction (r : arrow_hom f g) [H : is_retraction r]
    (b : g.cod) : hott.is_retraction (retraction_on_fiber r b) :=
  hott.is_retraction.mk (on_fiber r.sect b) (retraction_on_fiber_right_inverse r b)

  -- @[hott] theorem 4.7.4
  @[hott] def retract_of_equivalence_is_equivalence (r : arrow_hom f g) [H : is_retraction r]
    [K : is_equiv f] : is_equiv g :=
  begin
    have : is_contr_fun g, intro b,
      apply is_contr_retract (retraction_on_fiber r b),
      exact is_contr_fun_of_is_equiv f (r.sect.on_cod b),
    exactI is_equiv_of_is_contr_fun g
  end

end arrow

namespace arrow
  variables {A : Type _} {B : Type _} {f g : A → B} (p : f ~ g)

  @[hott] def arrow_hom_of_homotopy : arrow_hom (arrow_of_fn f) (arrow_of_fn g) :=
  arrow_hom.mk id id (λx, (p x)⁻¹)

  @[hott, instance] def is_retraction_arrow_hom_of_homotopy
    : is_retraction (arrow_hom_of_homotopy p) :=
  is_retraction.mk
    (arrow_hom_of_homotopy (λx, (p x)⁻¹))
    (λa, idp)
    (λb, idp)
    (λa, con_eq_of_eq_inv_con (ap_id _))

end arrow

namespace arrow
  /-
    equivalences in the arrow category; could be packaged into structures.
    cannot be moved to types.pi because of the dependence on types.equiv.
  -/

  variables {A : Type _} {A' : Type _} {B : Type _} {B' : Type _} (f : A → B) (f' : A' → B')
            (α : A → A') (β : B → B')
            [Hf : is_equiv f] [Hf' : is_equiv f']
  include Hf Hf'

  open function
  @[hott] def inv_commute_of_commute (p : f' ∘ α ~ β ∘ f) : f'⁻¹ᶠ ∘ β ~ α ∘ f⁻¹ᶠ :=
  begin
    apply inv_homotopy_of_homotopy_post f' (α ∘ f⁻¹ᶠ) β,
    apply homotopy.symm,
    apply inv_homotopy_of_homotopy_pre f (f' ∘ α) β,
    apply p
  end

  @[hott] def inv_commute_of_commute_top (p : f' ∘ α ~ β ∘ f) (a : A)
    : inv_commute_of_commute f f' α β p (f a)
    =  (ap f'⁻¹ᶠ (p a))⁻¹ ⬝ left_inv f' (α a) ⬝ ap α (left_inv f a)⁻¹ :=
  begin
    dsimp [inv_commute_of_commute, inv_homotopy_of_homotopy_post, inv_homotopy_of_homotopy_pre,
           homotopy.symm],
    rwr [adj f a,←ap_compose β f],
    rwr [eq_of_square (natural_square p (left_inv f a))],
    rwr [ap_inv f'⁻¹ᶠ,ap_con f'⁻¹ᶠ,con_inv,con.assoc,con.assoc],
    apply whisker_left (ap f'⁻¹ᶠ (p a))⁻¹,
    apply eq_of_square, rwr [ap_inv α,←(ap_compose f'⁻¹ᶠ (f' ∘ α))],
    apply hinverse, rwr [ap_compose (f'⁻¹ᶠ ∘ f') α],
    refine vconcat_eq _ (ap_id (ap α (left_inv f a))),
    apply natural_square_tr (left_inv f') (ap α (left_inv f a))
  end

  @[hott] def ap_bot_inv_commute_of_commute (p : f' ∘ α ~ β ∘ f) (b : B)
    : ap f' (inv_commute_of_commute f f' α β p b)
    = right_inv f' (β b) ⬝ ap β (right_inv f b)⁻¹ ⬝ (p (f⁻¹ᶠ b))⁻¹ :=
  begin
    dsimp [inv_commute_of_commute, inv_homotopy_of_homotopy_post, inv_homotopy_of_homotopy_pre],
    rwr [ap_con,←(ap_compose f' f'⁻¹ᶠ),←(adj f' (α (f⁻¹ᶠ b)))],
    rwr [con.assoc (right_inv f' (β b)) (ap β (right_inv f b)⁻¹)
                       (p (f⁻¹ᶠ b))⁻¹],
    apply eq_of_square,
    refine vconcat_eq _
      (whisker_right (p (f⁻¹ᶠ b))⁻¹ (ap_inv β (right_inv f b)))⁻¹ᵖ,
    refine vconcat_eq _
      (con_inv (p (f⁻¹ᶠ b)) (ap β (right_inv f b))),
    refine vconcat_eq _
      (ap_id (p (f⁻¹ᶠ b) ⬝ ap β (right_inv f b))⁻¹),
    apply natural_square_tr (right_inv f')
      (p (f⁻¹ᶠ b) ⬝ ap β (right_inv f b))⁻¹
  end

  @[hott] def is_equiv_inv_commute_of_commute
    : is_equiv (inv_commute_of_commute f f' α β) :=
  begin
    delta inv_commute_of_commute,
    napply @is_equiv_compose _ _ _ (inv_homotopy_of_homotopy_post f' (α ∘ f⁻¹ᶠ) β)
      (homotopy.symm ∘ (inv_homotopy_of_homotopy_pre f (f' ∘ α) β)),
    { napply @is_equiv_compose _ _ _ homotopy.symm (inv_homotopy_of_homotopy_pre f (f' ∘ α) β),
      { apply inv_homotopy_of_homotopy_pre.is_equiv },
      { apply pi.is_equiv_homotopy_symm }
    },
    { apply inv_homotopy_of_homotopy_post.is_equiv }
  end
end arrow
end hott