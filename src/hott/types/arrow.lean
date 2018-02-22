/-
Copyright (c) 2014 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Floris van Doorn

Ported from Coq HoTT
Theorems about arrow types (function spaces)
-/

import hott.types.pi

universe u
hott_theory

namespace hott
open eq hott.equiv hott.is_equiv is_trunc

namespace pi

  variables {A : Type _} {A' : Type _} {B : Type _} {B' : Type _} {C : A → B → Type _} {D : A → Type _}
            {a a' a'' : A} {b b' b'' : B} {f g : A → B} {d : D a} {d' : D a'}

  -- all lemmas here are special cases of the ones for pi-types

  /- Functorial action -/
  variables (f0 : A' → A) (f1 : B → B')

  @[hott] def arrow_functor : (A → B) → (A' → B') := pi_functor f0 (λa, f1)

  /- Equivalences -/

  @[hott] def is_equiv_arrow_functor
    [H0 : is_equiv f0] [H1 : is_equiv f1] : is_equiv (arrow_functor f0 f1) :=
  is_equiv_pi_functor f0 (λa, f1)

  @[hott] def arrow_equiv_arrow_rev (f0 : A' ≃ A) (f1 : B ≃ B')
    : (A → B) ≃ (A' → B') :=
  equiv.mk _ (is_equiv_arrow_functor f0 f1)

  @[hott] def arrow_equiv_arrow (f0 : A ≃ A') (f1 : B ≃ B') : (A → B) ≃ (A' → B') :=
  arrow_equiv_arrow_rev (equiv.symm f0) f1

  variable (A)
  @[hott] def arrow_equiv_arrow_right (f1 : B ≃ B') : (A → B) ≃ (A → B') :=
  arrow_equiv_arrow_rev equiv.rfl f1

  variables {A} (B)
  @[hott] def arrow_equiv_arrow_left_rev (f0 : A' ≃ A) : (A → B) ≃ (A' → B) :=
  arrow_equiv_arrow_rev f0 equiv.rfl

  @[hott] def arrow_equiv_arrow_left (f0 : A ≃ A') : (A → B) ≃ (A' → B) :=
  arrow_equiv_arrow f0 equiv.rfl

  variables {B}
  @[hott] def arrow_equiv_arrow_right' (f1 : A → (B ≃ B')) : (A → B) ≃ (A → B') :=
  pi_equiv_pi_right f1

  /- Equivalence if one of the types is contractible -/

  variables (A B)
  -- we prove this separately from pi_equiv_of_is_contr_left,
  --   because the underlying inverse function is simpler here (no transport needed)
  @[hott] def arrow_equiv_of_is_contr_left [H : is_contr A] : (A → B) ≃ B :=
  begin
    fapply equiv.MK,
    { intro f, exact f (center A)},
    { intros b a, exact b},
    { intro b, reflexivity},
    { intro f, apply eq_of_homotopy, intro a, exact ap f (is_prop.elim _ _)}
  end

  @[hott] def arrow_equiv_of_is_contr_right [H : is_contr B] : (A → B) ≃ unit :=
  pi_equiv_of_is_contr_right _

  /- Interaction with other type constructors -/

  -- most of these are in the file of the other type constructor

  @[hott] def arrow_empty_left : (empty → B) ≃ unit :=
  pi_empty_left _

  @[hott] def arrow_unit_left : (unit → B) ≃ B :=
  arrow_equiv_of_is_contr_left _ _

  @[hott] def arrow_unit_right : (A → unit) ≃ unit :=
  arrow_equiv_of_is_contr_right _ _

  variables {A B}

  /- Transport -/

  @[hott] def arrow_transport {B C : A → Type _} (p : a = a') (f : B a → C a)
    : (transport (λa, B a → C a) p f) ~ (λb, p ▸ f (p⁻¹ ▸ b)) :=
  eq.rec_on p (λx, idp)

  /- Pathovers -/

  @[hott] def arrow_pathover {B C : A → Type _} {f : B a → C a} {g : B a' → C a'} {p : a = a'}
    (r : Π(b : B a) (b' : B a') (q : b =[p] b'), f b =[p] g b') : f =[p; λa, B a → C a] g :=
  begin
    induction p, apply pathover_idp_of_eq,
    apply eq_of_homotopy, hintro b,
    exact eq_of_pathover_idp (r b b idpo),
  end

  @[hott] def arrow_pathover_left {B C : A → Type _} {f : B a → C a} {g : B a' → C a'} {p : a = a'}
    (r : Π(b : B a), f b =[p] g (p ▸ b)) : f =[p; λa, B a → C a] g :=
  begin
    induction p, apply pathover_idp_of_eq,
    apply eq_of_homotopy, hintro b,
    exact eq_of_pathover_idp (r b),
  end

  @[hott] def arrow_pathover_right {B C : A → Type _} {f : B a → C a} {g : B a' → C a'} {p : a = a'}
    (r : Π(b' : B a'), f (p⁻¹ ▸ b') =[p] g b') : f =[p; λa, B a → C a] g :=
  begin
    induction p, apply pathover_idp_of_eq,
    apply eq_of_homotopy, hintro b,
    exact eq_of_pathover_idp (r b),
  end

  @[hott] def arrow_pathover_constant_left {B : Type _} {C : A → Type _} {f : B → C a} {g : B → C a'}
    {p : a = a'} (r : Π(b : B), f b =[p] g b) : f =[p; λa, B → C a] g :=
  pi_pathover_constant r

  @[hott] def arrow_pathover_constant_right' {B : A → Type _} {C : Type _}
    {f : B a → C} {g : B a' → C} {p : a = a'}
    (r : Π⦃b : B a⦄ ⦃b' : B a'⦄ (q : b =[p] b'), f b = g b') : f =[p; λa, B a → C] g :=
  arrow_pathover (λb b' q, pathover_of_eq p (r q))

  @[hott] def arrow_pathover_constant_right {B : A → Type _} {C : Type _} {f : B a → C}
    {g : B a' → C} {p : a = a'} (r : Π(b : B a), f b = g (p ▸ b)) : f =[p; λa, B a → C] g :=
  arrow_pathover_left (λb, pathover_of_eq p (r b))

  @[hott] def arrow_pathover_constant_right_rev {A : Type _} {B : A → Type _} {C : Type _} {a a' : A}
    {f : B a → C} {g : B a' → C} {p : a = a'} (r : Π(b : B a'), f (p⁻¹ ▸ b) = g b) : f =[p; λa, B a → C] g :=
  arrow_pathover_right (λb, pathover_of_eq p (r b))

  /- a @[hott] lemma used for the flattening lemma, and is also used in the colimits file -/
  @[hott] def apo11_arrow_pathover_constant_right {f : D a → A'} {g : D a' → A'} {p : a = a'}
    {q : d =[p; D] d'} (r : Π(d : D a), f d = g (p ▸ d))
    : apo11_constant_right (arrow_pathover_constant_right r) q = r d ⬝ ap g (tr_eq_of_pathover q)
      :=
  begin
    induction q,
    eapply homotopy.rec_on r, clear r, intro r, dsimp at r, induction r,
    dsimp [apd10, arrow_pathover_constant_right, arrow_pathover_left, pathover_of_eq, eq_of_pathover_idp, tr_eq_of_pathover],
    rwr [eq_of_homotopy_idp]
  end

  /-
     The fact that the arrow type preserves truncation level is a direct consequence
     of the fact that pi's preserve truncation level
  -/
  @[hott] def is_trunc_arrow (B : Type _) (n : ℕ₋₂) [H : is_trunc n B] : is_trunc n (A → B) :=
  by apply_instance


  section hsquare
  variables {A₀₀ : Type _} {A₂₀ : Type _} {A₄₀ : Type _} 
            {A₀₂ : Type _} {A₂₂ : Type _} {A₄₂ : Type _} 
            {A₀₄ : Type _} {A₂₄ : Type _} {A₄₄ : Type _}
            {f₁₀ : A₀₀ → A₂₀} {f₃₀ : A₂₀ → A₄₀}
            {f₀₁ : A₀₀ → A₀₂} {f₂₁ : A₂₀ → A₂₂} {f₄₁ : A₄₀ → A₄₂}
            {f₁₂ : A₀₂ → A₂₂} {f₃₂ : A₂₂ → A₄₂}
            {f₀₃ : A₀₂ → A₀₄} {f₂₃ : A₂₂ → A₂₄} {f₄₃ : A₄₂ → A₄₄}
            {f₁₄ : A₀₄ → A₂₄} {f₃₄ : A₂₄ → A₄₄}

  @[hott, reducible] def hsquare (f₁₀ : A₀₀ → A₂₀) (f₁₂ : A₀₂ → A₂₂)
                                 (f₀₁ : A₀₀ → A₀₂) (f₂₁ : A₂₀ → A₂₂) : Type _ :=
  f₂₁ ∘ f₁₀ ~ f₁₂ ∘ f₀₁

  @[hott] def hsquare_of_homotopy (p : f₂₁ ∘ f₁₀ ~ f₁₂ ∘ f₀₁) : hsquare f₁₀ f₁₂ f₀₁ f₂₁ :=
  p

  @[hott] def homotopy_of_hsquare (p : hsquare f₁₀ f₁₂ f₀₁ f₂₁) : f₂₁ ∘ f₁₀ ~ f₁₂ ∘ f₀₁ :=
  p

  @[hott] def homotopy_top_of_hsquare {f₂₁ : A₂₀ ≃ A₂₂} (p : hsquare f₁₀ f₁₂ f₀₁ f₂₁) :
    f₁₀ ~ f₂₁⁻¹ᶠ ∘ f₁₂ ∘ f₀₁ :=
  homotopy_inv_of_homotopy_post _ _ _ p

  @[hott] def homotopy_top_of_hsquare' [is_equiv f₂₁] (p : hsquare f₁₀ f₁₂ f₀₁ f₂₁) :
    f₁₀ ~ f₂₁⁻¹ᶠ ∘ f₁₂ ∘ f₀₁ :=
  homotopy_inv_of_homotopy_post _ _ _ p

  @[hott] def hhconcat (p : hsquare f₁₀ f₁₂ f₀₁ f₂₁) (q : hsquare f₃₀ f₃₂ f₂₁ f₄₁) :
    hsquare (f₃₀ ∘ f₁₀) (f₃₂ ∘ f₁₂) f₀₁ f₄₁ :=
  begin have h1 := hwhisker_right f₁₀ q, have h2 := hwhisker_left f₃₂ p, exact h1 ⬝hty h2 end

  @[hott] def hvconcat (p : hsquare f₁₀ f₁₂ f₀₁ f₂₁) (q : hsquare f₁₂ f₁₄ f₀₃ f₂₃) :
    hsquare f₁₀ f₁₄ (f₀₃ ∘ f₀₁) (f₂₃ ∘ f₂₁) :=
  begin have h1 := hwhisker_left f₂₃ p, have h2 := hwhisker_right f₀₁ q, exact h1 ⬝hty h2 end

  @[hott] def hhinverse {f₁₀ : A₀₀ ≃ A₂₀} {f₁₂ : A₀₂ ≃ A₂₂} (p : hsquare f₁₀ f₁₂ f₀₁ f₂₁) :
    hsquare f₁₀⁻¹ᵉ f₁₂⁻¹ᵉ f₂₁ f₀₁ :=
  λb, eq_inv_of_eq ((p (f₁₀⁻¹ᵉ b))⁻¹ ⬝ ap f₂₁ (to_right_inv f₁₀ b))

  @[hott] def hvinverse {f₀₁ : A₀₀ ≃ A₀₂} {f₂₁ : A₂₀ ≃ A₂₂} (p : hsquare f₁₀ f₁₂ f₀₁ f₂₁) :
    hsquare f₁₂ f₁₀ f₀₁⁻¹ᵉ f₂₁⁻¹ᵉ :=
  λa, inv_eq_of_eq (p (f₀₁⁻¹ᵉ a) ⬝ ap f₁₂ (to_right_inv f₀₁ a))⁻¹

  infix ` ⬝htyh `:73 := hhconcat
  infix ` ⬝htyv `:73 := hvconcat
  postfix `⁻¹ʰᵗʸʰ`:(max+1) := hhinverse
  postfix `⁻¹ʰᵗʸᵛ`:(max+1) := hvinverse

  end hsquare

end pi
end hott