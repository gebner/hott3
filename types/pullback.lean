/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Floris van Doorn

Theorems about pullbacks
-/

import cubical.square

universes u v w
hott_theory

namespace hott

open hott.eq hott.equiv hott.is_equiv function hott.prod unit is_trunc hott.sigma

variables {A₀₀ : Type _} 
          {A₂₀ : Type _}  
          {A₄₀ : Type _} 
          {A₀₂ : Type _} 
          {A₂₂ : Type _} 
          {A₄₂ : Type _}
          (f₁₀ : A₀₀ → A₂₀) (f₃₀ : A₂₀ → A₄₀)
          (f₀₁ : A₀₀ → A₀₂) (f₂₁ : A₂₀ → A₂₂) (f₄₁ : A₄₀ → A₄₂)
          (f₁₂ : A₀₂ → A₂₂) (f₃₂ : A₂₂ → A₄₂)

structure pullback (f₂₁ : A₂₀ → A₂₂) (f₁₂ : A₀₂ → A₂₂) :=
  (fst : A₂₀)
  (snd : A₀₂)
  (fst_snd : f₂₁ fst = f₁₂ snd)

namespace pullback

  @[hott] protected def sigma_char :
    pullback f₂₁ f₁₂ ≃ Σ(a₂₀ : A₂₀) (a₀₂ : A₀₂), f₂₁ a₂₀ = f₁₂ a₀₂ :=
  begin
    fapply equiv.MK,
    { intro x, induction x with a₂₀ a₀₂ p, exact ⟨a₂₀, a₀₂, p⟩},
    { intro x, induction x with a₂₀ y, induction y with a₀₂ p, exact pullback.mk a₂₀ a₀₂ p},
    { intro x, induction x with a₂₀ y, induction y with a₀₂ p, reflexivity},
    { intro x, induction x with a₂₀ a₀₂ p, reflexivity},
  end

  variables {f₁₀ f₃₀ f₀₁ f₂₁ f₄₁ f₁₂ f₃₂}

  @[hott] def pullback_corec (p : Πa, f₂₁ (f₁₀ a) = f₁₂ (f₀₁ a)) (a : A₀₀)
    : pullback f₂₁ f₁₂ :=
  pullback.mk (f₁₀ a) (f₀₁ a) (p a)

  @[hott] def pullback_eq {x y : pullback f₂₁ f₁₂} (p1 : fst x = fst y) (p2 : snd x = snd y)
    (r : square (fst_snd x) (fst_snd y) (ap f₂₁ p1) (ap f₁₂ p2)) : x = y :=
  begin 
  induction y,
  induction x, 
  dsimp at *,
  induction p1, 
  induction p2,
  exact ap (pullback.mk _ _) (eq_of_vdeg_square r) 
  end

  @[hott] def pullback_comm_equiv : pullback f₁₂ f₂₁ ≃ pullback f₂₁ f₁₂ :=
  begin
    fapply equiv.MK,
    { intro v, induction v with x y p, exact pullback.mk y x p⁻¹},
    { intro v, induction v with x y p, exact pullback.mk y x p⁻¹},
    { intro v, induction v, dsimp, exact ap _ (inv_inv _)},
    { intro v, induction v, dsimp, exact ap _ (inv_inv _)},
  end

  @[hott] def pullback_unit_equiv
    : pullback (λ(x : A₀₂), star) (λ(x : A₂₀), star) ≃ A₀₂ × A₂₀ :=
  begin
    fapply equiv.MK,
    { intro v, induction v with x y p, exact (x, y)},
    { intro v, induction v with x y, exact pullback.mk x y idp},
    { intro v, induction v, reflexivity},
    { intro v, induction v, dsimp, apply ap _ (is_prop.elim  _ _), 
    apply_instance
    },
  end

  @[hott] def pullback_along {f : A₂₀ → A₂₂} (g : A₀₂ → A₂₂) : pullback f g → A₂₀ :=
  fst

  postfix `^*`:(max+1) := pullback_along

  variables (f₁₀ f₃₀ f₀₁ f₂₁ f₄₁ f₁₂ f₃₂)

  structure pullback_square (f₁₀ : A₀₀ → A₂₀) (f₁₂ : A₀₂ → A₂₂) (f₀₁ : A₀₀ → A₀₂) (f₂₁ : A₂₀ → A₂₂)
     :=
    (comm : Πa, f₂₁ (f₁₀ a) = f₁₂ (f₀₁ a))
    (is_pullback : is_equiv (pullback_corec comm : A₀₀ → pullback f₂₁ f₁₂))

  attribute [instance] pullback_square.is_pullback 
  @[hott] def pbs_comm := @pullback_square.comm

  @[hott] def pullback_square_pullback
    : pullback_square (fst : pullback f₂₁ f₁₂ → A₂₀) f₁₂ snd f₂₁ :=
  pullback_square.mk
    fst_snd
    (adjointify _ (λf, f)
                  (λf, by induction f; reflexivity)
                  (λg, by induction g; reflexivity))

  variables {f₁₀ f₃₀ f₀₁ f₂₁ f₄₁ f₁₂ f₃₂}

  @[hott] def pullback_square_equiv (s : pullback_square f₁₀ f₁₂ f₀₁ f₂₁)
    : A₀₀ ≃ pullback f₂₁ f₁₂ :=
  equiv.mk _ (pullback_square.is_pullback s)

  @[hott] def of_pullback (s : pullback_square f₁₀ f₁₂ f₀₁ f₂₁)
    (x : pullback f₂₁ f₁₂) : A₀₀ :=
  inv (pullback_square_equiv s) x

  @[hott] def right_of_pullback (s : pullback_square f₁₀ f₁₂ f₀₁ f₂₁)
    (x : pullback f₂₁ f₁₂) : f₁₀ (of_pullback s x) = fst x :=
  ap fst (to_right_inv (pullback_square_equiv s) x)

  @[hott] def down_of_pullback (s : pullback_square f₁₀ f₁₂ f₀₁ f₂₁)
    (x : pullback f₂₁ f₁₂) : f₀₁ (of_pullback s x) = snd x :=
  ap snd (to_right_inv (pullback_square_equiv s) x)

  -- @[hott] def pullback_square_compose_inverse (s : pullback_square f₁₀ f₁₂ f₀₁ f₂₁)
  --   (t : pullback_square f₃₀ f₃₂ f₂₁ f₄₁) (x : pullback f₄₁ (f₃₂ ∘ f₁₂)) : A₀₀ :=
  -- let a₂₀' : pullback f₄₁ f₃₂ :=
  --   pullback.mk (fst x) (f₁₂ (snd x)) (fst_snd x) in
  -- let a₂₀ : A₂₀ :=
  --   of_pullback t a₂₀' in
  -- have a₀₀' : pullback f₂₁ f₁₂,
  --   from pullback.mk a₂₀ (snd x) !down_of_pullback,
  -- show A₀₀,
  --   from of_pullback s a₀₀'
  -- local attribute pullback_square_compose_inverse [reducible]

  -- @[hott] def down_psci (s : pullback_square f₁₀ f₁₂ f₀₁ f₂₁)
  --   (t : pullback_square f₃₀ f₃₂ f₂₁ f₄₁) (x : pullback f₄₁ (f₃₂ ∘ f₁₂)) :
  --    f₀₁ (pullback_square_compose_inverse s t x) = snd x :=
  -- by apply down_of_pullback

  -- @[hott] def pullback_square_compose (s : pullback_square f₁₀ f₁₂ f₀₁ f₂₁)
  --   (t : pullback_square f₃₀ f₃₂ f₂₁ f₄₁) : pullback_square (f₃₀ ∘ f₁₀) (f₃₂ ∘ f₁₂) f₀₁ f₄₁ :=
  -- pullback_square.mk
  --   (λa, pbs_comm t (f₁₀ a) ⬝ ap f₃₂ (pbs_comm s a))
  --   (adjointify _
  --     (pullback_square_compose_inverse s t)
  --     begin
  --       intro x, induction x with x y p, esimp,
  --       fapply pullback_eq: esimp,
  --       { exact ap f₃₀ !right_of_pullback ⬝ !right_of_pullback},
  --       { apply down_of_pullback},
  --       { esimp, exact sorry }
  --     end
  --     begin
  --       intro x, esimp, exact sorry
  --     end)
end pullback
end hott
