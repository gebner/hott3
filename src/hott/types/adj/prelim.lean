/-
Authors: Daniel Carranza, Jonathon Chang, Ryan Sandford
Under the supervision of Chris Kapulkin

Some auxiliary lemmas used in adj.lean and two_adj.lean

Last updated: 2020-02-20
-/

import hott.init hott.types.equiv
open hott

hott_theory
universes u v
namespace pi
    variable {A : Type u}
    variable {B : Type v} 
    variable {C : Type _}

    @[hott] def precompose (f : A → B) : (B → C) → (A → C) :=
    λg, g ∘ f
    
    @[hott] def precompose_equiv_is_equiv (f : A → B) [H: is_equiv f]
      : is_equiv (@precompose A B C f) :=
    is_equiv.adjointify (precompose f) 
      (λg: A → C, g ∘ f⁻¹ᶠ)
      (λg, eq_of_homotopy (λx, ap g (is_equiv.left_inv f x) ))
      (λg, eq_of_homotopy (λx, ap g (is_equiv.right_inv f x)))
    
    @[hott] def precompose_equiv (f : A → B) [H : is_equiv f]
      : (B → C) ≃ (A → C) :=
    equiv.mk (precompose f) (precompose_equiv_is_equiv f)
    
    @[hott] def postcompose (f : B → C) : (A → B) → (A → C) :=
    λg, f ∘ g 

    @[hott] def postcompose_equiv_is_equiv (f : B → C) [H : is_equiv f]
      : is_equiv (@postcompose A B C f) :=
    is_equiv.adjointify (postcompose f)
      (λg : A → C, f⁻¹ᶠ ∘ g)
      (λg, eq_of_homotopy (λx, is_equiv.right_inv f _))
      (λg, eq_of_homotopy (λx, is_equiv.left_inv f _)) 
    
    @[hott] def postcompose_equiv (f : B → C) [H : is_equiv f]
      : (A → B) ≃ (A → C) :=
    equiv.mk (postcompose f) (postcompose_equiv_is_equiv f)
    
    @[hott] def eq_equiv_eq_htpy {P : A → Type _} {f g h k : Π(x : A), P x}
      (H : f ~ h) (H₂ : g ~ k) : f = g ≃ h = k :=
    eq_equiv_eq_closed (eq_of_homotopy H) (eq_of_homotopy H₂)

    @[hott] def htpy_equiv_htpy_closed {P : A → Type _} {f g h k : Π(x : A), P x}
      (H : f ~ h) (H₂ : g ~ k) : f ~ g ≃ h ~ k :=
    (eq_equiv_homotopy f g)⁻¹ᵉ ⬝e eq_equiv_eq_htpy H H₂ ⬝e eq_equiv_homotopy h k

    @[hott] def htpy_of_htpy_to_path_of_path {f g : A → B} (H H₂ : f ~ g)
      : (H ~ H₂) ≃ (eq_of_homotopy H = eq_of_homotopy H₂) :=
    (eq_equiv_homotopy H H₂)⁻¹ᵉ ⬝e equiv_ap eq_of_homotopy H H₂

    @[hott] def htpy_square_equiv_path_concat {P : A → Type _} {f₁ g₁ h₁ f₂ g₂ h₂ : Π(x : A), P x} 
      (F : f₁ = f₂) (G : g₁ = g₂) (H : h₁ = h₂) (α : f₁ = g₁) (β : g₁ = h₁)
      : (eq_equiv_eq_closed F G) α ⬝ (eq_equiv_eq_closed G H) β
        = eq_equiv_eq_closed F H (α ⬝ β) :=
    by hinduction G; hinduction H; hinduction β; reflexivity

end pi

namespace eq

  @[hott] def inv_inv_htpy {A : Type u} {P : A → Type _} {f g : Π(x : A), P x} 
    (H : f ~ g) : (H⁻¹ʰᵗʸ)⁻¹ʰᵗʸ = H :=
  eq_of_homotopy (λx, inv_inv (H x))

end eq
