/-
Authors: Daniel Carranza, Jonathon Chang, Ryan Sandford
Under the supervision of Chris Kapulkin

Theorems about two half-adjoint equivalences, 
  including a proof that two left half-adjoint
  and two right half-adjoint equivalences are propositions

Last updated: 2020-02-20
-/

import hott.init hott.types.sigma hott.types.prod hott.types.pi hott.types.fiber hott.types.equiv .adj .prelim
open hott hott.eq

hott_theory
universes u v

-- This is used in the definition of the compatibilites for
--   a two half-adjoint and two left half-adjoint equivalence
@[hott] def nat_coh {A : Type u} {B : Type _} (g : B → A) (f : A → B) (H : g ∘ f ~ id) (x : A) 
  : H (g (f x)) = ap g (ap f (H x)) :=
cancel_right (H x) (ap_con_eq_con H (H x))⁻¹ ⬝ ap_compose g f _

namespace equiv
    variables {A B: Type u}

    -- Right coherence for two half-adjoint equivalence
    @[hott] def r2coh (f : A → B) (h : adj f) (x : A) :=
    nat_coh h.1 f h.2.1 x ⬝ ap02 h.1 (h.2.2.2.1 x) = h.2.2.2.2 (f x)

    -- Left coherence for two half-adjoint equivalence
    @[hott] def l2coh (f : A → B) (h : adj f) (y : B) :=
    h.2.2.2.1 (h.1 y) ⬝ (nat_coh f h.1 h.2.2.1 y) = ap02 f (h.2.2.2.2 y)

    -- Definition of a two (right) half-adjoint equivalence
    @[hott] def is_two_hae (f : A → B) :=
    Σ(g : B → A) (η : g ∘ f ~ id) (ε: f ∘ g ~ id) 
      (τ : Π(x : A), rcoh f ⟨g, (η, ε)⟩ x) (θ : Π(y : B), lcoh f ⟨g, (η, ε)⟩ y), 
      Π(x : A), r2coh f ⟨g, ⟨η, ⟨ε, (τ, θ)⟩⟩⟩ x

    @[hott] def is_two_hae_to_is_equiv (f : A → B) : is_two_hae f → is_equiv f :=
    λh, hott.is_equiv.mk f h.1 h.2.2.1 h.2.1 h.2.2.2.1⁻¹ʰᵗʸ

    -- Definition of a two left half-adjoint equivalence
    @[hott] def is_two_hae_l (f : A → B) :=
    Σ(g : B → A) (η : g ∘ f ~ id) (ε: f ∘ g ~ id) 
      (τ : Π(x : A), rcoh f ⟨g, (η, ε)⟩ x) (θ : Π(y : B), lcoh f ⟨g, (η, ε)⟩ y), 
      Π(y : B), l2coh f ⟨g, ⟨η, ⟨ε, (τ, θ)⟩⟩⟩ y
    
    @[hott] def is_two_hae_l_to_is_equiv (f : A → B) : is_two_hae_l f → is_equiv f :=
    λh, is_equiv.adjointify f h.1 h.2.2.1 h.2.1
    
    @[hott] def l2coh_equiv_fib_eq (f : A → B) (h : is_equiv f)
      : (Σ(l : Π(y : B), lcoh f ⟨h.inv, (h.left_inv, h.right_inv)⟩ y), 
        Π(y : B), l2coh f ⟨h.inv, ⟨h.left_inv, ⟨h.right_inv, (h.adj⁻¹ʰᵗʸ, l)⟩⟩⟩ y)
        ≃ Π(y : B), fiber.mk ((is_equiv.left_inv f) 
        ((is_equiv.inv f) y)) (h.adj⁻¹ʰᵗʸ ((is_equiv.inv f) y) ⬝ nat_coh f h.inv h.right_inv y)
        = fiber.mk (ap h.inv ((is_equiv.right_inv f) y)) rfl :=
    sigma.sigma_pi_equiv_pi_sigma
      (λ(y : B) l : lcoh f ⟨h.inv, (h.left_inv, h.right_inv)⟩ y,
        h.adj⁻¹ʰᵗʸ (is_equiv.inv f y) ⬝ (nat_coh f h.inv h.right_inv y) = ap02 f l)
    ⬝e pi.pi_equiv_pi_right (λy : B, (fiber.fiber_eq_equiv
      (fiber.mk ((is_equiv.left_inv f) ((is_equiv.inv f) y)) 
        (@concat _ _ _ _ ((is_equiv.adj f)⁻¹ʰᵗʸ ((is_equiv.inv f) y)) (nat_coh f h.inv h.right_inv y)))
      (fiber.mk (ap h.inv ((is_equiv.right_inv f) y)) rfl))⁻¹ᵉ)

    @[hott] def r2coh_equiv_fib_eq (f : A → B) (h : is_hadj_l f)
      : (Σ(r : Π(x : A), rcoh f ⟨h.1, (h.2.1, h.2.2.1)⟩ x), 
          Π(x : A), nat_coh h.1 f h.2.1 x ⬝ ap02 h.1 (r x) = h.2.2.2 (f x))
        ≃ Π(x : A), fiber.mk (ap f (h.2.1 x)) ((nat_coh h.1 f h.2.1 x)⁻¹ ⬝ h.2.2.2 (f x))
          = fiber.mk (h.2.2.1 (f x)) rfl :=
    sigma.sigma_pi_equiv_pi_sigma 
      (λ(x : A) r : rcoh f ⟨h.1, (h.2.1, h.2.2.1)⟩ x, 
        nat_coh h.1 f h.2.1 x ⬝ ap02 h.1 r = h.2.2.2 (f x))
    ⬝e pi.pi_equiv_pi_right (λx : A, @sigma.sigma_equiv_sigma_right
        _ (λr, nat_coh h.1 f h.2.1 x ⬝ ap02 h.1 r = h.2.2.2 (f x))
        (λr, (nat_coh h.1 f h.2.1 x)⁻¹ ⬝ h.2.2.2 (f x) = ap02 h.1 r)
        (λr : rcoh f ⟨h.1, (h.2.1, h.2.2.1)⟩ x, 
        (@eq_inv_con_equiv_con_eq _ _ _ _ (ap02 h.1 r) (h.2.2.2 (f x)) (nat_coh h.1 f h.2.1 x))⁻¹ᵉ
        ⬝e eq_equiv_eq_symm (ap02 h.1 r) ((nat_coh h.1 f h.2.1 x)⁻¹ ⬝ h.2.2.2 (f x))))
    ⬝e pi.pi_equiv_pi_right (λx : A, (fiber.fiber_eq_equiv 
        (fiber.mk (ap f (h.2.1 x)) ((nat_coh h.1 f h.2.1 x)⁻¹ ⬝ h.2.2.2 (f x)))
        (fiber.mk (h.2.2.1 (f x)) rfl))⁻¹ᵉ
      )

    @[hott, instance] def is_contr_r2coh (f : A → B) (h : is_hadj_l f)
      : is_contr (Σ(r : Π(x : A), rcoh f ⟨h.1, (h.2.1, h.2.2.1)⟩ x), 
        Π(x : A), nat_coh h.1 f h.2.1 x ⬝ ap02 h.1 (r x) = h.2.2.2 (f x)) :=
    @is_trunc.is_contr_equiv_closed _ _ (r2coh_equiv_fib_eq f h)⁻¹ᵉ
      (@pi.is_trunc_pi _ _ -2 (λx : A, @is_trunc.is_contr_eq _ 
        (@is_equiv.is_contr_fiber_of_is_equiv _ _ (ap h.1) (@is_equiv.is_equiv_ap _ _ h.1 
          (@is_equiv.is_equiv_inv _ _ f (equiv.is_hadj_l_equiv_is_equiv f h)) _ _) _)
          (fiber.mk (ap f (h.2.1 x)) ((nat_coh h.1 f h.2.1 x)⁻¹ ⬝ h.2.2.2 (f x))) 
          (fiber.mk (h.2.2.1 (f x)) rfl)))
    
    @[hott, instance] def is_contr_l2coh (f : A → B) (h : is_equiv f)
      : is_contr (Σ(l : Π(y : B), lcoh f ⟨h.inv, (h.left_inv, h.right_inv)⟩ y),
        Π(y : B), l2coh f ⟨h.inv, ⟨h.left_inv, ⟨h.right_inv, (h.adj⁻¹ʰᵗʸ, l)⟩⟩⟩ y) :=
    @is_trunc.is_contr_equiv_closed _ _ (l2coh_equiv_fib_eq f h)⁻¹ᵉ
      (@pi.is_trunc_pi _ _ -2 (λy : B, @is_trunc.is_contr_eq _
      (@is_equiv.is_contr_fiber_of_is_equiv _ _ (ap f) _ _)
        (fiber.mk ((is_equiv.left_inv f) ((is_equiv.inv f) y)) 
          (@concat _ _ _ _ ((is_equiv.adj f)⁻¹ʰᵗʸ ((is_equiv.inv f) y)) (nat_coh f h.inv h.right_inv y)))
        (fiber.mk (ap h.inv ((is_equiv.right_inv f) y)) rfl)))

    @[hott] def is_two_hae_reorder (f : A → B) : is_two_hae f ≃ Σ(u : Σ(g : B → A), linv g f)
      (v : Σ(ε : rinv u.1 f), Π(y : B), lcoh f ⟨u.1, (u.2, ε)⟩ y) (τ : Π(x : A), rcoh f ⟨u.1, (u.2, v.1)⟩ x), 
      Π(x : A), r2coh f ⟨u.1, ⟨u.2, ⟨v.1, (τ, v.2)⟩⟩⟩ x :=
    begin
      apply sigma.sigma_assoc_equiv (λu : Σ(g : B → A), linv g f, Σ(ε : rinv u.1 f) (τ : Π(x : A), rcoh f ⟨u.1, (u.2, ε)⟩ x) 
        (θ : Π(y : B), lcoh f ⟨u.1, (u.2, ε)⟩ y), Π(x : A), r2coh f ⟨u.1, ⟨u.2, ⟨ε, (τ, θ)⟩⟩⟩ x) ⬝e _,
      apply sigma.sigma_equiv_sigma_right, intro u,
      apply (@sigma.sigma_equiv_sigma_right _ 
        (λε : rinv u.1 f, Σ(τ : Π(x : A), rcoh f ⟨u.1, (u.2, ε)⟩ x) (θ : Π(y : B), lcoh f ⟨u.1, (u.2, ε)⟩ y), 
          Π(x : A), r2coh f ⟨u.1, ⟨u.2, ⟨ε, (τ, θ)⟩⟩⟩ x) 
        (λε : rinv u.1 f, Σ(θ : Π(y : B), lcoh f ⟨u.1, (u.2, ε)⟩ y) (τ : Π(x : A), rcoh f ⟨u.1, (u.2, ε)⟩ x), 
          Π(x : A), r2coh f ⟨u.1, ⟨u.2, ⟨ε, (τ, θ)⟩⟩⟩ x) 
        (λε : rinv u.1 f, sigma.sigma_comm_equiv 
        (λ(τ : Π(x : A), rcoh f ⟨u.1, (u.2, ε)⟩ x) (θ : Π(y : B), lcoh f ⟨u.1, (u.2, ε)⟩ y), 
        Π(x : A), r2coh f ⟨u.1, ⟨u.2, ⟨ε, (τ, θ)⟩⟩⟩ x))) ⬝e _,
      exact sigma.sigma_assoc_equiv (λv : Σ(ε : rinv u.1 f), Π(y : B), lcoh f ⟨u.1, (u.2, ε)⟩ y, 
        Σ(τ : Π(x : A), rcoh f ⟨u.1, (u.2, v.1)⟩ x), Π(x : A), r2coh f ⟨u.1, ⟨u.2, ⟨v.1, (τ, v.2)⟩⟩⟩ x)
    end

    -- Proof that two half-adjoint equivalence is a mere proposition
    @[hott, instance] def is_prop_is_two_hae (f : A → B) : is_prop (is_two_hae f) :=
    begin
      apply is_trunc.is_prop_of_imp_is_contr, intro h,
      apply is_trunc.is_trunc_equiv_closed_rev -2 (is_two_hae_reorder f),
      have H : is_equiv f := is_two_hae_to_is_equiv f h,
      apply is_trunc.is_trunc_equiv_closed_rev -2 (@sigma.sigma_equiv_of_is_contr_left _ 
          (λu : Σ(g : B → A), linv g f, Σ(v : Σ(ε : rinv u.1 f), Π(y : B), lcoh f ⟨u.1, (u.2, ε)⟩ y), 
          Σ(τ : Π(x : A), rcoh f ⟨u.1, (u.2, v.1)⟩ x), Π(x : A), r2coh f ⟨u.1, ⟨u.2, ⟨v.1, (τ, v.2)⟩⟩⟩ x) 
        (@is_contr_linv _ _ f H)),
      dsimp,
      let u := (@is_trunc.center _ (@is_contr_linv _ _ f H)),
      apply is_trunc.is_trunc_equiv_closed_rev -2 (@sigma.sigma_equiv_of_is_contr_left _ 
        (λv : Σ(ε : rinv u.1 f), Π (y : B), lcoh f ⟨u.1, (u.2, ε)⟩ y, _)
        (@is_contr_lcoh _ _ f H u)),
      dsimp,
      let v := @is_trunc.center _ (@is_contr_lcoh _ _ f H u),
      exact is_contr_r2coh f ⟨u.1, ⟨u.2, ⟨v.1, v.2⟩⟩⟩
    end

    @[hott] def is_two_hae_l_reorder (f : A → B) : is_two_hae_l f ≃ Σ(u : Σ(g : B → A), rinv g f)
      (v : Σ(η : linv u.1 f), Π(x : A), rcoh f ⟨u.1, (η, u.2)⟩ x) (θ : Π(y : B), lcoh f ⟨u.1, (v.1, u.2)⟩ y),
      Π(y : B), l2coh f ⟨u.1, ⟨v.1, ⟨u.2, (v.2, θ)⟩⟩⟩ y :=
    begin
      apply (@sigma.sigma_equiv_sigma_right _ 
        (λg : B → A, Σ(l : linv g f) (r : rinv g f), _) 
        (λg : B → A, Σ(r : rinv g f) (l : linv g f), _) 
        (λg: B → A, sigma.sigma_comm_equiv (λ(l : linv g f) (r : rinv g f), _))) ⬝e _,
      dsimp,
      apply (sigma.sigma_assoc_equiv (λu : Σ(g : B → A), rinv g f, 
        Σ(η : linv u.1 f) (τ : Π(x : A), rcoh f ⟨u.1, (η, u.2)⟩ x) (θ : Π(y : B), lcoh f ⟨u.1, (η, u.2)⟩ y), 
          Π(y : B), l2coh f ⟨u.1, ⟨η, ⟨u.2, (τ, θ)⟩⟩⟩ y)) ⬝e _,
      apply sigma.sigma_equiv_sigma_right, intro u,
      exact sigma.sigma_assoc_equiv (λv : Σ(η : linv u.1 f), Π(x : A), rcoh f ⟨u.1, (η, u.2)⟩ x, 
        Σ(θ : Π(y : B), lcoh f ⟨u.1, (v.1, u.2)⟩ y), Π(y : B), l2coh f ⟨u.1, ⟨v.1, ⟨u.2, (v.2, θ)⟩⟩⟩ y),
    end

    -- Proof that two left half-adjoint equivalence is a mere proposition
    @[hott, instance] def is_prop_is_two_hae_l (f : A → B) : is_prop (is_two_hae_l f) :=
    begin
      apply is_trunc.is_prop_of_imp_is_contr, intro h,
      have H : is_equiv f := is_two_hae_l_to_is_equiv f h,
      apply is_trunc.is_trunc_equiv_closed_rev -2 (is_two_hae_l_reorder f),
      apply is_trunc.is_trunc_equiv_closed_rev -2 (@sigma.sigma_equiv_of_is_contr_left _
        (λu: Σ(g : B → A), rinv g f, Σ(v : Σ(η : linv u.1 f), Π(x : A), rcoh f ⟨u.1, (η, u.2)⟩ x),
        Σ(θ : Π(y : B), lcoh f ⟨u.1, (v.1, u.2)⟩ y), Π(y : B), l2coh f ⟨u.1, ⟨v.1, ⟨u.2, (v.2, θ)⟩⟩⟩ y)
        (@is_equiv.is_contr_right_inverse _ _ f H)),
      dsimp,
      let u := @is_trunc.center _ (@is_equiv.is_contr_right_inverse _ _ f H),
      apply is_trunc.is_trunc_is_equiv_closed_rev -2  (@sigma.sigma_equiv_of_is_contr_left _
        (λv : Σ(η : linv u.1 f), Π(x : A), rcoh f ⟨u.1, (η, u.2)⟩ x, Σ(θ : Π(y : B), lcoh f ⟨u.1, (v.1, u.2)⟩ y), 
          Π(y : B), l2coh f ⟨u.1, ⟨v.1, ⟨u.2, (v.2, θ)⟩⟩⟩ y)
        (@is_contr_rcoh _ _ f H u)),
      dsimp,
      let v := @is_trunc.center _ (@is_contr_rcoh _ _ f H u),
      let H' := (hott.is_equiv.mk' u.1 u.2 v.1 v.2⁻¹ʰᵗʸ),
      exact transport (λH, is_contr (Σ(θ : Π(y : B), lcoh f ⟨u.1, (v.1, u.2)⟩ y), 
          Π(y : B), l2coh f ⟨u.1, ⟨v.1, ⟨u.2, (H, θ)⟩⟩⟩ y))
        (eq.inv_inv_htpy v.2) (is_contr_l2coh f H')
    end

    -- Promoting a left half-adjoint equivalence to a two half-adjoint equivalence
    @[hott] def two_adjointify (f : A → B) : is_hadj_l f → is_two_hae f :=
    λh, have _, from @is_trunc.center _ (is_contr_r2coh f h),
      ⟨h.1, ⟨h.2.1, ⟨h.2.2.1, ⟨this.1, ⟨h.2.2.2, this.2⟩⟩⟩⟩⟩
    
    -- Promoting a half-adjoint equivalence to a two left half-adjoint equivalence
    @[hott] def two_adjointify_left (f : A → B) : is_equiv f → is_two_hae_l f :=
    λh, have _, from @is_trunc.center _ (is_contr_l2coh f h),
      ⟨h.inv, ⟨h.left_inv, ⟨h.right_inv, ⟨h.adj⁻¹ʰᵗʸ, this⟩⟩⟩⟩

    -- Two half-adjoint equivalences and two left half-adjoint equivalences are equivalent
    @[hott] def two_hae_equiv_two_hae_l (f : A → B) : is_two_hae f ≃ is_two_hae_l f :=
    is_trunc.equiv_of_is_prop
      (λh : is_two_hae f, two_adjointify_left f (is_equiv.mk' h.1 h.2.2.1 h.2.1 h.2.2.2.1⁻¹ʰᵗʸ))
      (λh : is_two_hae_l f, two_adjointify f ⟨h.1, ⟨h.2.1, ⟨h.2.2.1, h.2.2.2.2.1⟩⟩⟩)

    -- Definition of a two full-adjoint equivalence
    -- Note: This is included for completeness
    @[hott] def two_adj (f : A → B) :=
    Σ(g : B → A) (η : g ∘ f ~ id) (ε: f ∘ g ~ id) 
      (τ : Π(x : A), rcoh f ⟨g, (η, ε)⟩ x) (θ : Π(y : B), lcoh f ⟨g, (η, ε)⟩ y), 
      (Π(x : A), r2coh f ⟨g, ⟨η, ⟨ε, (τ, θ)⟩⟩⟩ x)
      × Π(y : B), l2coh f ⟨g, ⟨η, ⟨ε, (τ, θ)⟩⟩⟩ y

end equiv