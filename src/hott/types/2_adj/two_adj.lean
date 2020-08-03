/-
Authors: Daniel Carranza, Jonathon Chang, Ryan Sandford
Under the supervision of Chris Kapulkin

Theorems about two half-adjoint equivalences, 
  including a proof that two left half-adjoint
  and two right half-adjoint equivalences are propositions
  and that the two full-adjoint equivalence is equivalent to a non-propositional type 

Last updated: 2020-07-31
-/

import hott.init hott.types.sigma hott.types.prod hott.types.pi hott.types.fiber hott.types.equiv .adj .prelim
universes u v

hott_theory
namespace hott
open hott hott.eq hott.is_trunc hott.sigma

-- This is used in the definition of the compatibilites for
--   a two half-adjoint and two left half-adjoint equivalence
@[hott] def nat_coh {A : Type u} {B : Type _} (g : B → A) (f : A → B) (H : g ∘ f ~ id) (x : A) 
  : H (g (f x)) = ap g (ap f (H x)) :=
cancel_right (H x) (ap_con_eq_con H (H x))⁻¹ ⬝ ap_compose g f _

namespace equiv
    variables {A B: Type u}

    -- Right coherence for two half-adjoint equivalence
    @[hott] def r2coh (f : A → B) (h : adj f) (x : A) :=
    nat_coh h.inv f h.η x ⬝ ap02 h.inv (h.τ x) = h.θ (f x)

    -- Left coherence for two half-adjoint equivalence
    @[hott] def l2coh (f : A → B) (h : adj f) (y : B) :=
    h.τ (h.inv y) ⬝ (nat_coh f h.inv h.ε y) = ap02 f (h.θ y)

    -- Definition of a two (right) half-adjoint equivalence
    @[hott] def is_two_hae (f : A → B) :=
    Σ(g : B → A) (η : g ∘ f ~ id) (ε: f ∘ g ~ id) 
      (τ : Π(x : A), rcoh f ⟨g, (η, ε)⟩ x) (θ : Π(y : B), lcoh f ⟨g, (η, ε)⟩ y), 
      Π(x : A), r2coh f ⟨g, ⟨η, ⟨ε, (τ, θ)⟩⟩⟩ x

    @[hott, reducible] def is_two_hae.inv {f : A → B} (h : is_two_hae f) := h.1
    @[hott, reducible] def is_two_hae.η {f : A → B} (h : is_two_hae f) := h.2.1
    @[hott, reducible] def is_two_hae.ε {f : A → B} (h : is_two_hae f) := h.2.2.1
    @[hott, reducible] def is_two_hae.τ {f : A → B} (h : is_two_hae f) := h.2.2.2.1
    @[hott, reducible] def is_two_hae.θ {f : A → B} (h : is_two_hae f) := h.2.2.2.2.1
    @[hott, reducible] def is_two_hae.α {f : A → B} (h : is_two_hae f) := h.2.2.2.2.2

    @[hott] def is_two_hae_to_is_equiv (f : A → B) : is_two_hae f → is_equiv f :=
    λh, hott.is_equiv.mk f h.inv h.ε h.η h.τ⁻¹ʰᵗʸ

    -- Definition of a two left half-adjoint equivalence
    @[hott] def is_two_hae_l (f : A → B) :=
    Σ(g : B → A) (η : g ∘ f ~ id) (ε: f ∘ g ~ id) 
      (τ : Π(x : A), rcoh f ⟨g, (η, ε)⟩ x) (θ : Π(y : B), lcoh f ⟨g, (η, ε)⟩ y), 
      Π(y : B), l2coh f ⟨g, ⟨η, ⟨ε, (τ, θ)⟩⟩⟩ y

    @[hott, reducible] def is_two_hae_l.inv {f : A → B} (h : is_two_hae_l f) := h.1
    @[hott, reducible] def is_two_hae_l.η {f : A → B} (h : is_two_hae_l f) := h.2.1
    @[hott, reducible] def is_two_hae_l.ε {f : A → B} (h : is_two_hae_l f) := h.2.2.1
    @[hott, reducible] def is_two_hae_l.τ {f : A → B} (h : is_two_hae_l f) := h.2.2.2.1
    @[hott, reducible] def is_two_hae_l.θ {f : A → B} (h : is_two_hae_l f) := h.2.2.2.2.1
    @[hott, reducible] def is_two_hae_l.β {f : A → B} (h : is_two_hae_l f) := h.2.2.2.2.2
    
    @[hott] def is_two_hae_l_to_is_equiv (f : A → B) : is_two_hae_l f → is_equiv f :=
    λh, is_equiv.adjointify f h.inv h.ε h.η
    
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
      : (Σ(r : Π(x : A), rcoh f ⟨h.inv, (h.η, h.ε)⟩ x), 
          Π(x : A), nat_coh h.inv f h.η x ⬝ ap02 h.inv (r x) = h.θ (f x))
        ≃ Π(x : A), fiber.mk (ap f (h.η x)) ((nat_coh h.inv f h.η x)⁻¹ ⬝ h.θ (f x))
          = fiber.mk (h.ε (f x)) rfl :=
    sigma.sigma_pi_equiv_pi_sigma 
      (λ(x : A) r : rcoh f ⟨h.inv, (h.η, h.ε)⟩ x, 
        nat_coh h.inv f h.η x ⬝ ap02 h.inv r = h.θ (f x))
    ⬝e pi.pi_equiv_pi_right (λx : A, @sigma.sigma_equiv_sigma_right
        _ (λr, nat_coh h.inv f h.η x ⬝ ap02 h.inv r = h.θ (f x))
        (λr, (nat_coh h.inv f h.η x)⁻¹ ⬝ h.θ (f x) = ap02 h.inv r)
        (λr : rcoh f ⟨h.inv, (h.η, h.ε)⟩ x, 
        (@eq_inv_con_equiv_con_eq _ _ _ _ (ap02 h.inv r) (h.θ (f x)) (nat_coh h.inv f h.η x))⁻¹ᵉ
        ⬝e eq_equiv_eq_symm (ap02 h.inv r) ((nat_coh h.inv f h.η x)⁻¹ ⬝ h.θ (f x))))
    ⬝e pi.pi_equiv_pi_right (λx : A, (fiber.fiber_eq_equiv 
        (fiber.mk (ap f (h.η x)) ((nat_coh h.inv f h.η x)⁻¹ ⬝ h.θ (f x)))
        (fiber.mk (h.ε (f x)) rfl))⁻¹ᵉ
      )

    @[hott, instance] def is_contr_r2coh (f : A → B) (h : is_hadj_l f)
      : is_contr (Σ(r : Π(x : A), rcoh f ⟨h.inv, (h.η, h.ε)⟩ x), 
        Π(x : A), nat_coh h.inv f h.η x ⬝ ap02 h.inv (r x) = h.θ (f x)) :=
    @is_trunc.is_contr_equiv_closed _ _ (r2coh_equiv_fib_eq f h)⁻¹ᵉ
      (@pi.is_trunc_pi _ _ -2 (λx : A, @is_trunc.is_contr_eq _ 
        (@is_equiv.is_contr_fiber_of_is_equiv _ _ (ap h.inv) (@is_equiv.is_equiv_ap _ _ h.inv
          (@is_equiv.is_equiv_inv _ _ f (equiv.is_hadj_l_equiv_is_equiv f h)) _ _) _)
          (fiber.mk (ap f (h.η x)) ((nat_coh h.inv f h.η x)⁻¹ ⬝ h.θ (f x))) 
          (fiber.mk (h.ε (f x)) rfl)))
    
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
      ⟨h.inv, ⟨h.η, ⟨h.ε, ⟨this.1, ⟨h.θ, this.2⟩⟩⟩⟩⟩
    
    -- Promoting a half-adjoint equivalence to a two left half-adjoint equivalence
    @[hott] def two_adjointify_left (f : A → B) : is_equiv f → is_two_hae_l f :=
    λh, have _, from @is_trunc.center _ (is_contr_l2coh f h),
      ⟨h.inv, ⟨h.left_inv, ⟨h.right_inv, ⟨h.adj⁻¹ʰᵗʸ, this⟩⟩⟩⟩

    -- Two half-adjoint equivalences and two left half-adjoint equivalences are equivalent
    @[hott] def two_hae_equiv_two_hae_l (f : A → B) : is_two_hae f ≃ is_two_hae_l f :=
    is_trunc.equiv_of_is_prop
      (λh : is_two_hae f, two_adjointify_left f (is_equiv.mk' h.inv h.ε h.η h.τ⁻¹ʰᵗʸ))
      (λh : is_two_hae_l f, two_adjointify f ⟨h.inv, ⟨h.η, ⟨h.ε, h.θ⟩⟩⟩)

    -- Definition of a two full-adjoint equivalence
    @[hott] def two_adj (f : A → B) :=
    Σ(g : B → A) (η : g ∘ f ~ id) (ε: f ∘ g ~ id) 
      (τ : Π(x : A), rcoh f ⟨g, (η, ε)⟩ x) (θ : Π(y : B), lcoh f ⟨g, (η, ε)⟩ y), 
      (Π(x : A), r2coh f ⟨g, ⟨η, ⟨ε, (τ, θ)⟩⟩⟩ x)
      × Π(y : B), l2coh f ⟨g, ⟨η, ⟨ε, (τ, θ)⟩⟩⟩ y

    @[hott, reducible] def two_adj.inv {f : A → B} (h : two_adj f) := h.1
    @[hott, reducible] def two_adj.η {f : A → B} (h : two_adj f) := h.2.1
    @[hott, reducible] def two_adj.ε {f : A → B} (h : two_adj f) := h.2.2.1
    @[hott, reducible] def two_adj.τ {f : A → B} (h : two_adj f) := h.2.2.2.1
    @[hott, reducible] def two_adj.θ {f : A → B} (h : two_adj f) := h.2.2.2.2.1
    @[hott, reducible] def two_adj.α {f : A → B} (h : two_adj f) := h.2.2.2.2.2.1
    @[hott, reducible] def two_adj.β {f : A → B} (h : two_adj f) := h.2.2.2.2.2.2

    @[hott] def two_adj_id_equiv_no_linv
      : two_adj (@id A) ≃ Σ(ε : @id A ~ id) (τ : Π(x : A), rfl = ε x) (θ : Π(x : A), rfl = ap id (ε x)), 
        (Π(x : A), nat_coh id id (@hott.eq.refl A) x ⬝ ap02 id (τ x) = θ x) × (Π(x : A), τ x ⬝ nat_coh id id ε x = ap02 id (θ x)) :=
    sigma.sigma_assoc_equiv (λu : Σ(g : A → A), g ~ id, Σ(ε : u.1 ~ id) (τ : Π(x : A), ap id (u.2 x) = ε x) (θ : Π(x : A), u.2 (u.1 x) = ap u.1 (ε x)), (Π(x : A), nat_coh u.1 id u.2 x ⬝ ap02 u.1 (τ x) = θ x) × (Π(x : A), τ (u.1 x) ⬝ nat_coh id u.1 ε x = ap02 id (θ x)))
      ⬝e @sigma.sigma_equiv_of_is_contr_left _
          (λu : Σ(g : A → A), g ~ id, Σ(ε : u.1 ~ id) (τ : Π(x : A), ap id (u.2 x) = ε x) (θ : Π(x : A), u.2 (u.1 x) = ap u.1 (ε x)), (Π(x : A), nat_coh u.1 id u.2 x ⬝ ap02 u.1 (τ x) = θ x) × (Π(x : A), τ (u.1 x) ⬝ nat_coh id u.1 ε x = ap02 id (θ x)))
          (is_trunc.sigma_hty_is_contr_right (@id A))

    @[hott] def two_adj_id_equiv_no_rcoh
      : (Σ(ε : @id A ~ id) (τ : Π(x : A), rfl = ε x) (θ : Π(x : A), rfl = ap id (ε x)), 
        (Π(x : A), nat_coh id id (@hott.eq.refl A) x ⬝ ap02 id (τ x) = θ x) × (Π(x : A), τ x ⬝ nat_coh id id ε x = ap02 id (θ x)))
         ≃ Σ(θ : Π(x : A), rfl = ap id (hott.eq.refl x)), (Π(x : A), nat_coh id id (@hott.eq.refl A) x ⬝ ap02 id rfl = θ x) × (Π(x : A), rfl ⬝ nat_coh id id (@hott.eq.refl A) x = ap02 id (θ x)) :=
    sigma.sigma_assoc_equiv (λu : Σ(ε : @id A ~ id), Π(x : A), rfl = ε x, Σ(θ : Π(x : A), rfl = ap id (u.1 x)), (Π(x : A), nat_coh id id (@hott.eq.refl A) x ⬝ ap02 id (u.2 x) = θ x) × (Π(x : A), u.2 x ⬝ nat_coh id id u.1 x = ap02 id (θ x)))
      ⬝e @sigma.sigma_equiv_of_is_contr_left _
        (λu : Σ(ε : @id A ~ id), hott.eq.refl ~ ε, Σ(θ : Π(x : A), rfl = ap id (u.1 x)), (Π(x : A), nat_coh id id (@hott.eq.refl A) x ⬝ ap02 id (u.2 x) = θ x) × (Π(x : A), u.2 x ⬝ nat_coh id id u.1 x = ap02 id (θ x)))
        (is_trunc.sigma_hty_is_contr (@hott.eq.refl A))

    @[hott] def two_adj_id_equiv_no_rcoh_simplify
      : (Σ(θ : Π(x : A), rfl = ap id (hott.eq.refl x)), (Π(x : A), nat_coh id id (@hott.eq.refl A) x ⬝ ap02 id rfl = θ x) × (Π(x : A), rfl ⬝ nat_coh id id (@hott.eq.refl A) x = ap02 id (θ x)))
        ≃ Σ(θ : Π(x : A), hott.eq.refl x = hott.eq.refl x), (Π(x : A), hott.eq.refl (hott.eq.refl x) = θ x) × (Π(x : A), hott.eq.refl (hott.eq.refl x) = θ x) :=
    begin
      fapply sigma.sigma_equiv_sigma_right, intro θ,
      apply prod.prod_equiv_prod,
      refl,
      apply pi.pi_equiv_pi_right, intro x,
      exact eq_equiv_eq_closed rfl (@ap_con_eq_con _ (λp : x = x, ap id p) (λp, ap_id p) _ _ (θ x) ⬝ idp_con (θ x))
    end

    @[hott] def two_adj_id_equiv_no_r2coh
      : (Σ(θ : Π(x : A), hott.eq.refl x = hott.eq.refl x), (Π(x : A), hott.eq.refl (hott.eq.refl x) = θ x) × (Π(x : A), hott.eq.refl (hott.eq.refl x) = θ x))
        ≃ Π(x : A), rfl = hott.eq.refl (hott.eq.refl x) :=
    @sigma.sigma_equiv_sigma_right (Π(x : A), rfl = hott.eq.refl x) 
        (λθ, (Π(x : A), rfl = θ x) × (Π(x : A), rfl = θ x) ) _ 
        (λθ, (sigma.equiv_prod (Π(x : A), rfl = θ x) (Π(x : A), rfl = θ x))⁻¹ᵉ)
      ⬝e sigma.sigma_assoc_equiv (λu : Σ(θ : Π(x : A), rfl = hott.eq.refl x), Π(x : A), rfl = θ x, Π(x : A), rfl = u.1 x)
      ⬝e @sigma.sigma_equiv_of_is_contr_left _
        (λu : Σ(θ : Π(x : A), rfl = hott.eq.refl x), Π(x : A), rfl = θ x, Π(x : A), rfl= u.1 x)
        (is_trunc.sigma_hty_is_contr (λx : A, @hott.eq.refl (x = x) (hott.eq.refl x)))

    -- Two full-adjoint equivalence is not a mere proposition
    @[hott] def two_adj_equiv_pi_refl_eq (f : A ≃ B) : two_adj f ≃ Π(x : A), hott.eq.refl (hott.eq.refl x) = rfl :=
    by apply equiv.rec_on_ua_idp f; exact two_adj_id_equiv_no_linv
      ⬝e two_adj_id_equiv_no_rcoh
      ⬝e two_adj_id_equiv_no_rcoh_simplify
      ⬝e two_adj_id_equiv_no_r2coh

end equiv

end hott