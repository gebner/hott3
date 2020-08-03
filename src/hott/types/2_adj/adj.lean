/-
Authors: Daniel Carranza, Jonathon Chang, Ryan Sandford
Under the supervision of Chris Kapulkin

Theorems about half-adjoint equivalences, including
  a proof that the left half-adjoint type is a proposition
  and is equivalent to the built-in equivalence type
  
Last updated: 2020-07-31
-/

import hott.init hott.types.sigma hott.types.prod hott.types.pi hott.types.equiv .prelim
universes u v

hott_theory
namespace hott
open hott hott.eq hott.is_trunc hott.sigma

namespace equiv
    variables {A B: Type u}

    @[hott] def linv (g : B → A) (f : A → B) := 
    Π(a : A), g (f a) = a

    @[hott] def rinv (g : B → A) (f : A → B) := 
    Π(b : B), f (g b) = b
    
    @[hott] def qinv (f : A → B) := 
    Σ(g : B → A), linv g f × rinv g f

    @[hott, reducible] def qinv.inv {f : A → B} (h : qinv f) := h.1
    @[hott, reducible] def qinv.η {f : A → B} (h : qinv f) := h.2.1
    @[hott, reducible] def qinv.ε {f : A → B} (h : qinv f) := h.2.2

    @[hott, instance] def is_contr_linv (f : A → B) [H : is_equiv f]
      : is_contr Σ(g : B → A), linv g f :=
    begin
      apply is_trunc.is_trunc_equiv_closed -2,
      exact sigma.sigma_equiv_sigma_right 
       (λ g: B → A, (eq_equiv_homotopy (g ∘ f) id)),
      apply is_trunc.is_trunc_equiv_closed -2,
      exact @fiber.sigma_char _ _ (pi.precompose f) id,
      exact @is_equiv.is_contr_fiber_of_is_equiv _ _
        (pi.precompose f) (pi.precompose_equiv_is_equiv f) id
    end

    @[hott] def qinv_id_equiv_sigma_prod : qinv (@id A) ≃ Π(x : A), x = x :=
    sigma_equiv_sigma_right (λg : A → A, (equiv_prod (g ~ id) (g ~ id))⁻¹ᵉ)
    ⬝e sigma_assoc_equiv (λu : Σ(g : A → A), g ~ id, u.1 ~ id)
    ⬝e sigma_equiv_of_is_contr_left (λu : Σ(g : A → A), g ~ id, u.1 ~ id)

    -- qinv is not a mere proposition
    @[hott] def qinv_equiv_pi_eq (f: A ≃ B)
      : qinv f.to_fun ≃ Π(x : A), x = x :=
    by apply rec_on_ua_idp f; exact qinv_id_equiv_sigma_prod
    
    @[hott] def rcoh (f : A → B) (h: qinv f) (x : A) := 
    ap f (h.η x) = h.ε (f x)

    @[hott] def lcoh (f : A → B) (h: qinv f) (y : B) :=
    h.η (h.inv y) = ap h.inv (h.ε y)

    -- Definition of a left half-adjoint equivalence
    @[hott] def is_hadj_l (f : A → B) :=
    Σ(g : B → A) (η : linv g f) (ε : rinv g f), Π(y : B), lcoh f ⟨g, (η, ε)⟩ y

    @[hott, reducible] def is_hadj_l.inv {f : A → B} (h : is_hadj_l f) := h.1
    @[hott, reducible] def is_hadj_l.η {f : A → B} (h : is_hadj_l f) := h.2.1
    @[hott, reducible] def is_hadj_l.ε {f : A → B} (h : is_hadj_l f) := h.2.2.1
    @[hott, reducible] def is_hadj_l.θ {f : A → B} (h : is_hadj_l f) := h.2.2.2

    -- Note: A proof of a similar statement is found under types.equiv
    -- This proof is included here for compatibility 
    --  with the definitions above and in two_adj.lean
    @[hott, instance] def is_contr_rcoh (f : A → B) [H : is_equiv f] (u : Σ(g : B → A), rinv g f)
      : is_contr(Σ(l : linv u.1 f), Π(x : A), rcoh f ⟨u.1, (l, u.2)⟩ x) :=
    begin
      apply @is_trunc.is_trunc_equiv_closed_rev _ (Σ(l : linv u.1 f), Π(x : A), u.2 (f x) = ap f (l x)) -2,
      apply sigma.sigma_equiv_sigma_right, intro η,
      apply pi.pi_equiv_pi_right, intro x,
      apply (eq_equiv_eq_symm (u.2 (f x)) (ap f (η x)))⁻¹ᵉ,
      exact is_equiv.is_contr_right_coherence f u
    end

    @[hott, instance] def is_contr_lcoh (f : A → B) [H : is_equiv f] (u : Σ(g : B → A), linv g f)
      : is_contr(Σ(r : rinv u.1 f), Π(y : B), lcoh f ⟨u.1, (u.2, r)⟩ y) :=
    begin
      apply is_trunc.is_trunc_equiv_closed_rev -2
        (sigma.sigma_pi_equiv_pi_sigma (λy, λr : f (u.1 y) = y, u.2 (u.1 y) = ap u.1 r)),
      apply is_trunc.is_trunc_equiv_closed -2 (pi.pi_equiv_pi_right (
        λy : B, @fiber.fiber_eq_equiv _ _ u.1 (u.1 y) 
        (fiber.mk (f (u.1 y)) (u.2 (u.1 y))) (fiber.mk y rfl) 
      )),
      have : f⁻¹ᶠ = u.1 := 
        (@is_trunc.eq_of_is_contr _ (is_contr_linv f) ⟨f⁻¹ᶠ, is_equiv.left_inv f⟩ u)..1,
      have : is_equiv u.1 := is_equiv.is_equiv_eq_closed this,
      exact @pi.is_trunc_pi _ _ -2 (λy, 
        @is_trunc.is_contr_eq _ (@is_equiv.is_contr_fiber_of_is_equiv _ _ u.1 this (u.1 y)) 
        (fiber.mk (f (u.1 y)) (u.2 (u.1 y)))
        (fiber.mk y rfl))
    end

    -- Left half-adjoint equivalence is a mere proposition
    @[hott, instance] def is_prop_hadj_l (f : A → B) : is_prop (is_hadj_l f) :=
    begin
      apply is_trunc.is_prop_of_imp_is_contr, intro h,
      apply is_trunc.is_trunc_equiv_closed_rev -2 (
        sigma.sigma_assoc_equiv (λu: Σ(g : B → A), linv g f, 
        Σ(r : rinv u.1 f), Π(y : B), lcoh f ⟨u.1, (u.2, r)⟩ y)
      ),
      have H : is_equiv f := is_equiv.adjointify f h.inv h.ε h.η,
      apply is_trunc.is_trunc_equiv_closed_rev -2 (
        @sigma.sigma_equiv_of_is_contr_left _ (λu : Σ(g : B → A), linv g f, 
          Σ(r : rinv u.1 f), Π(y : B), lcoh f ⟨u.1, (u.2, r)⟩ y)
            (@is_contr_linv _ _ f H)),
      exact @is_contr_lcoh _ _ f H _
    end

    -- Left half-adjoint equivalence is equivalent to is_equiv
    @[hott] def is_hadj_l_equiv_is_equiv (f : A → B) : is_hadj_l f ≃ is_equiv f :=
    is_trunc.equiv_of_is_prop 
      (λh : is_hadj_l f, is_equiv.adjointify f h.inv h.ε h.η)
      (λH : is_equiv f, 
      have Σ(r : rinv H.inv f), Π(y : B), lcoh f ⟨H.inv, (H.left_inv, r)⟩ y, 
        from @is_trunc.center _ (@is_contr_lcoh _ _ f H ⟨H.inv, H.left_inv⟩),
      ⟨H.inv, ⟨H.left_inv, this⟩⟩)

    -- Promoting qinv to a left half-adjoint
    @[hott] def adjointify_left (f : A → B) (inv : B → A) (left_inv : linv inv f) (right_inv : rinv inv f)
      : is_hadj_l f :=
    is_equiv.inv (is_hadj_l_equiv_is_equiv f) (is_equiv.adjointify f inv right_inv left_inv)

    -- Definition of a full-adjoint equivalence
    @[hott] def adj (f : A → B) :=
    Σ(g : B → A) (η : g ∘ f ~ id) (ε : f ∘ g ~ id), 
      (Π(x : A), rcoh f ⟨g, (η, ε)⟩ x) × (Π(y : B), lcoh f ⟨g, (η, ε)⟩ y)

    @[hott, reducible] def adj.inv {f : A → B} (h : adj f) := h.1
    @[hott, reducible] def adj.η {f : A → B} (h : adj f) := h.2.1
    @[hott, reducible] def adj.ε {f : A → B} (h : adj f) := h.2.2.1
    @[hott, reducible] def adj.τ {f : A → B} (h : adj f) := h.2.2.2.1
    @[hott, reducible] def adj.θ {f : A → B} (h : adj f) := h.2.2.2.2

    @[hott] def id_adj_equiv_no_linv 
      : adj (@id A) ≃ Σ(ε : @id A ~ id), (Π(x : A), rfl = ε x) × (Π(x : A), rfl = ap id (ε x)) :=
    sigma.sigma_assoc_equiv 
      (λu : Σ(g : A → A), g ~ id, Σ(ε : u.1 ~ id), (Π(x : A), ap id (u.2 x) = ε x) × (Π(x : A), u.2 (u.1 x) = ap u.1 (ε x)))
      ⬝e @sigma.sigma_equiv_of_is_contr_left _
        (λu : Σ(g : A → A), g ~ id, Σ(ε : u.1 ~ id), (Π(x : A), ap id (u.2 x) = ε x) × (Π(x : A), u.2 (u.1 x) = ap u.1 (ε x)))
        (is_trunc.sigma_hty_is_contr_right id)

    @[hott] def id_adj_equiv_no_rcoh
      : (Σ(ε : @id A ~ id), (Π(x : A), rfl = ε x) × (Π(x : A), rfl = ap id (ε x)))
        ≃ Π(x : A), hott.eq.refl x = rfl :=
    @sigma.sigma_equiv_sigma_right (@id A ~ id) 
        (λε, (Π(x : A), rfl = ε x) × (Π(x : A), rfl = ap id (ε x))) _
        (λε, (sigma.equiv_prod (Π(x : A), rfl = ε x) (Π(x : A), rfl = ap id (ε x)))⁻¹ᵉ)
      ⬝e sigma.sigma_assoc_equiv
        (λu : Σ(ε : @id A ~ id), Π(x : A), rfl = ε x, Π(x : A), rfl = ap id (u.1 x))
      ⬝e @sigma.sigma_equiv_of_is_contr_left _
        (λu : Σ(ε : @id A ~ id), Π(x : A), rfl = ε x, Π(x : A), rfl = ap id (u.1 x))
        (is_trunc.sigma_hty_is_contr hott.eq.refl)

    -- Full-adjoint equivalence is not a mere proposition
    -- Note: This is a formalization of exercise 4.1 in the HoTT book
    @[hott] def adj_equiv_pi_refl_eq (f: A ≃ B) : adj f ≃ Π(x: A), refl x = refl x :=
    by apply equiv.rec_on_ua_idp f; exact id_adj_equiv_no_linv ⬝e id_adj_equiv_no_rcoh
    
end equiv

end hott