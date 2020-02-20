/-
Authors: Daniel Carranza, Jonathon Chang, Ryan Sandford
Under the supervision of Chris Kapulkin

Theorems about half-adjoint equivalences, including
  a proof that the left half-adjoint type is a proposition
  and is equivalent to the built-in equivalence type
  
Last updated: 2020-02-20
-/

import hott.init hott.types.sigma hott.types.prod hott.types.pi hott.types.equiv .prelim
open hott hott.eq

hott_theory
universes u v

namespace equiv
    variables {A B: Type u}

    @[hott] def linv (g : B → A) (f : A → B) := 
    Π(a : A), g (f a) = a

    @[hott] def rinv (g : B → A) (f : A → B) := 
    Π(b : B), f (g b) = b
    
    @[hott] def qinv (f : A → B) := 
    Σ(g : B → A), linv g f × rinv g f

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

    @[hott] def qinv_id_equiv_sigma_prod 
      : qinv (@id A) ≃ Σ(g : A → A), g = id × g = id :=
    sigma.sigma_equiv_sigma_right 
      (λg, prod.prod_equiv_prod ((eq_equiv_homotopy g id)⁻¹ᵉ) (eq_equiv_homotopy g id)⁻¹ᵉ)

    @[hott] def qinv_id_sigma_prod_equiv_sigma_sigma 
      : (Σ(g: A → A), g = id × g = id) ≃ Σ(g : A → A) (h : g = id), g = id := 
    sigma.sigma_equiv_sigma_right (λg, (sigma.equiv_prod _ _)⁻¹ᵉ)

    @[hott] def qinv_id_sigma_sigma_equiv_id_eq
      : (Σ(g: A → A) (h : g = id), g = id) ≃ @id A = id :=
    sigma.sigma_assoc_equiv (λh : Σg : A → A, g = id, h.1 = id)
      ⬝e sigma.sigma_equiv_of_is_contr_left (λh : Σg : A → A, g = id, h.1 = id)
    
    -- qinv is not a mere proposition
    @[hott] def qinv_equiv_pi_eq (f: A ≃ B)
      : qinv f.to_fun ≃ Π(x : A), x = x :=
    by apply equiv.rec_on_ua_idp f; exact qinv_id_equiv_sigma_prod 
      ⬝e qinv_id_sigma_prod_equiv_sigma_sigma 
      ⬝e qinv_id_sigma_sigma_equiv_id_eq 
      ⬝e (eq_equiv_homotopy _ _)
    
    @[hott] def rcoh (f : A → B) (h: qinv f) (x : A) := 
    ap f (h.2.1 x) = h.2.2 (f x)

    @[hott] def lcoh (f : A → B) (h: qinv f) (y : B) :=
    h.2.1 (h.1 y) = ap h.1 (h.2.2 y)

    -- Definition of a left half-adjoint equivalence
    @[hott] def is_hadj_l (f : A → B) :=
    Σ(g : B → A) (η : linv g f) (ε : rinv g f), Π(y : B), lcoh f ⟨g, (η, ε)⟩ y

    -- Note: A proof of a similar statement is found under types.equiv
    -- This proof is included here for compatibility 
    ---  with the definitions above and in two_adj.lean
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
      have H : is_equiv f := is_equiv.adjointify f h.1 h.2.2.1 h.2.1,
      apply is_trunc.is_trunc_equiv_closed_rev -2 (
        @sigma.sigma_equiv_of_is_contr_left _ (λu : Σ(g : B → A), linv g f, 
          Σ(r : rinv u.1 f), Π(y : B), lcoh f ⟨u.1, (u.2, r)⟩ y)
            (@is_contr_linv _ _ f H)),
      exact @is_contr_lcoh _ _ f H _
    end

    -- Left half-adjoint equivalence is equivalent to is_equiv
    @[hott] def is_hadj_l_equiv_is_equiv (f : A → B) : is_hadj_l f ≃ is_equiv f :=
    is_trunc.equiv_of_is_prop 
      (λh : is_hadj_l f, is_equiv.adjointify f h.1 h.2.2.1 h.2.1)
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

    @[hott] def ap_id_htpy {f g : A → B} (H : f ~ g) : Π(x : A), ap id (H x) = H x :=
      λx, ap_id (H x)

    @[hott] def id_htpy_eq_htpy {f g : A → B} (H : f ~ g) : (λx, ap id (H x)) = H :=
      eq_of_homotopy (ap_id_htpy H)

    @[hott] def htpy_id_to_id' {f : A → A} (p : id = f) (H H₂ : f ~ id) 
      : ((λx, H (f x)) ~ (λx, ap f (H₂ x))) ≃ (H ~ (λx, ap id (H₂ x))) :=
    by hinduction p; reflexivity

    @[hott] def htpy_id_to_id {f : A → A} (H H₂ : f ~ id) 
      : ((λx, H (f x)) ~ (λx, ap f (H₂ x))) ≃ (H ~ (λx, ap id (H₂ x))) :=
    htpy_id_to_id' (eq_of_homotopy H)⁻¹ _ _

    @[hott] def id_adj_equiv_sigma_prod
      : adj (@id A) ≃ Σ(g : A → A) (η ε : g = id), η = ε × η = ε :=
    begin
      apply sigma.sigma_equiv_sigma_right, intro g,
      apply sigma.sigma_equiv_sigma (eq_equiv_homotopy g id)⁻¹ᵉ, intro η,
      apply sigma.sigma_equiv_sigma (eq_equiv_homotopy g id)⁻¹ᵉ, intro ε,
      exact prod.prod_equiv_prod 
        (pi.htpy_equiv_htpy_closed (ap_id_htpy η) (λx, rfl) ⬝e pi.htpy_of_htpy_to_path_of_path η ε)
        (htpy_id_to_id η ε ⬝e pi.htpy_equiv_htpy_closed (λx, rfl) (ap_id_htpy ε) 
          ⬝e pi.htpy_of_htpy_to_path_of_path η ε)
    end

    @[hott] def id_adj_sigma_prod_equiv_sigma_sigma
      : (Σ(g : A → A) (η ε : g = id), η = ε × η = ε) 
        ≃ Σ(g : A → A) (η ε : g = id) (τ : η = ε), η = ε :=
    sigma.sigma_equiv_sigma_right (λg, sigma.sigma_equiv_sigma_right 
      (λη, sigma.sigma_equiv_sigma_right (λε, (sigma.equiv_prod _ _)⁻¹ᵉ)))
    
    @[hott] def id_adj_sigma_sigma_equiv_refl_id_eq
      : (Σ(g : A → A) (η ε : g = id) (τ : η = ε), η = ε) ≃ refl (@id A) = refl id :=
    by apply sigma.sigma_assoc_equiv (λh : Σ(g : A → A), g = id, Σ(ε: h.1 = id) (τ: h.2 = ε), h.2 = ε)
      ⬝e sigma.sigma_equiv_of_is_contr_left 
        (λh : Σ(g : A → A), g = id, Σ(ε: h.1 = id) (τ: h.2 = ε), h.2 = ε)
      ⬝e sigma.sigma_assoc_equiv (λh : Σ(ε : id = id), rfl = ε, rfl = h.1)
      ⬝e sigma.sigma_equiv_of_is_contr_left (λh : Σ(ε : id = id), rfl = ε, rfl = h.1)

    @[hott] def refl_id_eq_refl_id_eq_pi_refl_eq
      : (refl (@id A) = refl id) ≃ Π(x: A), refl x = refl x :=
    equiv.eq_equiv_fn_eq_of_equiv (eq_equiv_homotopy (@id A) id) rfl rfl
      ⬝e (eq_equiv_homotopy _ _)

    -- Full-adjoint equivalence is not a mere proposition
    -- Note: this is a formalization of exercise 4.1 in the HoTT book
    @[hott] def adj_equiv_pi_refl_eq (f: A ≃ B) : adj f ≃ Π(x: A), refl x = refl x :=
    by apply equiv.rec_on_ua_idp f; exact id_adj_equiv_sigma_prod 
      ⬝e id_adj_sigma_prod_equiv_sigma_sigma ⬝e id_adj_sigma_sigma_equiv_refl_id_eq 
      ⬝e refl_id_eq_refl_id_eq_pi_refl_eq
    
end equiv