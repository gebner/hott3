/-
Authors: Daniel Carranza, Jonathan Chang, Ryan Sandford
Under the supervision of Chris Kapulkin
-/

import hott.init hott.types.sigma hott.types.prod hott.types.pi hott.types.fiber hott.types.equiv .adj

open hott hott.eq

hott_theory
universes u v

section

    variable {A: Type u}
    variable {B: Type v}
    
    @[hott] def nat_homotopy {A : Type u} {B : Type _} (g : B → A) (f : A → B) (H : g ∘ f ~ id) (x : A) 
      : H (g (f x)) = ap g (ap f (H x)) :=
    cancel_right (H x) (ap_con_eq_con H (H x))⁻¹ ⬝ ap_compose g f _

    @[hott] def r2coh (f: A → B) (h: fae f) (x: A)
            : Type _ :=
        (nat_homotopy h.1.1 f h.1.2.1 x)⁻¹ ⬝ h.2.2 (f x) = ap02 h.1.1 (h.2.1 x)
    
    @[hott] def l2coh (f: A → B) (h: fae f) (y: B)
            : Type _ :=
        h.2.1 (h.1.1 y) ⬝ nat_homotopy f h.1.1 h.1.2.2 y = ap02 f (h.2.2 y)

    @[hott] def is_2hae (f: A → B) : Type _ :=
        Σ(h: fae f), Π(x: A), r2coh f h x 
    
    @[hott] def is_2hae_l (f: A → B) : Type _ :=
        Σ(h: fae f), Π(y: B), l2coh f h y

    @[hott] def two_fae (f: A → B) : Type _ :=
        Σ(h: fae f), (Π(x: A), r2coh f h x) × (Π(y: B), l2coh f h y)

    @[hott] def is_contr_r2coh (f: A → B) (h: is_hae_l f)
            : is_contr Σ(r: Π(x: A), rcoh f h.1 x), Π(x: A), r2coh f ⟨h.1, (r, h.2)⟩ x :=
        begin
            fapply is_trunc.is_trunc_equiv_closed -2,
                exact (sigma.sigma_pi_equiv_pi_sigma 
                    (λ (x: A) (r: rcoh f h.1 x), 
                        (nat_homotopy h.1.1 f h.1.2.1 x)⁻¹ ⬝ h.2 (f x) = ap02 h.1.1 r
                    ))⁻¹ᵉ,
            apply pi.is_trunc_pi _ -2,
                intro x,
                fapply is_trunc.is_trunc_equiv_closed -2,
                exact fiber.fiber_eq_equiv 
                    (fiber.mk (ap f (h.1.2.1 x)) ((nat_homotopy h.1.1 f h.1.2.1 x)⁻¹ ⬝ h.2 (f x)))
                    (fiber.mk (h.1.2.2 (f x)) rfl),
                apply is_trunc.is_contr_eq _ _,
                exact @is_equiv.is_contr_fiber_of_is_equiv _ _ (ap h.1.1) (ap_g_is_equiv h.1 _ _) _
        end
    
    @[hott] def is_2hae_equiv_sigma_char (f: A → B)
            : is_2hae f ≃ Σ(u: is_hae_l f), Σ(r: Π(x: A), rcoh f u.1 x), Π(x: A), r2coh f ⟨u.1, (r, u.2)⟩ x :=
        begin
            apply hott.equiv.trans,
            exact (sigma.sigma_assoc_equiv (λ e: fae f, Π(x: A), r2coh f e x))⁻¹ᵉ,
            apply hott.equiv.trans,
            apply sigma.sigma_equiv_sigma_right,
            intro q,
            apply (
                sigma.sigma_equiv_sigma_left 
                    (λ p: (Π(x: A), rcoh f q x) × (Π(y: B), lcoh f q y), 
                        Π(x: A), r2coh f ⟨q, p⟩ x) 
                    (prod.prod_comm_equiv _ _)
            ),
            apply hott.equiv.trans,
            dsimp,
            apply sigma.sigma_equiv_sigma_right,
            intro q,
            apply (
                sigma.sigma_equiv_sigma_left
                    (λ p: (Π(y: B), lcoh f q y) × (Π(x: A), rcoh f q x),
                        Π(x: A), r2coh f ⟨q, (prod.prod_comm_equiv _ _).to_inv p⟩ x)
                    (sigma.equiv_prod _ _)⁻¹ᵉ
            ),
            apply hott.equiv.trans,
            apply sigma.sigma_equiv_sigma_right,
            intro q,
            dsimp,
            exact (sigma.sigma_assoc_equiv 
                (λ u: Σ(l: Π(y: B), lcoh f q y), 
                        Π(x: A), rcoh f q x, Π(x: A), 
                r2coh f ⟨q,
            ((prod.prod_comm_equiv (Π (x : A), rcoh f q x) (Π (y : B), lcoh f q y)).to_fun)⁻¹ᶠ
              ((sigma.equiv_prod (Π (y : B), lcoh f q y) (Π (x : A), rcoh f q x)).to_fun u)⟩ x))⁻¹ᵉ,
            exact (sigma.sigma_assoc_equiv (λ e: is_hae_l f, Σ(r: Π(x: A), rcoh f e.1 x), Π(x: A), r2coh f ⟨e.1, (r, e.2)⟩ x)),
        end
    
    @[hott] def is_2hae_is_contr (f: A → B) (h: is_2hae f) 
            : is_contr (is_2hae f) :=  
        begin
            apply is_trunc.is_trunc_equiv_closed -2 (is_2hae_equiv_sigma_char f)⁻¹ᵉ,
            refine @sigma.is_trunc_sigma _ (λ e: Σ(q: qinv f), Π(y: B), lcoh f q y, Σ(r: Π(x: A), rcoh f e.1 x), Π(x: A), r2coh f ⟨e.1, (r, e.2)⟩ x) -2 (_: _) (_: _),
            exact is_hae_l_is_contr f ⟨h.1.1, h.1.2.2⟩,
            exact is_contr_r2coh f
        end

    @[hott] def fae_to_2hae (f: A → B) : fae f → is_2hae f :=
        λ e, begin
            have u : Π(h: is_hae_l f), 
                    Σ(r: Π(x: A), rcoh f h.1 x), 
                        Π(x: A), r2coh f ⟨h.1, (r, h.2)⟩ x
                := λ h, @is_trunc.center _ (is_contr_r2coh f h),
            exact ⟨⟨e.1, ((u ⟨e.1, e.2.2⟩).1, e.2.2)⟩, (u ⟨e.1, e.2.2⟩).2⟩ 
        end

end 