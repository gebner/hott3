/-
Authors: Daniel Carranza, Jonathan Chang, Ryan Sandford
Under the supervision of Chris Kapulkin
-/

import hott.init hott.types.sigma hott.types.prod hott.types.pi hott.types.fiber hott.types.equiv

open hott hott.eq

hott_theory
universes u v

section

    variable {A: Type u}
    variable {B: Type v}

    @[hott] def linv (g: B → A) (f: A → B) : Type _ := g ∘ f ~ id

    @[hott] def rinv (g: B → A) (f: A → B) : Type _ := f ∘ g ~ id

    @[hott] def has_linv (f: A → B) : Type _ := Σ(g: B → A), linv g f

    @[hott] def has_rinv (f: A → B) : Type _ := Σ(g: B → A), rinv g f

    @[hott] def qinv (f: A → B) : Type _ := Σ(g: B → A), linv g f × rinv g f

    @[hott] def qinv_to_is_equiv {f: A → B} 
            : qinv f → is_equiv f :=
        λ e, is_equiv.adjointify f e.1 e.2.2 e.2.1

    @[hott] def is_contr_has_linv (f: A → B) (e: qinv f) 
            : is_contr (has_linv f) :=
        begin 
            apply is_trunc.is_trunc_equiv_closed -2,
            exact sigma.sigma_equiv_sigma_right 
                (λ g: B → A, (eq_equiv_homotopy (g ∘ f) id)),
            apply is_trunc.is_trunc_equiv_closed -2,
            exact fiber.sigma_char 
                (pi.arrow_equiv_arrow_left A (equiv.mk f (qinv_to_is_equiv e))⁻¹ᵉ).to_fun
                id,
            exact @is_equiv.is_contr_fiber_of_is_equiv _ _
                (pi.arrow_equiv_arrow_left A (equiv.mk f (qinv_to_is_equiv e))⁻¹ᵉ).to_fun
                (pi.arrow_equiv_arrow_left A (equiv.mk f (qinv_to_is_equiv e))⁻¹ᵉ).to_is_equiv
                id
        end

    @[hott] def is_contr_has_rinv (f: A → B) (e: qinv f)
            : is_contr (has_rinv f) :=
        begin
            apply is_trunc.is_trunc_equiv_closed -2,
            exact sigma.sigma_equiv_sigma_right 
                (λ g: B → A, (eq_equiv_homotopy (f ∘ g) id)),
            apply is_trunc.is_trunc_equiv_closed -2,
            exact fiber.sigma_char 
                (pi.arrow_equiv_arrow_right B (equiv.mk f (qinv_to_is_equiv e))).to_fun
                id,
            exact @is_equiv.is_contr_fiber_of_is_equiv _ _
                (pi.arrow_equiv_arrow_right B (equiv.mk f (qinv_to_is_equiv e))).to_fun
                (pi.arrow_equiv_arrow_right B (equiv.mk f (qinv_to_is_equiv e))).to_is_equiv
                id
        end

    @[hott] def rcoh (f: A → B) (h: qinv f) (x: A)
            : Type _ :=
        ap f (h.2.1 x) = h.2.2 (f x)

    @[hott] def lcoh (f: A → B) (h: qinv f) (y: B)
            : Type _ :=
        h.2.1 (h.1 y) = ap h.1 (h.2.2 y)

    @[hott] def is_hae (f: A → B) : Type _ :=
        Σ(h: qinv f), Π(x: A), rcoh f h x
    
    @[hott] def is_hae_to_is_equiv {f: A → B}
            : is_hae f → is_equiv f :=
        λ e: is_hae f, is_equiv.mk' e.1.1 e.1.2.2 e.1.2.1 (λ x: A, (e.2 x)⁻¹)

    @[hott] def ap_g_is_equiv {f: A → B} (e: qinv f) (b b': B)
            : is_equiv (@ap B A e.1 b b') :=
        @is_equiv.is_equiv_ap _ _ e.1 (@is_equiv.is_equiv_inv _ _ f (qinv_to_is_equiv e)) _ _

    @[hott] def is_hae_l (f: A → B) : Type _ :=
        Σ(h: qinv f), Π(y: B), lcoh f h y

    @[hott] def is_contr_lcoh (f: A → B) (h: qinv f)
            : is_contr Σ(r: rinv h.1 f), Π(y: B), lcoh f ⟨h.1, (h.2.1, r)⟩ y :=
        begin
            apply is_trunc.is_trunc_equiv_closed -2,
            exact (sigma.sigma_pi_equiv_pi_sigma
                (λ (y: B) (r: f (h.1 y) = y), h.2.1 (h.1 y) = ap h.1 r))⁻¹ᵉ,
            apply pi.is_trunc_pi _ -2,
            intro y,
            apply is_trunc.is_trunc_equiv_closed -2,
            exact fiber.fiber_eq_equiv
                (fiber.mk (f (h.1 y)) (h.2.1 (h.1 y)))
                (fiber.mk y rfl),
            apply @is_trunc.is_contr_eq _ _,
            
            refine @is_equiv.is_contr_fiber_of_is_equiv _ _
                h.1 (_: _) (h.1 y),
            exact @is_equiv.is_equiv_inv _ _ f (qinv_to_is_equiv h)
        end

    @[hott] def is_hae_l_equiv_sigma_char (f: A → B)
            : is_hae_l f ≃ Σ(l: has_linv f) (r: rinv l.1 f), 
                                Π(y: B), lcoh f ⟨l.1, (l.2, r)⟩ y :=
        begin
            apply hott.equiv.trans,
            exact (sigma.sigma_assoc_equiv
                (λ u: qinv f, Π(y: B), lcoh f u y))⁻¹ᵉ,
            apply hott.equiv.trans,
            exact sigma.sigma_equiv_sigma_right
                (λ g: B → A, @sigma.sigma_equiv_sigma_left _ (Σ(l: linv g f), rinv g f)
                    (λ p: linv g f × rinv g f, Π(y: B), lcoh f ⟨g, p⟩ y)
                    (@hott.equiv.symm (Σ(l: linv g f), rinv g f) _ (sigma.equiv_prod (linv g f) (rinv g f)))
                ),
            dsimp,
            apply hott.equiv.trans,
            exact sigma.sigma_equiv_sigma_right
                (λ g: B → A, 
                    (sigma.sigma_assoc_equiv
                        (λ u: Σ(l: linv g f), rinv g f, Π (y : B), lcoh f ⟨g, (sigma.equiv_prod (linv g f) (rinv g f)).to_fun u⟩ y))⁻¹ᵉ
                ),
            exact sigma.sigma_assoc_equiv
                (λ l: has_linv f, Σ(r: rinv l.1 f), Π(y: B), lcoh f ⟨l.1, (l.2, r)⟩ y)
        end

    @[hott] def is_hae_l_is_contr (f: A → B) (h: is_hae_l f)
            : is_contr (is_hae_l f) :=
        begin
            refine is_trunc.is_trunc_equiv_closed -2
                (is_hae_l_equiv_sigma_char f)⁻¹ᵉ
                (@sigma.is_trunc_sigma _ (λ l: has_linv f, Σ(r: rinv l.1 f), Π(y: B), lcoh f ⟨l.1, (l.2, r)⟩ y) -2
                    (is_contr_has_linv f h.1)
                    (λ l: has_linv f, _: _)
                ),
            dsimp,
            have := (@is_trunc.eq_of_is_contr _ (is_contr_has_linv f h.1) ⟨h.1.1, h.1.2.1⟩ l),
            exact is_contr_lcoh f ⟨l.1, (l.2, transport (λ g: B → A, rinv g f) this..1 h.1.2.2)⟩
        end

    @[hott] def fae (f: A → B) : Type _ :=
    Σ(h: qinv f), (Π(x: A), rcoh f h x) × (Π(y: B), lcoh f h y)

end 