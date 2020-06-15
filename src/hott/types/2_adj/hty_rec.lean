/-
Authors: Daniel Carranza, Jonathon Chang, Ryan Sandford
Under the supervision of Chris Kapulkin

Contains theorems for performing induction on homotopies which
  is used in adj.lean and two_adj.lean to prove 
  full-adjoint equivalences are not mere propositions

Last updated: 2020-06-12
-/

import hott.init hott.types.equiv
open hott

hott_theory
universes u v

namespace homotopy

  variable {A : Type u}
  variable {B : A → Type v}

  @[hott] protected def rec' (f : Π(x : A), B x) (P : Π(g : Π(x : A), B x), (f = g) → Type _) (c : P f rfl)
    : Π(g : Π(x : A), B x) (p : f = g), P g p :=
  λg p, by hinduction p; exact c

  -- Based homotopy induction
  @[hott, induction] def rec {f : Π(x : A), B x} (P : Π(g : Π(x : A), B x), (f ~ g) → Type _) (c : P f (λx, refl (f x)))
    : Π(g : Π(x : A), B x) (H : f ~ g), P g H :=
  λg H, transport (λX : f ~ g, P g X) (is_equiv.right_inv (eq_equiv_homotopy f g) H) 
    (homotopy.rec' f (λg p, P g (eq_equiv_homotopy f g p)) c g ((eq_equiv_homotopy f g).to_inv H))
    
  -- Unbased homotopy induction
  -- Note: this is not used in adj.lean or two_adj.lean but is included here for completeness
  @[hott, induction] def rec_unbased {P : Π(f g : Π(x : A), B x), (f ~ g) → Type _} (c : Π(f : Π(x : A), B x), P f f (λx, refl (f x)))
    : Π(f g : Π(x : A), B x) (H : f ~ g), P f g H :=
  λf g H, rec (P f) (c f) g H

end homotopy

namespace is_trunc

    variable {A : Type u}
    variable {B : A → Type _}
  
    @[hott, instance] def sigma_hty_is_contr (f : Π(x : A), B x) : is_contr (Σ(g : Π(x : A), B x), f ~ g) :=
    is_trunc.is_contr.mk ⟨f, λx, rfl⟩ 
      (λu, by induction u; apply @homotopy.rec _ _ f (λg H, @sigma.mk (Π(x : A), B x) (λg, f ~ g) f (λx, hott.eq.refl (f x)) = sigma.mk g (λx, H x)) rfl u_fst u_snd)

    @[hott, instance] def sigma_hty_is_contr_right (f : Π(x : A), B x) : is_contr (Σ(g : Π(x : A), B x), g ~ f) :=
    @is_trunc.is_trunc_equiv_closed (Σ(g : Π(x : A), B x), f ~ g) (Σ(g : Π(x : A), B x), g ~ f) -2 
      (sigma.sigma_equiv_sigma_right (λg, pi.pi_equiv_pi_right (λx, eq_equiv_eq_symm (f x) (g x)))) 
      (sigma_hty_is_contr f)
      
end is_trunc