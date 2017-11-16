/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn

n-truncation of types.

Ported from Coq HoTT
-/

/- The hit n-truncation is primitive, declared in init.hit. -/

import types.sigma types.pointed
universes u v w
hott_theory
namespace hott
open hott.is_trunc hott.eq hott.equiv hott.is_equiv function prod sum sigma

namespace trunc

  @[hott, induction, priority 1500] protected def elim {n : ℕ₋₂} {A : Type _} {P : Type _}
    [Pt : is_trunc n P] (H : A → P) : trunc n A → P :=
  trunc.rec H

  @[hott] protected def elim_on {n : ℕ₋₂} {A : Type _} {P : Type _} (aa : trunc n A)
    [Pt : is_trunc n P] (H : A → P) : P :=
  trunc.elim H aa

  variables {X : Type _} {Y : Type _} {Z : Type _} {P : X → Type _} {m : ℕ₋₂} (n : ℕ₋₂) (A : Type _) (B : Type _)

  @[hott] def untrunc_of_is_trunc [H : is_trunc m X] : trunc m X → X :=
  trunc.rec id

  variables (A n)
  @[hott, instance] def is_equiv_tr [H : is_trunc n A] : is_equiv (@tr n A) :=
  adjointify _
             (untrunc_of_is_trunc)
             (λaa, trunc.rec_on aa (λa, idp))
             (λa, idp)

  @[hott] def trunc_equiv [H : is_trunc n A] : trunc n A ≃ A :=
  (equiv.mk tr (is_equiv_tr n A))⁻¹ᵉ

  @[hott] def is_trunc_of_is_equiv_tr [H : is_equiv (@tr n A)] : is_trunc n A :=
  is_trunc_is_equiv_closed_rev n (@tr n A) (by infer)

  /- Functoriality -/
  @[hott] def trunc_functor (f : X → Y) : trunc n X → trunc n Y :=
  λxx, trunc.rec_on xx (λx, tr (f x))

  @[hott] def trunc_functor_compose (f : X → Y) (g : Y → Z)
    : trunc_functor n (g ∘ f) ~ trunc_functor n g ∘ trunc_functor n f :=
  λxx, trunc.rec_on xx (λx, idp)

  @[hott] def trunc_functor_id : trunc_functor n (@id A) ~ id :=
  λxx, trunc.rec_on xx (λx, idp)

  @[hott] def trunc_functor_cast {X Y : Type _} (n : ℕ₋₂) (p : X = Y) :
    trunc_functor n (cast p) ~ cast (ap (trunc n) p) :=
  begin
    intro x, hinduction x using trunc.rec with x,
    exact fn_tr_eq_tr_fn p (λy, tr) x ⬝ tr_eq_cast_ap _ _
  end

  @[hott] def is_equiv_trunc_functor (f : X → Y) [H : is_equiv f]
    : is_equiv (trunc_functor n f) :=
  adjointify _
             (trunc_functor n f⁻¹ᶠ)
             (λyy, trunc.rec_on yy (λy, ap tr (right_inv _ _)))
             (λxx, trunc.rec_on xx (λx, ap tr (left_inv _ _)))

  @[hott] def trunc_homotopy {f g : X → Y} (p : f ~ g) : trunc_functor n f ~ trunc_functor n g :=
  λxx, trunc.rec_on xx (λx, ap tr (p x))

  section
    @[hott] def trunc_equiv_trunc (f : X ≃ Y) : trunc n X ≃ trunc n Y :=
    equiv.mk _ (is_equiv_trunc_functor n f)
  end

  section
  
  @[hott] def trunc_prod_equiv : trunc n (X × Y) ≃ trunc n X × trunc n Y :=
  begin
    fapply equiv.MK,
    { exact (λpp, trunc.rec_on pp (λp, (tr p.1, tr p.2))) },
    { intro p, induction p with xx yy,
      hinduction xx with x, hinduction yy with y, exact tr (x,y) },
    { intro p, induction p with xx yy,
      hinduction xx with x, hinduction yy with y, refl },
    { intro pp, hinduction pp with p, induction p, refl }
  end
  end

  /- Propositional truncation -/

  @[hott] def ttrunc (n : ℕ₋₂) (X : Type _) : n-Type :=
  trunctype.mk (trunc n X) (by infer)

  @[hott, hsimp] def carrier_ttrunc (n : ℕ₋₂) (X : Type _) : @coe_sort _ (hott.has_coe_to_sort n) (ttrunc n X) = trunc n X :=
  by refl

  @[hott, reducible] def merely (A : Type _) : Prop := ttrunc -1 A

  notation `∥`:max A `∥`:0   := merely A

  @[hott, reducible] def Exists (P : X → Type _) : Prop := ∥ sigma P ∥
  @[hott, reducible] def or (A B : Type _) : Prop := ∥ A ⊎ B ∥
  hott_theory_cmd "local notation `exists` binders `,` r:(scoped P, hott.trunc.Exists P) := r"
  hott_theory_cmd "local notation `∃` binders `,` r:(scoped P, Exists P) := r"
  hott_theory_cmd "local notation A ` \\/ ` B := or A B"
  hott_theory_cmd "local notation A ∨ B    := or A B"
  @[hott, reducible] def merely.intro   (a : A) : ∥ A ∥             := tr a
  @[hott, reducible] def exists.intro   (x : X) (p : P x) : ∃x, P x := tr ⟨x, p⟩
  @[hott, reducible] def or.intro_left  (x : X) : X ∨ Y             := tr (inl x)
  @[hott, reducible] def or.intro_right (y : Y) : X ∨ Y             := tr (inr y)

  @[hott, induction] def merely.rec {A : Type u} {P : ∥A∥ → Type v} [Pt : Π (aa : ∥A∥), is_prop (P aa)]
  (H : Π(a : A), P (tr a)) (x : ∥A∥) : P x :=
  begin dsimp [merely] at x, hinduction x with a, exact H a end 

  @[hott, induction] def exists.elim {A : Type _} {p : A → Type _} {B : Type _} [is_prop B] (H : Exists p)
    (H' : ∀ (a : A), p a → B) : B :=
  begin hinduction H with x, induction x with a x, exact H' a x end 

  @[hott] def is_contr_of_merely_prop [H : is_prop A] (aa : merely A) : is_contr A :=
  is_contr_of_inhabited_prop (trunc.rec_on aa id)

  @[hott] def trunc_sigma_equiv : trunc n (Σ x, P x) ≃ trunc n (Σ x, trunc n (P x)) :=
  begin 
    fapply equiv.MK; intro x,
    { hinduction x with p, exact tr ⟨p.1, tr p.2⟩ },
    { hinduction x with p, induction p with a p, hinduction p with p, exact tr ⟨a, p⟩ },
    { hinduction x with p, induction p with a p, hinduction p with p, refl },
    { hinduction x with p, induction p with a p, refl }
  end

  @[hott] def trunc_sigma_equiv_of_is_trunc [H : is_trunc n X]
    : trunc n (Σ x, P x) ≃ Σ x, trunc n (P x) :=
  calc
    trunc n (Σ x, P x) ≃ trunc n (Σ x, trunc n (P x)) : trunc_sigma_equiv _
      ... ≃ Σ x, trunc n (P x) : trunc_equiv _ _

  /- the (non-dependent) universal property -/
  @[hott] def trunc_arrow_equiv [H : is_trunc n B] :
    (trunc n A → B) ≃ (A → B) :=
  begin
    fapply equiv.MK,
    { intros g a, exact g (tr a) },
    { intros f x, hinduction x with a, exact f a },
    { intro f, apply eq_of_homotopy, intro a, refl },
    { intro g, apply eq_of_homotopy, intro x, hinduction x, refl },
  end

end trunc
end hott