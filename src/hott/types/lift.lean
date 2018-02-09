/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Floris van Doorn

Theorems about lift
-/

import ..function
universes u v w
hott_theory
namespace hott
open hott.equiv hott.is_equiv is_trunc pointed ulift

namespace ulift

  variables {A : Type u} (z z' : ulift.{v u} A)

  @[hott] protected def eta : up (down z) = z :=
  by induction z; reflexivity

  @[hott] protected def code : ulift A → ulift A → Type _
  | (up a) (up a') := a = a'

  @[hott] protected def decode : Π(z z' : ulift A), ulift.code z z' → z = z'
  | (up a) (up a') := λc, ap up c

  variables {z z'}
  @[hott] protected def encode (p : z = z') : ulift.code z z' :=
  by induction p; induction z; exact idp

  variables (z z')
  @[hott] def ulift_eq_equiv : (z = z') ≃ ulift.code z z' :=
  equiv.MK ulift.encode
           (ulift.decode z z')
           begin abstract {
             intro c, induction z with a, induction z' with a', induction c, reflexivity
           } end 
           begin abstract {
             intro p, induction p, induction z, reflexivity
           } end


  section
  variables {a a' : A}
  @[hott] def eq_of_up_eq_up (p : up a = up a') : a = a' :=
  ulift.encode p

  @[hott] def ulift_transport {P : A → Type _} (p : a = a') (z : ulift (P a))
    : p ▸ z = up (p ▸ down z) :=
  by induction p; induction z; reflexivity
  end

  variables {A' : Type _} (f : A → A') (g : ulift A → ulift A')
  @[hott] def ulift_functor : ulift A → ulift A'
  | (up a) := up (f a)

  @[hott] def is_equiv_ulift_functor [Hf : is_equiv f] : is_equiv (ulift_functor f) :=
  adjointify (ulift_functor f)
             (ulift_functor f⁻¹ᶠ)
             begin abstract {
               intro z', induction z' with a', exact ap up (right_inv f a')
             } end
             begin abstract {
               intro z, induction z with a, exact ap up (left_inv f a)
             } end

  @[hott] def ulift_equiv_ulift_of_is_equiv [Hf : is_equiv f] : ulift A ≃ ulift A' :=
  equiv.mk _ (is_equiv_ulift_functor f)

  @[hott] def ulift_equiv_ulift (f : A ≃ A') : ulift A ≃ ulift A' :=
  equiv.mk _ (is_equiv_ulift_functor f)

  @[hott] def ulift_equiv_ulift_refl (A : Type _) : ulift_equiv_ulift (erfl : A ≃ A) = erfl :=
  by apply equiv_eq; intro z; induction z with a; reflexivity

  @[hott] def ulift_inv_functor (a : A) : A' :=
  down (g (up a))

  @[hott] def is_equiv_ulift_inv_functor [Hf : is_equiv g]
    : is_equiv (ulift_inv_functor g) :=
  adjointify (ulift_inv_functor g)
             (ulift_inv_functor g⁻¹ᶠ)
             begin abstract {
               intro z', dsimp [ulift_inv_functor], rwr [ulift.eta, right_inv g],
             } end
             begin abstract {
               intro z', dsimp [ulift_inv_functor], rwr [ulift.eta, left_inv g],
             } end

  @[hott] def equiv_of_ulift_equiv_ulift (g : ulift A ≃ ulift A') : A ≃ A' :=
  equiv.mk _ (is_equiv_ulift_inv_functor g)

  @[hott] def ulift_functor_left_inv  : ulift_inv_functor (ulift_functor f) = f :=
  eq_of_homotopy (λa, idp)

  @[hott] def ulift_functor_right_inv : ulift_functor (ulift_inv_functor g) = g :=
  begin
    apply eq_of_homotopy, intro z, induction z with a, apply ulift.eta
  end

  variables (A A')
  @[hott] def is_equiv_ulift_functor_fn
    : is_equiv (ulift_functor : (A → A') → (ulift A → ulift A')) :=
  adjointify ulift_functor
             ulift_inv_functor
             ulift_functor_right_inv
             ulift_functor_left_inv

  @[hott] def ulift_imp_ulift_equiv : (ulift A → ulift A') ≃ (A → A') :=
  (equiv.mk _ (is_equiv_ulift_functor_fn A A'))⁻¹ᵉ

  -- can we deduce this from ulift_imp_ulift_equiv?
  @[hott] def ulift_equiv_ulift_equiv : (ulift A ≃ ulift A') ≃ (A ≃ A') :=
  equiv.MK equiv_of_ulift_equiv_ulift
           ulift_equiv_ulift
           begin abstract {
             intro f, apply equiv_eq, reflexivity
           } end
           begin abstract {
             intro g, apply equiv_eq', apply eq_of_homotopy, intro z,
             induction z with a, apply ulift.eta
           } end

  @[hott] def {u1 u2} ulift_eq_ulift_equiv (A A' : Type u1)
    : (ulift.{u2 u1} A = ulift.{u2 u1} A') ≃ (A = A') :=
  eq_equiv_equiv _ _ ⬝e ulift_equiv_ulift_equiv _ _ ⬝e (eq_equiv_equiv _ _)⁻¹ᵉ

  @[hott, instance] def is_embedding_ulift : is_embedding ulift :=
  begin
    intros A A', nfapply is_equiv.homotopy_closed,
      exact to_inv (ulift_eq_ulift_equiv _ _), 
      apply_instance,
    { intro p, induction p,
      dsimp [ulift_eq_ulift_equiv,equiv.trans,equiv.symm,eq_equiv_equiv],
      rwr [ulift_equiv_ulift_refl], apply ua_refl }
  end

  @[hott] def pulift (A : pType.{u}) : pType.{max u v} :=
  pointed.MK (ulift A) (up pt)

  @[hott] def pulift_functor {A B : Type*} (f : A →* B) : pulift A →* pulift B :=
  pmap.mk (ulift_functor f) (ap up (respect_pt f))

  -- is_trunc_ulift is defined in init.trunc

  @[hott] def pup {A : Type*} : A →* pulift A :=
  pmap.mk up idp

  @[hott] def pdown {A : Type*} : pulift A →* A :=
  pmap.mk down idp

  @[hott] def pulift_functor_phomotopy {A B : Type*} (f : A →* B)
    : pdown ∘* pulift_functor f ∘* pup ~* f :=
  begin
    fapply phomotopy.mk,
    { reflexivity},
    { refine idp_con _ ⬝ _, symmetry,
      refine ap02 down (idp_con _) ⬝ _,
      refine ap_compose' _ _ _ ⬝ _, exact ap_id _ }
  end

  @[hott] def pequiv_pulift (A : Type*) : A ≃* pulift A :=
  pequiv_of_equiv (equiv_ulift A) idp

  @[hott] def fiber_ulift_functor {A B : Type _} (f : A → B) (b : B) :
    fiber (ulift_functor f) (up b) ≃ fiber f b :=
  begin
    fapply equiv.MK; intro v; cases v with a p,
    { cases a with a, exact fiber.mk a (eq_of_fn_eq_fn' up p) },
    { exact fiber.mk (up a) (ap up p) },
    { dsimp, apply ap (fiber.mk a), apply eq_of_fn_eq_fn'_ap },
    { cases a with a, apply ap (fiber.mk (up a)), apply ap_eq_of_fn_eq_fn' }
  end

end ulift
end hott