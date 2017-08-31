/-
Copyright (c) 2014 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob von Raumer, Floris van Doorn

Ported from Coq HoTT
-/
import hott.init.equiv

universes u v w l
hott_theory

namespace hott
open eq equiv is_equiv

axiom univalence (A B : Type u) : is_equiv (@equiv_of_eq A B)

attribute [instance] univalence

-- This is the version of univalence axiom we will probably use most often
@[hott] def ua {A B : Type u} : A ≃ B → A = B :=
equiv_of_eq⁻¹

@[hott] def eq_equiv_equiv (A B : Type u) : (A = B) ≃ (A ≃ B) :=
equiv.mk equiv_of_eq (by apply_instance)

@[hott, elab_simple] def equiv_of_eq_ua {A B : Type u} (f : A ≃ B) : equiv_of_eq (ua f) = f :=
right_inv equiv_of_eq f

@[hott] def cast_ua_fn {A B : Type u} (f : A ≃ B) : cast (ua f) = f.to_fun :=
ap to_fun (equiv_of_eq_ua f)

@[hott] def cast_ua {A B : Type u} (f : A ≃ B) (a : A) : cast (ua f) a = f a :=
ap10 (cast_ua_fn f) a

@[hott] def cast_ua_inv_fn {A B : Type u} (f : A ≃ B) : cast (ua f)⁻¹ = to_inv f :=
ap to_inv (equiv_of_eq_ua f)

@[hott] def cast_ua_inv {A B : Type u} (f : A ≃ B) (b : B) : cast (ua f)⁻¹ b = to_inv f b :=
ap10 (cast_ua_inv_fn f) b

@[hott] def ua_equiv_of_eq {A B : Type u} (p : A = B) : ua (equiv_of_eq p) = p :=
left_inv equiv_of_eq p

@[hott] def eq_of_equiv_lift {A : Type (max v u)} {B : Type v} (f : A ≃ B) : A = ulift B :=
ua (f ⬝e equiv_lift _)

namespace equiv

  -- One consequence of UA is that we can transport along equivalencies of types
  -- We can use this for calculation evironments
  @[subst, hott]
  protected def transport_of_equiv (P : Type _ → Type _) {A B : Type _} (H : A ≃ B)
    : P A → P B :=
  eq.transport P (ua H)

  -- we can "recurse" on equivalences, by replacing them by (equiv_of_eq _)
  @[hott] def rec_on_ua {A B : Type _} {P : A ≃ B → Type _}
    (f : A ≃ B) (H : Π(q : A = B), P (equiv_of_eq q)) : P f :=
  right_inv equiv_of_eq f ▸ H (ua f)

  -- a variant where we immediately recurse on the equality in the new goal
  @[hott] def rec_on_ua_idp {A : Type _} {P : Π{B}, A ≃ B → Type _} {B : Type _}
    (f : A ≃ B) (H : P equiv.rfl) : P f :=
  rec_on_ua f (λq, by induction q; apply H)

  -- a variant where (equiv_of_eq (ua f)) will be replaced by f in the new goal
  @[hott] def rec_on_ua' {A B : Type _} {P : A ≃ B → A = B → Type _}
    (f : A ≃ B) (H : Π(q : A = B), P (equiv_of_eq q) q) : P f (ua f) :=
  transport (λ x, P x (ua f)) (right_inv equiv_of_eq f) (H (ua f))

  -- a variant where we do both
  @[hott] def rec_on_ua_idp' {A : Type _} {P : Π{B}, A ≃ B → A = B → Type _} {B : Type _}
    (f : A ≃ B) (H : P equiv.rfl idp) : P f (ua f) :=
  rec_on_ua' f (λq, by induction q; exact H)

  @[hott] def ua_refl (A : Type _) : ua equiv.rfl = idpath A :=
  eq_of_fn_eq_fn (eq_equiv_equiv _ _) (right_inv (eq_equiv_equiv _  _).to_fun equiv.rfl)

  @[hott] def ua_symm {A B : Type _} (f : A ≃ B) : ua f⁻¹ᵉ = (ua f)⁻¹ :=
  begin
    apply rec_on_ua_idp f,
    transitivity, tactic.swap,
    {apply inverse2, symmetry, apply ua_refl},
    {apply ua_refl},
  end

  @[hott] def ua_trans {A B C : Type _} (f : A ≃ B) (g : B ≃ C) : ua (f ⬝e g) = ua f ⬝ ua g :=
  begin
    apply rec_on_ua_idp g, apply rec_on_ua_idp f,
    transitivity, tactic.swap,
    {apply concat2; {symmetry, apply ua_refl}},
    {apply ua_refl},
  end


end equiv

end hott
