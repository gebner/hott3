/-
Copyright (c) 2017 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Ulrik Buchholtz

Quotients. This is a quotient without truncation for an arbitrary type-valued binary relation
(graph).
See also .set_quotient
-/

/-
  The hit quotient is primitive, declared in init.hit.
  The constructors are, given {A : Type _} (R : A → A → Type _),
  * class_of : A → quotient R (A implicit, R explicit)
  * eq_of_rel : Π{a a' : A}, R a a' → class_of a = class_of a' (R explicit)
-/

import hott.arity hott.cubical.squareover hott.types.arrow hott.cubical.pathover2 hott.types.pointed
universes u v w
hott_theory

namespace hott
open hott.eq hott.equiv hott.pi is_trunc pointed hott.sigma

namespace quotient
section
variables {A : Type _} {R : A → A → Type _}

@[hott, induction, priority 1500] protected def elim {P : Type _} (Pc : A → P) (Pp : Π⦃a a' : A⦄
  (H : R a a'), Pc a = Pc a') (x : quotient R) : P :=
begin hinduction x, exact Pc a, exact pathover_of_eq _ (Pp H) end

@[hott, reducible] protected def elim_on {P : Type _} (x : quotient R)
  (Pc : A → P) (Pp : Π⦃a a' : A⦄ (H : R a a'), Pc a = Pc a') : P :=
quotient.elim Pc Pp x

@[hott] theorem elim_eq_of_rel {P : Type _} (Pc : A → P)
  (Pp : Π⦃a a' : A⦄ (H : R a a'), Pc a = Pc a') {a a' : A} (H : R a a')
  : ap (quotient.elim Pc Pp) (eq_of_rel R H) = Pp H :=
begin
  apply eq_of_fn_eq_fn_inv ((pathover_constant (eq_of_rel R H)) _ _),
  refine (apd_eq_pathover_of_eq_ap _ _)⁻¹ ⬝ rec_eq_of_rel _ _ _
end

@[hott] protected def rec_prop {A : Type _} {R : A → A → Type _} {P : quotient R → Type _}
  [H : Πx, is_prop (P x)] (Pc : Π(a : A), P (class_of R a)) (x : quotient R) : P x :=
quotient.rec Pc (λa a' H, is_prop.elimo _ _ _) x

@[hott] protected def elim_prop {P : Type _} [H : is_prop P] (Pc : A → P) (x : quotient R) : P :=
quotient.elim Pc (λa a' H, is_prop.elim _ _) x

@[hott] protected def elim_type (Pc : A → Type _)
  (Pp : Π⦃a a' : A⦄ (H : R a a'), Pc a ≃ Pc a') : quotient R → Type _ :=
quotient.elim Pc (λa a' H, ua (Pp H))

@[hott, reducible] protected def elim_type_on (x : quotient R) (Pc : A → Type _)
  (Pp : Π⦃a a' : A⦄ (H : R a a'), Pc a ≃ Pc a') : Type _ :=
quotient.elim_type Pc Pp x

@[hott] theorem elim_type_eq_of_rel_fn (Pc : A → Type _)
  (Pp : Π⦃a a' : A⦄ (H : R a a'), Pc a ≃ Pc a') {a a' : A} (H : R a a')
  : transport (quotient.elim_type Pc Pp) (eq_of_rel R H) = to_fun (Pp H) :=
begin
  refine tr_eq_cast_ap_fn _ ⬝ ap cast _ ⬝ cast_ua_fn _,
  apply elim_eq_of_rel
end

-- rename to elim_type_eq_of_rel_fn_inv
@[hott] theorem elim_type_eq_of_rel_inv (Pc : A → Type _)
  (Pp : Π⦃a a' : A⦄ (H : R a a'), Pc a ≃ Pc a') {a a' : A} (H : R a a')
  : transport (quotient.elim_type Pc Pp) (eq_of_rel R H)⁻¹ = to_inv (Pp H) :=
begin
  hsimp [tr_eq_cast_ap_fn, quotient.elim_type, ap_inv, elim_eq_of_rel, cast_ua_inv_fn]
end

-- remove '
@[hott] theorem elim_type_eq_of_rel_inv' (Pc : A → Type _)
  (Pp : Π⦃a a' : A⦄ (H : R a a'), Pc a ≃ Pc a') {a a' : A} (H : R a a') (x : Pc a')
  : transport (quotient.elim_type Pc Pp) (eq_of_rel R H)⁻¹ x = to_inv (Pp H) x :=
ap10 (elim_type_eq_of_rel_inv Pc Pp H) x

@[hott] theorem elim_type_eq_of_rel (Pc : A → Type u)
  (Pp : Π⦃a a' : A⦄ (H : R a a'), Pc a ≃ Pc a') {a a' : A} (H : R a a') (p : Pc a)
  : transport (quotient.elim_type Pc Pp) (eq_of_rel R H) p = to_fun (Pp H) p :=
ap10 (elim_type_eq_of_rel_fn Pc Pp H) p

@[hott] def elim_type_eq_of_rel' (Pc : A → Type _)
  (Pp : Π⦃a a' : A⦄ (H : R a a'), Pc a ≃ Pc a') {a a' : A} (H : R a a') (p : Pc a)
  : @pathover _ (class_of _ a) (quotient.elim_type Pc Pp) p _ (eq_of_rel R H) (to_fun (Pp H) p) :=
pathover_of_tr_eq (elim_type_eq_of_rel Pc Pp H p)

@[hott] def elim_type_uncurried (H : Σ(Pc : A → Type _),  Π⦃a a' : A⦄ (H : R a a'), Pc a ≃ Pc a')
  : quotient R → Type _ :=
quotient.elim_type H.1 H.2

/- The dependent universal property -/
@[hott] def quotient_pi_equiv (C : quotient R → Type _) : (Πx, C x) ≃
  (Σ(f : Π(a : A), C (class_of R a)),  Π⦃a a' : A⦄ (H : R a a'), f a =[eq_of_rel R H] f a') :=
begin
  fapply equiv.MK,
  { intro f, exact ⟨λa, f (class_of R a), λa a' H, apd f (eq_of_rel R H)⟩},
  { intros v x, induction v with i p, hinduction x,
      exact (i a),
      exact (p H)},
  { intro v, induction v with i p,
    apply ap (sigma.mk i), apply eq_of_homotopy3, intros a a' H, apply rec_eq_of_rel},
  { intro f, apply eq_of_homotopy, intro x, hinduction x, reflexivity,
    apply eq_pathover_dep, rwr rec_eq_of_rel, exact hrflo},
end

@[hott] def pquotient {A : Type*} (R : A → A → Type _) : Type* :=
pType.mk (quotient R) (class_of R pt)
end

/- the flattening lemma -/

namespace flattening
section

parameters {A : Type u} (R : A → A → Type v) (C : A → Type w) (f : Π⦃a a'⦄, R a a' → C a ≃ C a')
include f
variables {a a' : A} {r : R a a'}

private def P : quotient R → Type w := quotient.elim_type C f

@[hott] def flattening_type : Type (max u w) := Σa, C a
private def X := flattening_type
inductive flattening_rel : X → X → Type (max u v w)
| mk : Π⦃a a' : A⦄ (r : R a a') (c : C a), flattening_rel ⟨a, c⟩ ⟨a', f r c⟩

@[hott] def Ppt (c : C a) : sigma P :=
⟨class_of R a, c⟩

@[hott] def Peq (r : R a a') (c : C a) : Ppt c = Ppt (f r c) :=
begin
  fapply sigma_eq,
  { apply eq_of_rel R r},
  { refine elim_type_eq_of_rel' C f r c}
end

@[hott] def rec {Q : sigma P → Type _} (Qpt : Π{a : A} (x : C a), Q (Ppt x))
  (Qeq : Π⦃a a' : A⦄ (r : R a a') (c : C a), Qpt c =[Peq r c] Qpt (f r c))
  (v : sigma P) : Q v :=
begin
  induction v with q p,
  hinduction q,
  { exact Qpt p},
  { apply pi_pathover_left, intro c,
    refine _ ⬝op apdt Qpt (elim_type_eq_of_rel C f H c)⁻¹ᵖ,
    refine _ ⬝op (tr_compose Q (Ppt R C f) _ _)⁻¹,
    rwr ap_inv,
    refine pathover_cancel_right _ (tr_pathover _ _)⁻¹ᵒ,
    refine change_path _ (Qeq H c),
    symmetry, dsimp [Ppt, Peq],
    refine whisker_left _ (ap_dpair _) ⬝ _,
    refine (dpair_eq_dpair_con _ _ _ _)⁻¹ ⬝ _,
    apply ap (dpair_eq_dpair _), symmetry,
    exact pathover_of_tr_eq_eq_concato _ },
end

@[hott] def elim' {Q : Type _} (Qpt : Π{a : A}, C a → Q)
  (Qeq : Π⦃a a' : A⦄ (r : R a a') (c : C a), Qpt c = Qpt (f r c))
  (q : quotient R) (p : P q) : Q :=
begin
  hinduction q,
  { exact Qpt p},
  { apply arrow_pathover_constant_right,
    intro c, exact Qeq H c ⬝ ap Qpt (elim_type_eq_of_rel C f H c)⁻¹},
end

@[hott] def elim {Q : Type _} (Qpt : Π{a : A}, C a → Q)
  (Qeq : Π⦃a a' : A⦄ (r : R a a') (c : C a), Qpt c = Qpt (f r c))
  (v : sigma P) : Q :=
begin
  induction v with q p, exact elim' R C f @Qpt Qeq q p,
end

@[hott] theorem elim_Peq {Q : Type _} (Qpt : Π{a : A}, C a → Q)
  (Qeq : Π⦃a a' : A⦄ (r : R a a') (c : C a), Qpt c = Qpt (f r c)) {a a' : A} (r : R a a')
  (c : C a) : ap (elim @Qpt Qeq) (Peq r c) = Qeq r c :=
begin
  refine ap_dpair_eq_dpair _ _ _ ⬝ _,
  refine apd011_eq_apo11_apd (elim' R C f @Qpt Qeq) _ _ ⬝ _,
  delta elim', dsimp, rwr [rec_eq_of_rel], dsimp,
  refine @apo11_arrow_pathover_constant_right _ _ _ _ _ _ _ _ _ _ _
    (λc : P R C f (class_of R a), Qeq r c ⬝ ap Qpt (elim_type_eq_of_rel C f r c)⁻¹) ⬝ _,
    -- we need the @ because otherwise the elaborator unfolds too much
  dsimp [elim_type_eq_of_rel'],
  refine idp ◾ idp ◾ ap02 _ begin exact to_right_inv (pathover_equiv_tr_eq _ _ _) _ end ⬝ _,
  rwr [ap_inv], apply inv_con_cancel_right
end

open flattening_rel
@[hott] def flattening_lemma : sigma P ≃ quotient flattening_rel :=
begin
  fapply equiv.MK,
  { refine elim R C f _ _,
    { intros a c, exact class_of _ ⟨a, c⟩},
    { intros a a' r c, apply eq_of_rel, constructor}},
  { intro q, hinduction q with x x x' H,
    { exact Ppt R C f x.2},
    { induction H, apply Peq}},
  { intro q, hinduction q with x x x' H,
    { induction x with a c, reflexivity},
    { induction H, apply eq_pathover, apply hdeg_square,
      refine ap_compose (elim R C f _ _) (quotient.elim _ _) _ ⬝ _,
      rwr [elim_eq_of_rel, ap_id],
      apply elim_Peq }},
  { refine rec R C f (λa x, idp) _, intros,
    apply eq_pathover, apply hdeg_square,
      refine ap_compose (quotient.elim _ _) (elim R C f _ _) _ ⬝ _,
      rwr [elim_Peq, ap_id],
      apply elim_eq_of_rel }
end

end
end flattening

section
open hott.is_equiv hott.equiv prod
variables {A : Type _} {R : A → A → Type _}
          {B : Type _} {Q : B → B → Type _}
          {C : Type _} {S : C → C → Type _}
          (f : A → B) (k : Πa a' : A, R a a' → Q (f a) (f a'))
          (g : B → C) (l : Πb b' : B, Q b b' → S (g b) (g b'))

@[hott] protected def functor : quotient R → quotient Q :=
quotient.elim (λa, class_of Q (f a)) (λa a' r, eq_of_rel Q (k a a' r))

@[hott, hsimp] def functor_class_of (a : A) :
  quotient.functor f k (class_of R a) = class_of Q (f a) :=
by refl

@[hott, hsimp] def functor_eq_of_rel {a a' : A} (r : R a a') :
  ap (quotient.functor f k) (eq_of_rel R r) = eq_of_rel Q (k a a' r) :=
elim_eq_of_rel _ _ r

@[hott] protected def functor_compose :
  quotient.functor (g ∘ f) (λa a' r, l (f a) (f a') (k a a' r)) ~
  quotient.functor g l ∘ quotient.functor f k :=
begin
  intro x, hinduction x,
  { refl },
  { dsimp, apply eq_pathover_compose_right, apply hdeg_square, hsimp }
end

@[hott] protected def functor_homotopy {f f' : A → B} {k : Πa a' : A, R a a' → Q (f a) (f a')}
  {k' : Πa a' : A, R a a' → Q (f' a) (f' a')} (h : f ~ f')
  (h2 : Π(a a' : A) (r : R a a'), transport11 Q (h a) (h a') (k a a' r) = k' a a' r) :
  quotient.functor f k ~ quotient.functor f' k' :=
begin
  intro x, hinduction x with a a a' r,
  { exact ap (class_of Q) (h a) },
  { dsimp, apply eq_pathover, hsimp, apply transpose, apply natural_square2, apply h2 }
end

@[hott] protected def functor_id (x : quotient R) :
  quotient.functor id (λa a' r, r) x = x :=
begin
  hinduction x,
  { refl },
  { apply eq_pathover_id_right, apply hdeg_square, hsimp }
end

variables [F : is_equiv f] [K : Πa a', is_equiv (k a a')]
include F K

@[hott] instance is_equiv : is_equiv (quotient.functor f k) :=
begin
  apply adjointify _ (quotient.functor f⁻¹ᶠ
    (λb b' q, (k (f⁻¹ᶠ b) (f⁻¹ᶠ b'))⁻¹ᶠ (transport11 Q (right_inv f b)⁻¹ (right_inv f b')⁻¹ q))),
  abstract { intro x, refine (quotient.functor_compose _ _ _ _ x)⁻¹ ⬝ _ ⬝ quotient.functor_id x,
    apply quotient.functor_homotopy (right_inv f), intros a a' r,
    rwr [right_inv (k _ _), ←transport11_con, con.left_inv, con.left_inv] },
  abstract { intro x, refine (quotient.functor_compose _ _ _ _ x)⁻¹ ⬝ _ ⬝ quotient.functor_id x,
    apply quotient.functor_homotopy (left_inv f), intros a a' r,
    rwr [adj f, adj f, ←ap_inv, ←ap_inv, transport11_ap,
         ←fn_transport11_eq_transport11_fn _ _ _ _ k, left_inv (k _ _), ←transport11_con,
         con.left_inv, con.left_inv] }
end
end

section
variables {A : Type _} (R : A → A → Type _)
           {B : Type _} (Q : B → B → Type _)
           (f : A ≃ B) (k : Πa a' : A, R a a' ≃ Q (f a) (f a'))
include f k

@[hott] protected def equiv : quotient R ≃ quotient Q :=
equiv.mk (quotient.functor f (λa a', k a a')) (quotient.is_equiv _ _)
end


end quotient
end hott
