/-
Copyright (c) 2015-16 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Ulrik Buchholtz, Jakob von Raumer

Declaration and properties of the pushout
-/

import .quotient ..types.arrow_2
universes u v w
hott_theory
namespace hott

open hott.quotient hott.sum sum hott.equiv is_trunc pointed hott.sigma

namespace pushout
section

parameters {TL : Type u} {BL : Type v} {TR : Type w} (f : TL → BL) (g : TL → TR)

private abbreviation A := BL ⊎ TR
inductive pushout_rel : A → A → Type (max u v w)
| Rmk : Π(x : TL), pushout_rel (inl (f x)) (inr (g x))
open pushout_rel
private abbreviation R := pushout_rel

@[hott] def pushout : Type _ := quotient R

parameters {f g}
@[hott] def inl (x : BL) : pushout :=
class_of R (inl x)

@[hott] def inr (x : TR) : pushout :=
class_of R (inr x)

@[hott] def glue (x : TL) : inl (f x) = inr (g x) :=
eq_of_rel pushout_rel (Rmk x)

@[hott, elab_as_eliminator, induction] protected def rec {P : pushout → Type _} (Pinl : Π(x : BL), P (inl x))
  (Pinr : Π(x : TR), P (inr x)) (Pglue : Π(x : TL), Pinl (f x) =[glue x] Pinr (g x))
    (y : pushout) : P y :=
begin
  hinduction y,
  { cases a,
      apply Pinl,
      apply Pinr},
  { cases H, apply Pglue}
end

@[hott, reducible] protected def rec_on {P : pushout → Type _} (y : pushout)
  (Pinl : Π(x : BL), P (inl x)) (Pinr : Π(x : TR), P (inr x))
  (Pglue : Π(x : TL), Pinl (f x) =[glue x] Pinr (g x)) : P y :=
rec Pinl Pinr Pglue y

@[hott] theorem rec_glue {P : pushout → Type _} (Pinl : Π(x : BL), P (inl x))
  (Pinr : Π(x : TR), P (inr x)) (Pglue : Π(x : TL), Pinl (f x) =[glue x] Pinr (g x))
    (x : TL) : apd (rec Pinl Pinr Pglue) (glue x) = Pglue x :=
rec_eq_of_rel _ _ _

@[hott, induction, priority 1100] protected def elim {P : Type _} (Pinl : BL → P) 
  (Pinr : TR → P) (Pglue : Π(x : TL), Pinl (f x) = Pinr (g x)) (y : pushout) : P :=
begin hinduction y, exact Pinl x, exact Pinr x, exact pathover_of_eq _ (Pglue x) end

@[hott] theorem elim_glue {P : Type _} (Pinl : BL → P) (Pinr : TR → P)
  (Pglue : Π(x : TL), Pinl (f x) = Pinr (g x)) (x : TL)
  : ap (elim Pinl Pinr Pglue) (glue x) = Pglue x :=
begin
  apply eq_of_fn_eq_fn_inv ((pathover_constant (glue x)) _ _),
  refine (apd_eq_pathover_of_eq_ap _ _)⁻¹ ⬝ rec_eq_of_rel _ _ _
end

@[hott] protected def elim_type (Pinl : BL → Type _) (Pinr : TR → Type _)
  (Pglue : Π(x : TL), Pinl (f x) ≃ Pinr (g x)) : pushout → Type _ :=
quotient.elim_type (λz, sum.rec Pinl Pinr z)
  begin intros v v' r, induction r, apply Pglue end

@[hott] theorem elim_type_glue (Pinl : BL → Type _) (Pinr : TR → Type _)
  (Pglue : Π(x : TL), Pinl (f x) ≃ Pinr (g x)) (x : TL)
  : transport (elim_type Pinl Pinr Pglue) (glue x) = Pglue x :=
elim_type_eq_of_rel_fn _ _ _

@[hott] theorem elim_type_glue_inv (Pinl : BL → Type _) (Pinr : TR → Type _)
  (Pglue : Π(x : TL), Pinl (f x) ≃ Pinr (g x)) (x : TL)
  : transport (elim_type Pinl Pinr Pglue) (glue x)⁻¹ = to_inv (Pglue x) :=
elim_type_eq_of_rel_inv _ _ _

@[hott] protected def rec_prop {P : pushout → Type _} [H : Πx, is_prop (P x)]
  (Pinl : Π(x : BL), P (inl x)) (Pinr : Π(x : TR), P (inr x)) (y : pushout) :=
rec Pinl Pinr (λx, is_prop.elimo _ _ _) y

@[hott] protected def elim_prop {P : Type _} [H : is_prop P] (Pinl : BL → P) (Pinr : TR → P)
  (y : pushout) : P :=
elim Pinl Pinr (λa, is_prop.elim _ _) y

end

variables {TL : Type u} {BL : Type v} {TR : Type w} (f : TL → BL) (g : TL → TR)

@[hott] protected theorem elim_inl {P : Type _} (Pinl : BL → P) (Pinr : TR → P)
  (Pglue : Π(x : TL), Pinl (f x) = Pinr (g x)) {b b' : BL} (p : b = b')
  : ap (pushout.elim Pinl Pinr Pglue) (ap inl p) = ap Pinl p :=
(ap_compose _ _ _)⁻¹

@[hott] protected theorem elim_inr {P : Type _} (Pinl : BL → P) (Pinr : TR → P)
  (Pglue : Π(x : TL), Pinl (f x) = Pinr (g x)) {b b' : TR} (p : b = b')
  : ap (pushout.elim Pinl Pinr Pglue) (ap inr p) = ap Pinr p :=
(ap_compose _ _ _)⁻¹

/- The non-dependent universal property -/
@[hott] def pushout_arrow_equiv (C : Type _)
  : (pushout f g → C) ≃ (Σ(i : BL → C) (j : TR → C), Πc, i (f c) = j (g c)) :=
begin
  fapply equiv.MK,
  { intro f, exact ⟨λx, f (inl x), λx, f (inr x), λx, ap f (glue x)⟩},
  { intros v x, induction v with i w, induction w with j p, hinduction x,
      exact (i a), exact (j a), exact (p x)},
  { intro v, induction v with i w, induction w with j p, dsimp,
    apply ap, apply ap, apply eq_of_homotopy, intro x, apply elim_glue},
  { intro f, apply eq_of_homotopy, intro x, hinduction x, refl, refl, dsimp,
    apply eq_pathover, apply hdeg_square, apply elim_glue},
end

/- glue squares -/
@[hott] protected def glue_square {x x' : TL} (p : x = x')
  : square (glue x) (glue x') (ap inl (ap f p)) (ap inr (ap g p)) :=
by cases p; apply vrefl

end pushout

--open function --

namespace pushout

/- The flattening lemma -/
section

parameters {TL : Type _} {BL : Type _} {TR : Type _} (f : TL → BL) (g : TL → TR)
            (Pinl : BL → Type u) (Pinr : TR → Type u)
            (Pglue : Π(x : TL), Pinl (f x) ≃ Pinr (g x))
include Pglue

private abbreviation A := BL ⊎ TR
private abbreviation R : A → A → Type _ := pushout_rel f g
private abbreviation P := pushout.elim_type Pinl Pinr Pglue

private abbreviation F : sigma (Pinl ∘ f) → sigma Pinl :=
λz, ⟨ f z.1 , z.2 ⟩

private abbreviation G : sigma (Pinl ∘ f) → sigma Pinr :=
λz, ⟨ g z.1 , Pglue z.1 z.2 ⟩

@[hott] protected def flattening : sigma P ≃ pushout F G :=
begin
  refine quotient.flattening.flattening_lemma _ _ _ ⬝e _,
  fapply equiv.MK,
  { intro q, hinduction q with z z z' fr,
    { induction z with a p, induction a with x x,
      { exact inl ⟨x, p⟩ },
      { exact inr ⟨x, p⟩ } },
    { induction fr with a a' r p, induction r with x,
      exact glue (⟨x, p⟩ : sigma _) } },
  { intro q, hinduction q with xp xp xp,
    { exact class_of _ ⟨sum.inl xp.1, xp.2⟩ },
    { exact class_of _ ⟨sum.inr xp.1, xp.2⟩ },
    { apply eq_of_rel, dsimp,
      exact flattening.flattening_rel.mk _ (pushout_rel.Rmk _ _ _) _ } },
  { intro q, hinduction q with xp xp xp; induction xp with x p,
    { apply ap inl, reflexivity },
    { apply ap inr, reflexivity },
    { apply eq_pathover, dsimp,
      rwr [ap_id, ←ap_compose' (quotient.elim _ _)],
      rwr elim_glue, rwr elim_eq_of_rel, dsimp, apply hrefl } },
  { intro q, hinduction q with z z z' fr,
    { induction z with a p, induction a with x x,
      { reflexivity },
      { reflexivity } },
    { induction fr with a a' r p, induction r with x,
      apply eq_pathover,
      rwr [ap_id, ←ap_compose' (pushout.elim _ _ _)],
      rwr elim_eq_of_rel, rwr elim_glue, apply hrefl } }
end
end

-- Commutativity of pushouts
section
variables {TL : Type u} {BL : Type v} {TR : Type w} (f : TL → BL) (g : TL → TR)

@[hott] protected def transpose : pushout f g → pushout g f :=
begin
  intro x, hinduction x, apply inr a, apply inl a, exact (glue _)⁻¹
end

--TODO prove without krwr?
@[hott] protected def transpose_involutive (x : pushout f g) :
  pushout.transpose g f (pushout.transpose f g x) = x :=
begin
    hinduction x, apply idp, apply idp,
    apply eq_pathover, refine _ ⬝hp (ap_id _)⁻¹ᵖ,
    refine ap_compose (pushout.transpose _ _) _ _ ⬝ph _, 
    apply hdeg_square,
    dsimp [pushout.transpose],
    rwr [elim_glue, ap_inv, elim_glue, hott.eq.inv_inv],
end

@[hott] protected def symm : pushout f g ≃ pushout g f :=
begin
  fapply equiv.MK, apply pushout.transpose, apply pushout.transpose,
    intro x; apply pushout.transpose_involutive,
    intro x; apply pushout.transpose_involutive
end

end

-- Functoriality of pushouts
section
  section lemmas
    variables {X : Type _} {x₀ x₁ x₂ x₃ : X}
              (p : x₀ = x₁) (q : x₁ = x₂) (r : x₂ = x₃)
    @[hott] private def is_equiv_functor_lemma₁
      : (r ⬝ ((p ⬝ q ⬝ r)⁻¹ ⬝ p)) = q⁻¹ :=
    by cases p; cases r; cases q; reflexivity

    @[hott] private def is_equiv_functor_lemma₂
      : (p ⬝ q ⬝ r)⁻¹ ⬝ (p ⬝ q) = r⁻¹ :=
    by cases p; cases r; cases q; reflexivity
  end lemmas

  variables {TL : Type _} {BL : Type _} {TR : Type _} {f : TL → BL} {g : TL → TR}
            {TL' : Type _} {BL' : Type _} {TR' : Type _} {f' : TL' → BL'} {g' : TL' → TR'}
            (tl : TL → TL') (bl : BL → BL') (tr : TR → TR')
            (fh : bl ∘ f ~ f' ∘ tl) (gh : tr ∘ g ~ g' ∘ tl)
  include fh gh

  def pushout_rel_functor {{x x' : BL ⊎ TR}}
    (r : pushout_rel f g x x') : pushout_rel f' g' (x.functor bl tr) (x'.functor bl tr) :=
  begin
    induction r,
    apply transport11 (pushout_rel f' g') (ap sum.inl (fh r)⁻¹ᵖ) (ap sum.inr (gh r)⁻¹ᵖ),
    constructor
  end 

  @[hott] protected def functor : pushout f g → pushout f' g' :=
  begin
    intro x, hinduction x with a b z,
    { exact inl (bl a) },
    { exact inr (tr b) },
    { exact (ap inl (fh z)) ⬝ glue (tl z) ⬝ (ap inr (gh z)⁻¹) }
  end

  @[hott] protected def pushout_functor_homotopy_quotient_functor : 
    pushout.functor tl bl tr fh gh ~ 
    quotient.functor (sum.functor bl tr) (pushout_rel_functor tl bl tr fh gh) :=
  begin
    intro x, hinduction x with a b z,
    { refl },
    { refl },
    { dsimp, apply eq_pathover, apply hdeg_square, 
      refine elim_glue _ _ _ _ ⬝ _ ⬝ (functor_eq_of_rel _ _ _)⁻¹ᵖ,
      dsimp [glue, pushout_rel_functor], rwr [ap_inv],
      symmetry, apply eq_top_of_square,
      refine ap_compose (class_of _) _ _ ⬝ph _ ⬝hp (ap_compose (class_of _) _ _)⁻¹ᵖ,
      apply natural_square2,
      rwr [←transport11_con, ap_inv, con.left_inv, ap_inv, con.left_inv] }
  end

  @[hott] protected def ap_functor_inl {x x' : BL} (p : x = x')
    : ap (pushout.functor tl bl tr fh gh) (ap inl p) = ap inl (ap bl p) :=
  by cases p; reflexivity

  @[hott] protected def ap_functor_inr {x x' : TR} (p : x = x')
    : ap (pushout.functor tl bl tr fh gh) (ap inr p) = ap inr (ap tr p) :=
  by cases p; reflexivity

  variables [ietl : is_equiv tl] [iebl : is_equiv bl] [ietr : is_equiv tr]
  include ietl iebl ietr

  open equiv is_equiv arrow
  @[hott, instance] protected def is_equiv_functor
    : is_equiv (pushout.functor tl bl tr fh gh) :=
  sorry
end

/- version giving the equivalence -/
section

  variables {TL : Type _} {BL : Type _} {TR : Type _} {f : TL → BL} {g : TL → TR}
            {TL' : Type _} {BL' : Type _} {TR' : Type _} {f' : TL' → BL'} {g' : TL' → TR'}
            (tl : TL ≃ TL') (bl : BL ≃ BL') (tr : TR ≃ TR')
            (fh : bl ∘ f ~ f' ∘ tl) (gh : tr ∘ g ~ g' ∘ tl)
  include fh gh

  @[hott] protected def equiv : pushout f g ≃ pushout f' g' :=
  equiv.mk (pushout.functor tl bl tr fh gh) (by apply_instance)
end

@[hott, instance] def pointed_pushout {TL BL TR : Type _} [HTL : pointed TL]
  [HBL : pointed BL] [HTR : pointed TR] (f : TL → BL) (g : TL → TR) : pointed (pushout f g) :=
pointed.mk (inl (point _))
end pushout open pushout

@[hott] def ppushout {TL BL TR : Type*} (f : TL →* BL) (g : TL →* TR) : Type* :=
pointed.mk' (pushout f g)

namespace pushout
  section
  parameters {TL : Type*} {BL : Type*} {TR : Type*} (f : TL →* BL) (g : TL →* TR)

  parameters {f g}
  @[hott] def pinl : BL →* ppushout f g :=
  pmap.mk inl idp

  @[hott] def pinr : TR →* ppushout f g :=
  pmap.mk inr ((ap inr (respect_pt g))⁻¹ ⬝ (glue _)⁻¹ ⬝ (ap inl (respect_pt f)))

  @[hott] def pglue (x : TL) : pinl (f x) = pinr (g x) := -- TODO do we need this?
  glue _

  end

  section
  variables {TL : Type*} {BL : Type*} {TR : Type*} (f : TL →* BL) (g : TL →* TR)

  @[hott] protected def psymm : ppushout f g ≃* ppushout g f :=
  begin
    fapply pequiv_of_equiv,
    { apply pushout.symm },
    { exact ap inr (respect_pt f)⁻¹ ⬝ (glue _)⁻¹ ⬝ ap inl (respect_pt g) }
  end

  end
end pushout
end hott