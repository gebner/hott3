/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Floris van Doorn

Theorems about sums/coproducts/disjoint unions
-/

import .pi .equiv hott.cubical.square

open /-hott.lift-/ hott hott.eq hott.is_equiv hott.equiv
  hott.prod /-prod.ops-/ hott.is_trunc hott.sigma hott.bool

hott_theory

namespace sum
  universe variables u v u' v'
  variables {A : Type.{u}} {B : Type.{v}}
    (z z' : A ⊎ B) {P : A → Type.{u'}} {Q : A → Type.{v'}}

  @[hott] protected def eta : @sum.rec A B (λ z, A ⊎ B) inl inr z = z :=
  by hinduction z; reflexivity

  @[hott] protected def code : A ⊎ B → A ⊎ B → Type (max u v) :=
  begin
    intros x y, induction x with a b; induction y with a' b',
    exact ulift.{(max u v) u} (a = a'), exact ulift empty,
    exact ulift empty, exact @ulift.{(max u v) v} (b = b'),
  end
  
  @[hott] protected def decode : Π (z z' : A ⊎ B), sum.code z z' → z = z' :=
  begin
    intros z z', induction z with a b; induction z' with a' b',
    exact λ c, ap inl (ulift.down c),
    exact λ c, empty.elim (ulift.down c),
    exact λ c, empty.elim (ulift.down c),
    exact λ c, ap inr (ulift.down c)
  end

  @[hott] protected def mem_cases : (Σ a, z = inl a) ⊎ (Σ b, z = inr b) :=
  begin
    induction z with a b,
    exact inl ⟨a, idp⟩, exact inr ⟨b, idp⟩
  end

  @[hott] protected def eqrec {A B : Type} {C : A ⊎ B → Type}
    (x : A ⊎ B) (cl : Π a, x = inl a → C (inl a)) (cr : Π b, x = inr b → C (inr b)) : C x :=
  begin
    induction x with a b,
    exact cl a idp, exact cr b idp
  end
  
  variables {z z'}
  @[hott] protected def encode (p : z = z') : sum.code z z' :=
  by induction p; induction z; exact ulift.up idp

  variables (z z')
  @[hott] def sum_eq_equiv : (z = z') ≃ sum.code z z' :=
  begin
    fapply equiv.MK, apply sum.encode, apply sum.decode,
    { induction z with a b; induction z' with a' b';
       intro b; induction b with b; induction b; reflexivity },
    { intro p, induction p, induction z; refl  }
  end

  section
  variables {a a' : A} {b b' : B}
  @[hott] def eq_of_inl_eq_inl (p : inl a = (inl a' : A ⊎ B)) : a = a' :=
  ulift.down (sum.encode p)
  @[hott] def eq_of_inr_eq_inr (p : inr b = (inr b' : A ⊎ B)) : b = b' :=
  ulift.down (sum.encode p)
  @[hott] def empty_of_inl_eq_inr (p : inl a = inr b) : empty :=
  ulift.down (sum.encode p)
  @[hott] def empty_of_inr_eq_inl (p : inr b = inl a) : empty := 
  ulift.down (sum.encode p)

  /- Transport -/

  @[hott] def sum_transport (p : a = a') (z : P a ⊎ Q a)
    : p ▸ z = sum.rec (λa, inl (p ▸ a)) (λb, inr (p ▸ b)) z :=
  by induction p; induction z; reflexivity

  /- Pathovers -/

  /-@[hott] def etao (p : a = a') (z : P a ⊎ Q a)
    : z =[p] sum.rec (λa, inl (p ▸ a)) (λb, inr (p ▸ b)) z :=
  by induction p; induction z; constructor

  protected def codeo (p : a = a') : P a ⊎ Q a → P a' ⊎ Q a' → Type.{max u' v'}
  | codeo (inl x) (inl x') := ulift.{u' v'} (x =[p] x')
  | codeo (inr y) (inr y') := ulift.{v' u'} (y =[p] y')
  | codeo _       _        := ulift empty

  protected def decodeo (p : a = a') : Π(z : P a ⊎ Q a) (z' : P a' ⊎ Q a'),
    sum.codeo p z z' → z =[p] z'
  | decodeo (inl x) (inl x') := λc, apo (λa, inl) (down c)
  | decodeo (inl x) (inr y') := λc, empty.elim (down c) _
  | decodeo (inr y) (inl x') := λc, empty.elim (down c) _
  | decodeo (inr y) (inr y') := λc, apo (λa, inr) (down c)

  variables {z z'}
  protected def encodeo {p : a = a'} {z : P a ⊎ Q a} {z' : P a' ⊎ Q a'} (q : z =[p] z')
    : sum.codeo p z z' :=
  by induction q; induction z; all_goals exact up idpo

  variables (z z')
  def sum_pathover_equiv [constructor] (p : a = a') (z : P a ⊎ Q a) (z' : P a' ⊎ Q a')
    : (z =[p] z') ≃ sum.codeo p z z' :=
  equiv.MK sum.encodeo
           !sum.decodeo
           abstract begin
             intro c, induction z with a b, all_goals induction z' with a' b',
             all_goals (esimp at *; induction c with c),
             all_goals induction c, -- c either has type empty or a pathover
             all_goals reflexivity
           end end
           abstract begin
             intro q, induction q, induction z, all_goals reflexivity
           end end
  end-/

  /- Functorial action -/

  universes u'' v''
  variables {A' : Type u''} {B' : Type v''}
  @[hott] def sum_functor (f : A → A') (g : B → B') : A ⊎ B → A' ⊎ B' :=
  begin
    intro z, induction z with a b, exact inl (f a), exact inr (g b)
  end

  infix ` +→ `:62 := sum_functor

  /- Equivalences -/

  @[hott, instance] def is_equiv_sum_functor (f : A → A') (g : B → B') 
    [Hf : is_equiv f] [Hg : is_equiv g] :
    is_equiv (sum_functor f g) :=
  begin
    fapply adjointify, refine sum_functor f⁻¹ᶠ g⁻¹ᶠ,
    { intro z, induction z, apply ap inl, apply right_inv,
      apply ap inr, apply right_inv },
    { intro z, induction z, apply ap inl, apply left_inv,
      apply ap inr, apply left_inv }
  end

  @[hott] def sum_equiv_sum_of_is_equiv (f : A → A') (g : B → B') 
    [Hf : is_equiv f] [Hg : is_equiv g]
    : A ⊎ B ≃ A' ⊎ B' :=
  equiv.mk _ (is_equiv_sum_functor f g)

  @[hott] def sum_equiv_sum (f : A ≃ A') (g : B ≃ B') : A ⊎ B ≃ A' ⊎ B' :=
  equiv.mk _ (is_equiv_sum_functor f g)

  infix ` +≃ `:62 := sum_equiv_sum

  @[hott] def sum_equiv_sum_left (g : B ≃ B') : A ⊎ B ≃ A ⊎ B' :=
  sum_equiv_sum equiv.rfl g

  @[hott] def sum_equiv_sum_right (f : A ≃ A') : A ⊎ B ≃ A' ⊎ B :=
  sum_equiv_sum f equiv.rfl

  @[hott] def flip : A ⊎ B → B ⊎ A :=
  begin
    intro z, induction z with a b, exact inr a, exact inl b
  end

  @[hott] def flip_flip (x : A ⊎ B) : flip (flip x) = x :=
  begin induction x; reflexivity end

  @[hott] def sum_comm_equiv (A B : Type  _) : A ⊎ B ≃ B ⊎ A :=
  equiv.MK flip flip flip_flip flip_flip

  @[hott] def sum_assoc_equiv (A B C : Type _) : A ⊎ (B ⊎ C) ≃ (A ⊎ B) ⊎ C :=
  begin
    fapply equiv.MK,
    { intro z, induction z with u v, exact inl (inl u),
      induction v, exact inl (inr v),
      exact inr v },
    { intro z, induction z with u v, induction u, exact (inl u),
      exact inr (inl u), exact inr (inr v) },
    { intro z, induction z with u v, induction u, refl, refl, refl },
    { intro z, induction z with u v, refl, induction v, refl, refl }
  end

  @[hott] def sum_empty_equiv (A : Type _) : A ⊎ empty ≃ A :=
  begin
    fapply equiv.MK,
    { intro z, induction z, assumption, apply empty.elim z },
    { exact inl},
    { intro a, reflexivity},
    { intro z, induction z, reflexivity, apply empty.elim z}
  end

  @[hott] def empty_sum_equiv  (A : Type _) : empty ⊎ A ≃ A :=
  sum_comm_equiv _ _ ⬝e sum_empty_equiv _

  @[hott] def bool_equiv_unit_sum_unit : bool ≃ unit ⊎ unit :=
  begin
    fapply equiv.MK,
    { intro b, cases b, exact inl unit.star, exact inr unit.star },
    { intro s, cases s, exact bool.ff, exact bool.tt },
    { intro s, cases s, repeat { cases s; refl } },
    { intro b, cases b, refl, refl },
  end

  @[hott] def sum_prod_right_distrib (A B C : Type _) :
    (A ⊎ B) × C ≃ (A × C) ⊎ (B × C) :=
  begin
    fapply equiv.MK,
    { intro x, cases x with ab c, cases ab with a b, exact inl (a, c), exact inr (b, c) },
    { intro x, cases x with ac bc, cases ac with a c, exact (inl a, c),
      cases bc with b c, exact (inr b, c) },
    { intro x, cases x with ac bc, cases ac with a c, refl, cases bc, refl },
    { intro x, cases x with ab c, cases ab with a b, refl, refl }
  end

  @[hott] def sum_prod_left_distrib (A B C : Type _) :
    A × (B ⊎ C) ≃ (A × B) ⊎ (A × C) :=
  calc A × (B ⊎ C) ≃ (B ⊎ C) × A : prod_comm_equiv _ _
               ... ≃ (B × A) ⊎ (C × A) : sum_prod_right_distrib _ _ _
               ... ≃ (A × B) ⊎ (C × A) : sum_equiv_sum_right (prod_comm_equiv _ _)
               ... ≃ (A × B) ⊎ (A × C) : sum_equiv_sum_left  (prod_comm_equiv _ _)

  section
  --variables (H : unit ⊎ A ≃ unit ⊎ B)
  --include H

  --open unit /-sigma.ops-/

  /-@[hott] def unit_sum_equiv_cancel_map : A → B :=
  begin
    intro a, cases sum.mem_cases (H (inr a)) with u b,
    cases u with u Hu, induction sum.mem_cases (H (inl unit.star)) with u' b,
     /-rotate 1, exact b.1,
    cases u with u Hu, cases sum.mem_cases (H (inl ⋆)) with u' b, rotate 1, exact b.1,
    cases u' with u' Hu', exfalso, apply empty_of_inl_eq_inr,
    calc inl ⋆ = H⁻¹ (H (inl ⋆)) : (to_left_inv H (inl ⋆))⁻¹
           ... = H⁻¹ (inl u') : {Hu'}
           ... = H⁻¹ (inl u) : is_prop.elim
           ... = H⁻¹ (H (inr a)) : {Hu⁻¹}
           ... = inr a : to_left_inv H (inr a)-/
  end

  def unit_sum_equiv_cancel_inv (b : B) :
    unit_sum_equiv_cancel_map H (unit_sum_equiv_cancel_map H⁻¹ᵉ b) = b :=
  begin
    esimp[unit_sum_equiv_cancel_map], apply sum.rec,
    { intro x, cases x with u Hu, esimp, apply sum.rec,
      { intro x, exfalso, cases x with u' Hu', apply empty_of_inl_eq_inr,
        calc inl ⋆ = H⁻¹ (H (inl ⋆)) : (to_left_inv H (inl ⋆))⁻¹
               ... = H⁻¹ (inl u')    : ap H⁻¹ Hu'
               ... = H⁻¹ (inl u)     : {!is_prop.elim}
               ... = H⁻¹ (H (inr _)) : {Hu⁻¹}
               ... = inr _ : to_left_inv H },
      { intro x, cases x with b' Hb', esimp, cases sum.mem_cases (H⁻¹ (inr b)) with x x,
        { cases x with u' Hu', cases u', apply eq_of_inr_eq_inr,
          calc inr b' = H (inl ⋆)       : Hb'⁻¹
                  ... = H (H⁻¹ (inr b)) : (ap H Hu')⁻¹
                  ... = inr b           : to_right_inv H (inr b)},
        { exfalso, cases x with a Ha, apply empty_of_inl_eq_inr,
          cases u, apply concat, apply Hu⁻¹, apply concat, rotate 1, apply !(to_right_inv H),
          apply ap H,
          apply concat, rotate 1, apply Ha⁻¹, apply ap inr, esimp,
          apply sum.rec, intro x, exfalso, apply empty_of_inl_eq_inr,
          apply concat, exact x.2⁻¹, apply Ha,
          intro x, cases x with a' Ha', esimp, apply eq_of_inr_eq_inr, apply Ha'⁻¹ ⬝ Ha } } },
    { intro x, cases x with b' Hb', esimp, apply eq_of_inr_eq_inr, refine Hb'⁻¹ ⬝ _,
      cases sum.mem_cases (H⁻¹ (inr b)) with x x,
      { cases x with u Hu, esimp, cases sum.mem_cases (H⁻¹ (inl ⋆)) with x x,
        { cases x with u' Hu', exfalso, apply empty_of_inl_eq_inr,
          calc inl ⋆ = H (H⁻¹ (inl ⋆))  : (to_right_inv H (inl ⋆))⁻¹
                 ... = H (inl u')       : ap H Hu'
                 ... = H (inl u)        : by rewrite [is_prop.elim u' u]
                 ... = H (H⁻¹ (inr b))  : ap H Hu⁻¹
                 ... = inr b            : to_right_inv H (inr b) },
      { cases x with a Ha, exfalso, apply empty_of_inl_eq_inr,
        apply concat, rotate 1, exact Hb',
        have Ha' : inl ⋆ = H (inr a), by apply !(to_right_inv H)⁻¹ ⬝ ap H Ha,
        apply concat Ha', apply ap H, apply ap inr, apply sum.rec,
          intro x, cases x with u' Hu', esimp, apply sum.rec,
            intro x, cases x with u'' Hu'', esimp, apply empty.rec,
            intro x, cases x with a'' Ha'', esimp, krewrite Ha' at Ha'', apply eq_of_inr_eq_inr,
            apply !(to_left_inv H)⁻¹ ⬝ Ha'',
          intro x, exfalso, cases x with a'' Ha'', apply empty_of_inl_eq_inr,
          apply Hu⁻¹ ⬝ Ha'', } },
      { cases x with a' Ha', esimp, refine _ ⬝ !(to_right_inv H), apply ap H,
        apply Ha'⁻¹ } }
  end

  def unit_sum_equiv_cancel : A ≃ B :=
  begin
    fapply equiv.MK, apply unit_sum_equiv_cancel_map H,
    apply unit_sum_equiv_cancel_map H⁻¹ᵉ,
    intro b, apply unit_sum_equiv_cancel_inv,
    { intro a, have H = (H⁻¹ᵉ)⁻¹ᵉ, from !equiv.symm_symm⁻¹, rewrite this at {2},
      apply unit_sum_equiv_cancel_inv }
  end
-/
  end
/-
  /- universal property -/

  def sum_rec_unc [unfold 5] {P : A ⊎ B → Type} (fg : (Πa, P (inl a)) × (Πb, P (inr b)))
    : Πz, P z :=
  sum.rec fg.1 fg.2

  def is_equiv_sum_rec [constructor] (P : A ⊎ B → Type)
    : is_equiv (sum_rec_unc : (Πa, P (inl a)) × (Πb, P (inr b)) → Πz, P z) :=
  begin
     apply adjointify sum_rec_unc (λf, (λa, f (inl a), λb, f (inr b))),
       intro f, apply eq_of_homotopy, intro z, focus (induction z; all_goals reflexivity),
       intro h, induction h with f g, reflexivity
  end

  def equiv_sum_rec [constructor] (P : A ⊎ B → Type)
    : (Πa, P (inl a)) × (Πb, P (inr b)) ≃ Πz, P z :=
  equiv.mk _ !is_equiv_sum_rec

  def imp_prod_imp_equiv_sum_imp [constructor] (A B C : Type)
    : (A → C) × (B → C) ≃ (A ⊎ B → C) :=
  !equiv_sum_rec-/

  /- truncatedness -/

  @[hott] def is_trunc_sum (n : ℕ₋₂) (A B : Type _) [HA : is_trunc (n.+1.+1) A] 
    [HB : is_trunc (n.+1.+1) B]
    : is_trunc (n.+1.+1) (A ⊎ B) :=
  begin
    apply is_trunc_succ_intro, intros z z',
    apply is_trunc_equiv_closed_rev, apply sum_eq_equiv,
    hinduction z with a b; hinduction z' with a' b';
    dsimp[sum.code]; infer
  end

  @[hott] def is_trunc_sum_excluded (n : ℕ₋₂) (A B : Type _) [HA : is_trunc n A]  [HB : is_trunc n B]
    (H : A → B → empty) : is_trunc n (A ⊎ B) :=
  begin
    resetI,
    induction n with n IH,
    { apply empty.elim, exact H (center _) (center _) },
    { clear IH, induction n with n IH,
      { apply is_prop.mk, intros x y,
        induction x; induction y;
        try { exfalso; apply H; assumption; assumption },
        apply ap inl, apply is_prop.elim,
        apply empty.elim, exact H x y,
        apply empty.elim, exact H y x,
        apply ap inr, apply is_prop.elim },
      { apply is_trunc_sum}}
  end

  @[hott] def is_contr_sum_left (A : Type _) {B : Type _} [HA : is_contr A] (H : ¬B) :
    is_contr (A ⊎ B) :=
  is_contr.mk (inl (center _))
              (λx, sum.rec_on x (λa, ap inl (center_eq _)) (λb, empty.elim (H b)))

  /-
    Sums are equivalent to dependent sigmas where the first component is a bool.

    The current construction only works for A and B in the same universe.
    If we need it for A and B in different universes, we need to insert some lifts.
  -/

  @[hott] def sum_of_sigma_bool {A B : Type u} (v : Σ(b : bool), bool.rec A B b) : A ⊎ B :=
  by { induction v with b x, induction b, exact inl x, exact inr x }

  @[hott] def sigma_bool_of_sum {A B : Type u} (z : A ⊎ B) : Σ(b : bool), bool.rec A B b :=
  by { induction z with a b, exact ⟨ff, a⟩, exact ⟨tt, b⟩ }

  @[hott] def sum_equiv_sigma_bool (A B : Type u)
    : A ⊎ B ≃ Σ(b : bool), bool.rec A B b :=
  equiv.MK sigma_bool_of_sum
           sum_of_sigma_bool
           begin intro v, induction v with b x, induction b; refl end
           begin intro z, induction z with a b; refl end

  variables {A₀₀ A₂₀ A₀₂ A₂₂ B₀₀ B₂₀ B₀₂ B₂₂ C C' : Type}
    {f₁₀ : A₀₀ → A₂₀} {f₁₂ : A₀₂ → A₂₂} {f₀₁ : A₀₀ → A₀₂} {f₂₁ : A₂₀ → A₂₂}
    {g₁₀ : B₀₀ → B₂₀} {g₁₂ : B₀₂ → B₂₂} {g₀₁ : B₀₀ → B₀₂} {g₂₁ : B₂₀ → B₂₂}
    {h₀₁ : B₀₀ → A₀₂} {h₂₁ : B₂₀ → A₂₂}
  open function

  /-@[hott] def sum_rec_hsquare (h : hsquare f₁₀ f₁₂ f₀₁ f₂₁)
    (k : hsquare g₁₀ f₁₂ h₀₁ h₂₁) : hsquare (f₁₀ +→ g₁₀) f₁₂ (sum.rec f₀₁ h₀₁) (sum.rec f₂₁ h₂₁) :=
  begin intro x, induction x with a b, exact h a, exact k b end

  def sum_functor_hsquare [unfold 19] (h : hsquare f₁₀ f₁₂ f₀₁ f₂₁)
    (k : hsquare g₁₀ g₁₂ g₀₁ g₂₁) : hsquare (f₁₀ +→ g₁₀) (f₁₂ +→ g₁₂) (f₀₁ +→ g₀₁) (f₂₁ +→ g₂₁) :=
  sum_rec_hsquare (λa, ap inl (h a)) (λb, ap inr (k b))-/

  /-@[hott] def sum_functor_compose (g : B → C) (f : A → B) (g' : B' → C') (f' : A' → B') :
    (g ∘ f) +→ (g' ∘ f') ~ g +→ g' ∘ f +→ f' :=
  begin intro x, induction x with a a': reflexivity end

  def sum_rec_sum_functor (g : B → C) (g' : B' → C) (f : A → B) (f' : A' → B') :
    sum.rec g g' ∘ sum_functor f f' ~ sum.rec (g ∘ f) (g' ∘ f') :=
  begin intro x, induction x with a a': reflexivity end

  def sum_rec_same_compose (g : B → C) (f : A → B) :
    sum.rec (g ∘ f) (g ∘ f) ~ g ∘ sum.rec f f :=
  begin intro x, induction x with a a': reflexivity end

  def sum_rec_same (f : A → B) : sum.rec f f ~ f ∘ sum.rec id id :=
  by exact sum_rec_same_compose f id-/

  /- pointed sums. We arbitrarily choose (inl pt) as basepoint for the sum -/

  open hott.pointed
  @[hott] def psum (A B : Type*) : Type* :=
  pointed.MK (A ⊎ B) (inl pt)

  infixr ` +* `:30 := psum
end 
end sum
open sum pi

namespace decidable

  /- some properties about the inductive type `decidable`
     decidable A is equivalent to A ⊎ ¬A -/
  @[hott] def decidable_equiv (A : Type _) : decidable A ≃ A ⊎ ¬A :=
  begin
    fapply equiv.MK; intro a; induction a; try { constructor, assumption },
    apply inr a, apply decidable.inr a,
    refl, refl, refl, refl
  end

  @[hott] def is_trunc_decidable (A : Type _) (n : ℕ₋₂) [H : is_trunc n A] :
    is_trunc n (decidable A) :=
  begin
    resetI,
    apply is_trunc_equiv_closed_rev,
    apply decidable_equiv,
    induction n with n IH,
    { apply is_contr_sum_left, exact λna, na (center _)},
    { apply is_trunc_sum_excluded, exact λa na, na a}
  end

  @[hott] def double_neg_elim {A : Type _} (H : decidable A) (p : ¬ ¬ A) : A :=
  begin resetI, induction H, assumption, apply empty.elim, exact p H end

  @[hott] def dite_true {C : Type _} [H : decidable C] {A : Type _}
    {t : C → A} {e : ¬ C → A} (c : C) (H' : is_prop C) : dite C t e = t c :=
  begin
    resetI, induction H with H H,
    exact ap t (is_prop.elim _ _),
    apply empty.elim, exact H c,
  end

  @[hott] def dite_false {C : Type _} [H : decidable C] {A : Type _}
    {t : C → A} {e : ¬ C → A} (c : ¬ C) : dite C t e = e c :=
  begin
    resetI, induction H with H H,
    apply empty.elim, exact c H,
    exact ap e (is_prop.elim _ _),
  end

  @[hott] def decidable_eq_of_is_prop (A : Type _) [is_prop A] 
    : hott.decidable_eq A :=
  λa a', decidable.inl (is_prop.elim _ _)

  @[hott, instance] def decidable_eq_sigma {A : Type _} (B : A → Type _)
    [HA : hott.decidable_eq A]
    [HB : Πa, hott.decidable_eq (B a)] : hott.decidable_eq (Σa, B a) :=
  begin
    intros v v', induction v with a b, induction v' with a' b',
    cases HA a a' with p np,
    { induction p, cases HB a b b' with q nq,
        induction q, exact decidable.inl idp,
        apply decidable.inr, intro p, apply nq, apply @eq_of_pathover_idp A B,
        exact change_path (is_prop.elim _ _) p..2 },
    { apply decidable.inr, intro p, apply np, exact p..1 }
  end

  open sum
  @[hott, instance] def decidable_eq_sum (A B : Type _)
    [HA : hott.decidable_eq A] [HB : hott.decidable_eq B] :
    hott.decidable_eq (A ⊎ B) :=
  begin
    intros v v', induction v with a b; induction v' with a' b',
    { hinduction HA a a',
      { exact decidable.inl (ap sum.inl a_1) },
      { apply decidable.inr, intro p, apply a_1, exact ulift.down (sum.encode p) }},
    { apply decidable.inr, intro p, apply empty_of_inl_eq_inr p },
    { apply decidable.inr, intro p, apply empty_of_inr_eq_inl p },
    { hinduction HB b b',
      { exact decidable.inl (ap sum.inr a) },
      { apply decidable.inr, intro p, apply a, exact ulift.down (sum.encode p) }},
  end

end decidable

@[hott]def tsum {n : ℕ₋₂} (A B : (n.+2)-Type) : (n.+2)-Type :=
trunctype.mk (A ⊎ B) (is_trunc_sum _ _ _)

infixr `+t`:25 := tsum
