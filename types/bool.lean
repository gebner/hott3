/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura, Floris van Doorn

Partially ported from the standard library
-/
import ..init

universes u v w
hott_theory

namespace hott
open decidable

namespace bool
  -- local attribute bor [reducible]
  -- local attribute band [reducible]

  @[hott] def dichotomy : ∀ b, b = ff ⊎ b = tt
  | ff := sum.inl rfl
  | tt := sum.inr rfl

  @[hott, hsimp] def cond_ff {A : Type _} (t e : A) : cond ff t e = e :=
  idp

  @[hott, hsimp] def cond_tt {A : Type _} (t e : A) : cond tt t e = t :=
  idp

  @[hott] def eq_tt_of_ne_ff : Π {a : bool}, a ≠ ff → a = tt
  | tt H := rfl
  | ff H := absurd rfl H

  @[hott] def eq_ff_of_ne_tt : Π {a : bool}, a ≠ tt → a = ff
  | tt H := absurd rfl H
  | ff H := rfl

  @[hott] def absurd_of_eq_ff_of_eq_tt {B : Type _} {a : bool} (H₁ : a = ff) (H₂ : a = tt) : B :=
  absurd (H₁⁻¹ ⬝ H₂) ff_ne_tt

  @[hott, hsimp] def tt_bor (a : bool) : tt || a = tt :=
  idp

  @[hott, hsimp] def bor_tt (a : bool) : a || tt = tt :=
  by cases a; refl

  @[hott, hsimp] def ff_bor (a : bool) : ff || a = a :=
  by cases a; refl

  @[hott, hsimp] def bor_ff (a : bool) : a || ff = a :=
  by cases a; refl

  @[hott, hsimp] def bor_self (a : bool) : a || a = a :=
  by cases a; refl

  @[hott, hsimp] def bor.comm (a b : bool) : a || b = b || a :=
  by cases a; repeat { cases b <|> reflexivity }

  @[hott, hsimp] def bor.assoc (a b c) : (a || b) || c = a || (b || c) :=
  by cases a; hsimp

  @[hott] def or_of_bor_eq : Π {a b}, a || b = tt → a = tt ⊎ b = tt
  | ff b H := sum.inr (by hsimp at H; assumption)
  | tt b H := sum.inl idp

  @[hott] def bor_inl {a b : bool} (H : a = tt) : a || b = tt :=
  by rwr H

  @[hott] def bor_inr {a b : bool} (H : b = tt) : a || b = tt :=
  by cases a; rwr H

  @[hott, hsimp] def ff_band (a : bool) : ff && a = ff :=
  rfl

  @[hott, hsimp] def tt_band (a : bool) : tt && a = a :=
  by cases a; refl

  @[hott, hsimp] def band_ff (a : bool) : a && ff = ff :=
  by cases a; refl

  @[hott, hsimp] def band_tt (a : bool) : a && tt = a :=
  by cases a; refl

  @[hott, hsimp] def band_self (a : bool) : a && a = a :=
  by cases a; refl

  @[hott, hsimp] def band.comm (a b : bool) : a && b = b && a :=
  by cases a; cases b; refl

  @[hott, hsimp] def band.assoc (a b c : bool) : (a && b) && c = a && (b && c) :=
  by cases a; hsimp

  @[hott] def band_elim_left {a b : bool} (H : a && b = tt) : a = tt :=
  by cases a; hsimp at H; assumption

  @[hott] def band_intro {a b : bool} (H₁ : a = tt) (H₂ : b = tt) : a && b = tt :=
  by hsimp *

  @[hott] def band_elim_right {a b : bool} (H : a && b = tt) : b = tt :=
  by apply band_elim_left; rwra band.comm

  @[hott, hsimp] def bnot_bnot (a : bool) : bnot (bnot a) = a :=
  bool.cases_on a rfl rfl

  @[hott, hsimp] def bnot_empty : bnot ff = tt :=
  rfl

  @[hott, hsimp] def bnot_unit  : bnot tt = ff :=
  rfl

  @[hott] def eq_tt_of_bnot_eq_ff {a : bool} : bnot a = ff → a = tt :=
  bool.cases_on a (by dsimp; intro; hsimp*) (λ h, rfl)

  @[hott] def eq_ff_of_bnot_eq_tt {a : bool} : bnot a = tt → a = ff :=
  bool.cases_on a (λ h, rfl) (by dsimp; intro; hsimp*)

  /- HoTT-related stuff -/
  open is_equiv equiv function is_trunc option unit decidable

  @[hott, instance] def is_equiv_bnot : is_equiv bnot :=
  by fapply is_equiv.mk bnot bnot; intro a; cases a; refl

  @[hott] def bnot_ne : Π(b : bool), bnot b ≠ b
  | tt := ff_ne_tt
  | ff := ne.symm ff_ne_tt

  @[hott] def equiv_bnot : bool ≃ bool := equiv.mk bnot (by apply_instance)
  @[hott] def eq_bnot    : bool = bool := ua equiv_bnot

  @[hott] def eq_bnot_ne_idp : eq_bnot ≠ idp :=
  assume H : eq_bnot = idp,
  have H2 : bnot = id, from (cast_ua_fn equiv_bnot).inverse ⬝ ap cast H,
  absurd (ap10 H2 tt) ff_ne_tt

  @[hott] def is_set_bool : is_set bool := by apply_instance
  @[hott] def not_is_prop_bool_eq_bool : ¬ is_prop (bool = bool) :=
  λ H, eq_bnot_ne_idp (by apply is_prop.elim)

  @[hott] def bool_equiv_option_unit : bool ≃ option unit :=
  begin
    fapply equiv.MK,
    { intro b, cases b, exact none, exact some star},
    { intro u, cases u, exact ff, exact tt},
    { intro u, cases u with u, reflexivity, cases u, reflexivity},
    { intro b, cases b, reflexivity, reflexivity},
  end

  /- pointed and truncated bool -/
  open pointed
  @[hott, instance] def pointed_bool : pointed bool :=
  pointed.mk ff

  @[hott] def pbool : Set* :=
  pSet.mk' bool

  @[hott] def tbool : Set := trunctype.mk bool (by apply_instance)

  notation `bool*` := pbool


end bool

end hott