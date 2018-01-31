/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Jakob von Raumer

Squares in a type
-/
import hott.types.eq

universes u v w
hott_theory

namespace hott
open eq hott.equiv hott.is_equiv

namespace eq

  variables {A : Type _} {B : Type _} {C : Type _}
       {a a' a'' a₀₀ a₂₀ a₄₀ a₀₂ a₂₂ a₂₄ a₀₄ a₄₂ a₄₄ a₁ a₂ a₃ a₄ : A}
            /-a₀₀-/ {p₁₀ p₁₀' : a₀₀ = a₂₀} /-a₂₀-/ {p₃₀ : a₂₀ = a₄₀} /-a₄₀-/
       {p₀₁ p₀₁' : a₀₀ = a₀₂} /-s₁₁-/ {p₂₁ p₂₁' : a₂₀ = a₂₂} /-s₃₁-/ {p₄₁ : a₄₀ = a₄₂}
            /-a₀₂-/ {p₁₂ p₁₂' : a₀₂ = a₂₂} /-a₂₂-/ {p₃₂ : a₂₂ = a₄₂} /-a₄₂-/
       {p₀₃ : a₀₂ = a₀₄} /-s₁₃-/ {p₂₃ : a₂₂ = a₂₄} /-s₃₃-/ {p₄₃ : a₄₂ = a₄₄}
            /-a₀₄-/ {p₁₄ : a₀₄ = a₂₄} /-a₂₄-/ {p₃₄ : a₂₄ = a₄₄} /-a₄₄-/
            {b : B} {c : C}

  inductive square {A : Type u} {a₀₀ : A}
    : Π{a₂₀ a₀₂ a₂₂ : A}, a₀₀ = a₂₀ → a₀₂ = a₂₂ → a₀₀ = a₀₂ → a₂₀ = a₂₂ → Type u
  | ids : square idp idp idp idp
  /- square top bottom left right -/

  variables {s₁₁ : square p₁₀ p₁₂ p₀₁ p₂₁} {s₃₁ : square p₃₀ p₃₂ p₂₁ p₄₁}
            {s₁₃ : square p₁₂ p₁₄ p₀₃ p₂₃} {s₃₃ : square p₃₂ p₃₄ p₂₃ p₄₃}

  @[hott, reducible] def ids              := @square.ids
  @[hott, reducible] def idsquare (a : A) := @square.ids A a

  @[hott] def hrefl (p : a = a') : square idp idp p p :=
  by induction p; exact ids

  @[hott] def vrefl (p : a = a') : square p p idp idp :=
  by induction p; exact ids

  @[hott, reducible] def hrfl {p : a = a'} : square idp idp p p := hrefl _
  @[hott, reducible] def vrfl {p : a = a'} : square p p idp idp := vrefl _

  @[hott] def hdeg_square {p q : a = a'} (r : p = q) : square idp idp p q :=
  by induction r;apply hrefl

  @[hott] def vdeg_square {p q : a = a'} (r : p = q) : square p q idp idp :=
  by induction r;apply vrefl

  @[hott, hsimp] def hdeg_square_idp (p : a = a') : hdeg_square (refl p) = hrfl :=
  idp

  @[hott, hsimp] def vdeg_square_idp (p : a = a') : vdeg_square (refl p) = vrfl :=
  idp

  @[hott] def hconcat (s₁₁ : square p₁₀ p₁₂ p₀₁ p₂₁) (s₃₁ : square p₃₀ p₃₂ p₂₁ p₄₁)
    : square (p₁₀ ⬝ p₃₀) (p₁₂ ⬝ p₃₂) p₀₁ p₄₁ :=
  by induction s₃₁; exact s₁₁

  @[hott] def vconcat (s₁₁ : square p₁₀ p₁₂ p₀₁ p₂₁) (s₁₃ : square p₁₂ p₁₄ p₀₃ p₂₃)
    : square p₁₀ p₁₄ (p₀₁ ⬝ p₀₃) (p₂₁ ⬝ p₂₃) :=
  by induction s₁₃; exact s₁₁

  @[hott] def dconcat {p₀₀ : a₀₀ = a} {p₂₂ : a = a₂₂}
    (s₂₁ : square p₀₀ p₁₂ p₀₁ p₂₂) (s₁₂ : square p₁₀ p₂₂ p₀₀ p₂₁) : square p₁₀ p₁₂ p₀₁ p₂₁ :=
  by induction s₁₂; exact s₂₁

  @[hott] def hinverse (s₁₁ : square p₁₀ p₁₂ p₀₁ p₂₁) : square p₁₀⁻¹ p₁₂⁻¹ p₂₁ p₀₁ :=
  by induction s₁₁;exact ids

  @[hott] def vinverse (s₁₁ : square p₁₀ p₁₂ p₀₁ p₂₁) : square p₁₂ p₁₀ p₀₁⁻¹ p₂₁⁻¹ :=
  by induction s₁₁;exact ids

  @[hott] def eq_vconcat {p : a₀₀ = a₂₀} (r : p = p₁₀) (s₁₁ : square p₁₀ p₁₂ p₀₁ p₂₁) :
    square p p₁₂ p₀₁ p₂₁ :=
  by induction r; exact s₁₁

  @[hott] def vconcat_eq {p : a₀₂ = a₂₂} (s₁₁ : square p₁₀ p₁₂ p₀₁ p₂₁) (r : p₁₂ = p) :
    square p₁₀ p p₀₁ p₂₁ :=
  by induction r; exact s₁₁

  @[hott] def eq_hconcat {p : a₀₀ = a₀₂} (r : p = p₀₁) (s₁₁ : square p₁₀ p₁₂ p₀₁ p₂₁) :
    square p₁₀ p₁₂ p p₂₁ :=
  by induction r; exact s₁₁

  @[hott] def hconcat_eq {p : a₂₀ = a₂₂} (s₁₁ : square p₁₀ p₁₂ p₀₁ p₂₁) (r : p₂₁ = p) :
    square p₁₀ p₁₂ p₀₁ p :=
  by induction r; exact s₁₁

  infix ` ⬝h `:69 := hconcat --type using \tr
  infix ` ⬝v `:70 := vconcat --type using \tr
  infixl ` ⬝hp `:71 := hconcat_eq --type using \tr
  infixl ` ⬝vp `:73 := vconcat_eq --type using \tr
  infixr ` ⬝ph `:72 := eq_hconcat --type using \tr
  infixr ` ⬝pv `:74 := eq_vconcat --type using \tr
  postfix `⁻¹ʰ`:(max+1) := hinverse --type using \-1h
  postfix `⁻¹ᵛ`:(max+1) := vinverse --type using \-1v

  @[hott] def transpose (s₁₁ : square p₁₀ p₁₂ p₀₁ p₂₁) : square p₀₁ p₂₁ p₁₀ p₁₂ :=
  by induction s₁₁;exact ids

  @[hott] def aps (f : A → B) (s₁₁ : square p₁₀ p₁₂ p₀₁ p₂₁)
    : square (ap f p₁₀) (ap f p₁₂) (ap f p₀₁) (ap f p₂₁) :=
  by induction s₁₁;exact ids

  /- canceling, whiskering and moving thinks along the sides of the square -/
  @[hott] def whisker_tl (p : a = a₀₀) (s₁₁ : square p₁₀ p₁₂ p₀₁ p₂₁)
    : square (p ⬝ p₁₀) p₁₂ (p ⬝ p₀₁) p₂₁ :=
  by induction s₁₁;induction p;constructor

  @[hott] def whisker_br (p : a₂₂ = a) (s₁₁ : square p₁₀ p₁₂ p₀₁ p₂₁)
    : square p₁₀ (p₁₂ ⬝ p) p₀₁ (p₂₁ ⬝ p) :=
  by induction p;exact s₁₁

  @[hott] def whisker_rt (p : a = a₂₀) (s₁₁ : square p₁₀ p₁₂ p₀₁ p₂₁)
    : square (p₁₀ ⬝ p⁻¹) p₁₂ p₀₁ (p ⬝ p₂₁) :=
  by induction s₁₁;induction p;constructor

  @[hott] def whisker_tr (p : a₂₀ = a) (s₁₁ : square p₁₀ p₁₂ p₀₁ p₂₁)
    : square (p₁₀ ⬝ p) p₁₂ p₀₁ (p⁻¹ ⬝ p₂₁) :=
  by induction s₁₁;induction p;constructor

  @[hott] def whisker_bl (p : a = a₀₂) (s₁₁ : square p₁₀ p₁₂ p₀₁ p₂₁)
    : square p₁₀ (p ⬝ p₁₂) (p₀₁ ⬝ p⁻¹) p₂₁ :=
  by induction s₁₁;induction p;constructor

  @[hott] def whisker_lb (p : a₀₂ = a) (s₁₁ : square p₁₀ p₁₂ p₀₁ p₂₁)
    : square p₁₀ (p⁻¹ ⬝ p₁₂) (p₀₁ ⬝ p) p₂₁ :=
  by induction s₁₁;induction p;constructor

  @[hott] def cancel_tl (p : a = a₀₀) (s₁₁ : square (p ⬝ p₁₀) p₁₂ (p ⬝ p₀₁) p₂₁)
    : square p₁₀ p₁₂ p₀₁ p₂₁ :=
  by induction p; hsimp at s₁₁; exact s₁₁

  @[hott] def cancel_br (p : a₂₂ = a) (s₁₁ : square p₁₀ (p₁₂ ⬝ p) p₀₁ (p₂₁ ⬝ p))
    : square p₁₀ p₁₂ p₀₁ p₂₁ :=
  by induction p;exact s₁₁

  @[hott] def cancel_rt (p : a = a₂₀) (s₁₁ : square (p₁₀ ⬝ p⁻¹) p₁₂ p₀₁ (p ⬝ p₂₁))
    : square p₁₀ p₁₂ p₀₁ p₂₁ :=
  by induction p; hsimp at s₁₁; exact s₁₁

  @[hott] def cancel_tr (p : a₂₀ = a) (s₁₁ : square (p₁₀ ⬝ p) p₁₂ p₀₁ (p⁻¹ ⬝ p₂₁))
    : square p₁₀ p₁₂ p₀₁ p₂₁ :=
  by induction p; hsimp at s₁₁; exact s₁₁

  @[hott] def cancel_bl (p : a = a₀₂) (s₁₁ : square p₁₀ (p ⬝ p₁₂) (p₀₁ ⬝ p⁻¹) p₂₁)
    : square p₁₀ p₁₂ p₀₁ p₂₁ :=
  by induction p; hsimp at s₁₁; exact s₁₁

  @[hott] def cancel_lb (p : a₀₂ = a) (s₁₁ : square p₁₀ (p⁻¹ ⬝ p₁₂) (p₀₁ ⬝ p) p₂₁)
    : square p₁₀ p₁₂ p₀₁ p₂₁ :=
  by induction p; hsimp at s₁₁; exact s₁₁

  @[hott] def move_top_of_left   {p : a₀₀ = a} {q : a = a₀₂} (s : square p₁₀ p₁₂ (p ⬝ q) p₂₁)
    : square (p⁻¹ ⬝ p₁₀) p₁₂ q p₂₁ :=
  by apply cancel_tl p; hsimp; exact s

  @[hott] def move_top_of_left'  {p : a = a₀₀} {q : a = a₀₂} (s : square p₁₀ p₁₂ (p⁻¹ ⬝ q) p₂₁)
    : square (p ⬝ p₁₀) p₁₂ q p₂₁ :=
  by apply cancel_tl p⁻¹; hsimp; exact s

  @[hott] def move_left_of_top   {p : a₀₀ = a} {q : a = a₂₀} (s : square (p ⬝ q) p₁₂ p₀₁ p₂₁)
    : square q p₁₂ (p⁻¹ ⬝ p₀₁) p₂₁ :=
  by apply cancel_tl p; hsimp; exact s

  @[hott] def move_left_of_top'  {p : a = a₀₀} {q : a = a₂₀} (s : square (p⁻¹ ⬝ q) p₁₂ p₀₁ p₂₁)
    : square q p₁₂ (p ⬝ p₀₁) p₂₁ :=
  by apply cancel_tl p⁻¹; hsimp; exact s

  @[hott] def move_bot_of_right  {p : a₂₀ = a} {q : a = a₂₂} (s : square p₁₀ p₁₂ p₀₁ (p ⬝ q))
    : square p₁₀ (p₁₂ ⬝ q⁻¹) p₀₁ p :=
  by apply cancel_br q; hsimp; exact s

  @[hott] def move_bot_of_right' {p : a₂₀ = a} {q : a₂₂ = a} (s : square p₁₀ p₁₂ p₀₁ (p ⬝ q⁻¹))
    : square p₁₀ (p₁₂ ⬝ q) p₀₁ p :=
  by apply cancel_br q⁻¹; hsimp; exact s

  @[hott] def move_right_of_bot  {p : a₀₂ = a} {q : a = a₂₂} (s : square p₁₀ (p ⬝ q) p₀₁ p₂₁)
    : square p₁₀ p p₀₁ (p₂₁ ⬝ q⁻¹) :=
  by apply cancel_br q; hsimp; exact s

  @[hott] def move_right_of_bot' {p : a₀₂ = a} {q : a₂₂ = a} (s : square p₁₀ (p ⬝ q⁻¹) p₀₁ p₂₁)
    : square p₁₀ p p₀₁ (p₂₁ ⬝ q) :=
  by apply cancel_br q⁻¹; hsimp; exact s

  @[hott] def move_top_of_right  {p : a₂₀ = a} {q : a = a₂₂} (s : square p₁₀ p₁₂ p₀₁ (p ⬝ q))
    : square (p₁₀ ⬝ p) p₁₂ p₀₁ q :=
  by apply cancel_rt p; hsimp; exact s

  @[hott] def move_right_of_top  {p : a₀₀ = a} {q : a = a₂₀} (s : square (p ⬝ q) p₁₂ p₀₁ p₂₁)
    : square p p₁₂ p₀₁ (q ⬝ p₂₁) :=
  by apply cancel_tr q; hsimp; exact s

  @[hott] def move_bot_of_left   {p : a₀₀ = a} {q : a = a₀₂} (s : square p₁₀ p₁₂ (p ⬝ q) p₂₁)
    : square  p₁₀ (q ⬝ p₁₂) p p₂₁ :=
  by apply cancel_lb q; hsimp; exact s

  @[hott] def move_left_of_bot   {p : a₀₂ = a} {q : a = a₂₂} (s : square p₁₀ (p ⬝ q) p₀₁ p₂₁)
    : square p₁₀ q (p₀₁ ⬝ p) p₂₁ :=
  by apply cancel_bl p; hsimp; exact s

  /- some higher ∞-groupoid operations -/

  @[hott] def vconcat_vrfl (s₁₁ : square p₁₀ p₁₂ p₀₁ p₂₁)
    : s₁₁ ⬝v vrefl p₁₂ = s₁₁ :=
  by induction s₁₁; reflexivity

  @[hott] def hconcat_hrfl (s₁₁ : square p₁₀ p₁₂ p₀₁ p₂₁)
    : s₁₁ ⬝h hrefl p₂₁ = s₁₁ :=
  by induction s₁₁; reflexivity

  /- equivalences -/

  @[hott] def eq_of_square (s₁₁ : square p₁₀ p₁₂ p₀₁ p₂₁) : p₁₀ ⬝ p₂₁ = p₀₁ ⬝ p₁₂ :=
  by induction s₁₁; apply idp

  @[hott] def square_of_eq (r : p₁₀ ⬝ p₂₁ = p₀₁ ⬝ p₁₂) : square p₁₀ p₁₂ p₀₁ p₂₁ :=
  by induction p₁₂; dsimp at r; induction r; induction p₂₁; induction p₁₀; exact ids

  @[hott] def eq_top_of_square (s₁₁ : square p₁₀ p₁₂ p₀₁ p₂₁)
    : p₁₀ = p₀₁ ⬝ p₁₂ ⬝ p₂₁⁻¹ :=
  by induction s₁₁; apply idp

  @[hott] def square_of_eq_top (r : p₁₀ = p₀₁ ⬝ p₁₂ ⬝ p₂₁⁻¹) : square p₁₀ p₁₂ p₀₁ p₂₁ :=
  by induction p₂₁; induction p₁₂; dsimp at r;induction r;induction p₁₀;exact ids

  @[hott] def eq_bot_of_square (s₁₁ : square p₁₀ p₁₂ p₀₁ p₂₁)
    : p₁₂ = p₀₁⁻¹ ⬝ p₁₀ ⬝ p₂₁ :=
  by induction s₁₁; apply idp

  @[hott] def square_of_eq_bot (r : p₀₁⁻¹ ⬝ p₁₀ ⬝ p₂₁ = p₁₂) : square p₁₀ p₁₂ p₀₁ p₂₁ :=
  by induction p₂₁; induction p₁₀; dsimp at r; induction r; induction p₀₁; exact ids

  @[hott] def square_equiv_eq (t : a₀₀ = a₀₂) (b : a₂₀ = a₂₂)
    (l : a₀₀ = a₂₀) (r : a₀₂ = a₂₂) : square t b l r ≃ t ⬝ r = l ⬝ b :=
  begin
    fapply equiv.MK,
    { exact eq_of_square},
    { exact square_of_eq},
    { intro s, induction b, dsimp [concat] at s, induction s, induction r, induction t, apply idp},
    { intro s, induction s, apply idp},
  end

  @[hott] def hdeg_square_equiv' (p q : a = a') : square idp idp p q ≃ p = q :=
  begin
    transitivity, {apply square_equiv_eq},
    transitivity, {apply eq_equiv_eq_symm},
    {apply equiv_eq_closed_right, apply idp_con},
  end

  @[hott] def vdeg_square_equiv' (p q : a = a') : square p q idp idp ≃ p = q :=
  begin
    transitivity, {apply square_equiv_eq},
    {apply equiv_eq_closed_right, apply idp_con},
  end

  @[hott] def eq_of_hdeg_square {p q : a = a'} (s : square idp idp p q) : p = q :=
  to_fun (hdeg_square_equiv' _ _) s

  @[hott] def eq_of_vdeg_square {p q : a = a'} (s : square p q idp idp) : p = q :=
  to_fun (vdeg_square_equiv' _ _) s

  @[hott] def top_deg_square (l : a₁ = a₂) (b : a₂ = a₃) (r : a₄ = a₃)
    : square (l ⬝ b ⬝ r⁻¹) b l r :=
  by induction r;induction b;induction l;constructor

  @[hott] def bot_deg_square (l : a₁ = a₂) (t : a₁ = a₃) (r : a₃ = a₄)
    : square t (l⁻¹ ⬝ t ⬝ r) l r :=
  by induction r;induction t;induction l;constructor

  /-
    the following two equivalences have as underlying inverse function the functions
    hdeg_square and vdeg_square, respectively.
    See example below the @[hott] def
  -/
  @[hott] def hdeg_square_equiv (p q : a = a') :
    square idp idp p q ≃ p = q :=
  begin
    fapply equiv_change_fun,
    { fapply equiv_change_inv, apply hdeg_square_equiv', exact hdeg_square,
        intro s, induction s, induction p, reflexivity},
    { exact eq_of_hdeg_square},
    { reflexivity}
  end

  @[hott] def vdeg_square_equiv (p q : a = a') :
    square p q idp idp ≃ p = q :=
  begin
    fapply equiv_change_fun,
    { fapply equiv_change_inv, apply vdeg_square_equiv',exact vdeg_square,
        intro s, induction s, induction p, reflexivity},
    { exact eq_of_vdeg_square},
    { reflexivity}
  end

  example (p q : a = a') : (hdeg_square_equiv p q)⁻¹ᶠ = hdeg_square := idp

  /-
    characterization of pathovers in a equality type. The type B of the equality is fixed here.
    A version where B may also varies over the path p is given in the file squareover
  -/

  @[hott] def eq_pathover {f g : A → B} {p : a = a'} {q : f a = g a} {r : f a' = g a'}
    (s : square q r (ap f p) (ap g p)) : q =[p; λ a, f a  = g a] r :=
  begin induction p, apply pathover_idp_of_eq, exact eq_of_vdeg_square s end

  @[hott] def eq_pathover_constant_left {g : A → B} {p : a = a'} {b : B} {q : b = g a} {r : b = g a'}
    (s : square q r idp (ap g p)) : q =[p; λ a, b = g a] r :=
  eq_pathover (ap_constant p b ⬝ph s)

  @[hott] def eq_pathover_id_left {g : A → A} {p : a = a'} {q : a = g a} {r : a' = g a'}
    (s : square q r p (ap g p)) : q =[p; λ a, a = g a] r :=
  eq_pathover (ap_id p ⬝ph s)

  @[hott] def eq_pathover_constant_right {f : A → B} {p : a = a'} {b : B} {q : f a = b} {r : f a' = b}
    (s : square q r (ap f p) idp) : q =[p; λ a, f a = b] r :=
  eq_pathover (s ⬝hp (ap_constant p b)⁻¹)

  @[hott] def eq_pathover_id_right {f : A → A} {p : a = a'} {q : f a = a} {r : f a' = a'}
    (s : square q r (ap f p) p) : q =[p; λ a, f a = a] r :=
  eq_pathover (s ⬝hp (ap_id p)⁻¹)

  @[hott] def square_of_pathover
    {f g : A → B} {p : a = a'} {q : f a = g a} {r : f a' = g a'}
    (s : q =[p; λ a, f a = g a] r) : square q r (ap f p) (ap g p) :=
  by induction p;apply vdeg_square;exact (eq_of_pathover_idp s)

  @[hott] def eq_pathover_constant_left_id_right {p : a = a'} {a₀ : A} {q : a₀ = a} {r : a₀ = a'}
    (s : square q r idp p) : q =[p] r :=
  eq_pathover (ap_constant p a₀ ⬝ph s ⬝hp (ap_id p)⁻¹)

  @[hott] def eq_pathover_id_left_constant_right {p : a = a'} {a₀ : A} {q : a = a₀} {r : a' = a₀}
    (s : square q r p idp) : q =[p; λ a, a = a₀] r :=
  eq_pathover (ap_id p ⬝ph s ⬝hp (ap_constant p a₀)⁻¹)

  @[hott] def loop_pathover {p : a = a'} {q : a = a} {r : a' = a'} (s : square q r p p) : q =[p; λ a, a = a] r :=
  eq_pathover (ap_id p ⬝ph s ⬝hp (ap_id p)⁻¹)

  /- interaction of equivalences with operations on squares -/

  @[hott] def eq_pathover_equiv_square {f g : A → B}
    (p : a = a') (q : f a = g a) (r : f a' = g a') : q =[p; λ a, f a = g a] r ≃ square q r (ap f p) (ap g p) :=
  equiv.MK square_of_pathover
           eq_pathover
           begin
             intro s, induction p, dsimp [square_of_pathover,eq_pathover],
             transitivity, {apply ap vdeg_square, apply to_right_inv (pathover_idp _ _ _)},
             {apply to_left_inv (vdeg_square_equiv _ _)}
           end
           begin
             intro s, induction p, dsimp [square_of_pathover,eq_pathover],
             transitivity, {apply ap (pathover_idp_of_eq _), apply to_right_inv (vdeg_square_equiv _ _)},
             {apply to_left_inv (pathover_idp _ _ _)},
           end

  @[hott] def square_of_pathover_eq_concato {f g : A → B} {p : a = a'} {q q' : f a = g a}
    {r : f a' = g a'} (s' : q = q') (s : q' =[p; λ a, f a = g a] r)
    : square_of_pathover (s' ⬝po s) = s' ⬝pv square_of_pathover s :=
  by induction s;induction s';reflexivity

  @[hott] def square_of_pathover_concato_eq {f g : A → B} {p : a = a'} {q : f a = g a}
    {r r' : f a' = g a'} (s' : r = r') (s : q =[p; λ a, f a = g a] r)
    : square_of_pathover (s ⬝op s') = square_of_pathover s ⬝vp s' :=
  by induction s;induction s';reflexivity

  @[hott] def square_of_pathover_concato {f g : A → B} {p : a = a'} {p' : a' = a''} {q : f a = g a}
    {q' : f a' = g a'} {q'' : f a'' = g a''} (s : q =[p; λ a, f a = g a] q') (s' : q' =[p'; λ a, f a = g a] q'')
    : square_of_pathover (s ⬝o s')
  = ap_con f p p' ⬝ph (square_of_pathover s ⬝v square_of_pathover s') ⬝hp (ap_con g p p')⁻¹ :=
  by induction s'; induction s; symmetry; apply vconcat_vrfl

  @[hott] def eq_of_square_hrfl (p : a = a') : eq_of_square hrfl = idp_con p :=
  by induction p;reflexivity

  @[hott] def eq_of_square_vrfl (p : a = a') : eq_of_square vrfl = (idp_con p)⁻¹ :=
  by induction p;reflexivity

  @[hott] def eq_of_square_hdeg_square {p q : a = a'} (r : p = q)
    : eq_of_square (hdeg_square r) = !idp_con ⬝ r⁻¹ :=
  by induction r;induction p;reflexivity

  @[hott] def eq_of_square_vdeg_square {p q : a = a'} (r : p = q)
    : eq_of_square (vdeg_square r) = r ⬝ !idp_con⁻¹ :=
  by induction r;induction p;reflexivity

  @[hott] def eq_of_square_eq_vconcat {p : a₀₀ = a₂₀} (r : p = p₁₀) (s₁₁ : square p₁₀ p₁₂ p₀₁ p₂₁)
    : eq_of_square (r ⬝pv s₁₁) = whisker_right p₂₁ r ⬝ eq_of_square s₁₁ :=
  by induction s₁₁; eq_cases r;reflexivity

  @[hott] def eq_of_square_eq_hconcat {p : a₀₀ = a₀₂} (r : p = p₀₁) (s₁₁ : square p₁₀ p₁₂ p₀₁ p₂₁)
    : eq_of_square (r ⬝ph s₁₁) = eq_of_square s₁₁ ⬝ (whisker_right p₁₂ r)⁻¹ :=
  by induction r;reflexivity

  @[hott] def eq_of_square_vconcat_eq {p : a₀₂ = a₂₂} (s₁₁ : square p₁₀ p₁₂ p₀₁ p₂₁) (r : p₁₂ = p)
    : eq_of_square (s₁₁ ⬝vp r) = eq_of_square s₁₁ ⬝ whisker_left p₀₁ r :=
  by induction r;reflexivity

  @[hott] def eq_of_square_hconcat_eq {p : a₂₀ = a₂₂} (s₁₁ : square p₁₀ p₁₂ p₀₁ p₂₁) (r : p₂₁ = p)
    : eq_of_square (s₁₁ ⬝hp r) = (whisker_left p₁₀ r)⁻¹ ⬝ eq_of_square s₁₁ :=
  by induction s₁₁; induction r;reflexivity

  @[hott] def change_path_eq_pathover {A B : Type _} {a a' : A} {f g : A → B}
    {p p' : a = a'} (r : p = p')
    {q : f a = g a} {q' : f a' = g a'}
    (s : square q q' (ap f p) (ap g p)) :
    change_path r (eq_pathover s) = eq_pathover ((ap02 f r)⁻¹ ⬝ph s ⬝hp (ap02 g r)) :=
  by induction r; reflexivity

  @[hott] def eq_hconcat_hdeg_square {A : Type _} {a a' : A} {p₁ p₂ p₃ : a = a'} (q₁ : p₁ = p₂)
    (q₂ : p₂ = p₃) : q₁ ⬝ph hdeg_square q₂ = hdeg_square (q₁ ⬝ q₂) :=
  by induction q₁; induction q₂; reflexivity

  @[hott] def hdeg_square_hconcat_eq {A : Type _} {a a' : A} {p₁ p₂ p₃ : a = a'} (q₁ : p₁ = p₂)
    (q₂ : p₂ = p₃) : hdeg_square q₁ ⬝hp q₂ = hdeg_square (q₁ ⬝ q₂) :=
  by induction q₁; induction q₂; reflexivity

  @[hott] def eq_hconcat_eq_hdeg_square {A : Type _} {a a' : A} {p₁ p₂ p₃ p₄ : a = a'} (q₁ : p₁ = p₂)
    (q₂ : p₂ = p₃) (q₃ : p₃ = p₄) : q₁ ⬝ph hdeg_square q₂ ⬝hp q₃ = hdeg_square (q₁ ⬝ q₂ ⬝ q₃) :=
  by induction q₃; apply eq_hconcat_hdeg_square

  -- @[hott] def vconcat_eq [unfold 11] {p : a₀₂ = a₂₂} (s₁₁ : square p₁₀ p₁₂ p₀₁ p₂₁) (r : p₁₂ = p) :
  --   square p₁₀ p p₀₁ p₂₁ :=
  -- by induction r; exact s₁₁

  -- @[hott] def eq_hconcat [unfold 11] {p : a₀₀ = a₀₂} (r : p = p₀₁)
  --   (s₁₁ : square p₁₀ p₁₂ p₀₁ p₂₁) : square p₁₀ p₁₂ p p₂₁ :=
  -- by induction r; exact s₁₁

  -- @[hott] def hconcat_eq [unfold 11] {p : a₂₀ = a₂₂}
  --   (s₁₁ : square p₁₀ p₁₂ p₀₁ p₂₁) (r : p₂₁ = p) : square p₁₀ p₁₂ p₀₁ p :=
  -- by induction r; exact s₁₁

  /- recursors for squares where some sides are reflexivity -/

  @[hott,elab_as_eliminator] def rec_on_b {a₀₀ : A}
    {P : Π{a₂₀ a₁₂ : A} {t : a₀₀ = a₂₀} {l : a₀₀ = a₁₂} {r : a₂₀ = a₁₂}, square t idp l r → Type _}
    {a₂₀ a₁₂ : A} {t : a₀₀ = a₂₀} {l : a₀₀ = a₁₂} {r : a₂₀ = a₁₂}
      (s : square t idp l r) (H : P ids) : P s :=
  have H2 : P (square_of_eq (eq_of_square s)),
    begin
      induction r, induction t,
      hgeneralize: eq_of_square s = es, dsimp at es, induction es,
      apply H
    end,
  left_inv (square_equiv_eq _ _ _ _).to_fun s ▸ H2

  @[hott, elab_as_eliminator] def rec_on_r {a₀₀ : A}
    {P : Π{a₀₂ a₂₁ : A} {t : a₀₀ = a₂₁} {b : a₀₂ = a₂₁} {l : a₀₀ = a₀₂}, square t b l idp → Type _}
    {a₀₂ a₂₁ : A} {t : a₀₀ = a₂₁} {b : a₀₂ = a₂₁} {l : a₀₀ = a₀₂}
      (s : square t b l idp) (H : P ids) : P s :=
  let p : l ⬝ b = t := (eq_of_square s)⁻¹ in
  have H2 : P (square_of_eq (eq_of_square s)⁻¹⁻¹),
    from @eq.rec_on _ _ (λx p, P (square_of_eq p⁻¹)) _ p (by induction b; induction l; exact H),
  have H3 : square_of_eq (eq_of_square s) = s,
    from left_inv (square_equiv_eq _ _ _ _).to_fun s,
  by rwra [inv_inv, H3] at H2

  @[hott, elab_as_eliminator] def rec_on_l {a₀₁ : A}
    {P : Π {a₂₀ a₂₂ : A} {t : a₀₁ = a₂₀} {b : a₀₁ = a₂₂} {r : a₂₀ = a₂₂},
      square t b idp r → Type _}
    {a₂₀ a₂₂ : A} {t : a₀₁ = a₂₀} {b : a₀₁ = a₂₂} {r : a₂₀ = a₂₂}
      (s : square t b idp r) (H : P ids) : P s :=
  let p : t ⬝ r = b := eq_of_square s ⬝ !idp_con in
  have H2 : P (square_of_eq (p ⬝ !idp_con⁻¹)),
    from eq.rec_on p (by induction r; induction t; exact H),
  have H3 : square_of_eq (eq_of_square s) = s,
    from left_inv (square_equiv_eq _ _ _ _).to_fun s,
  by rwra [con_inv_cancel_right, H3] at H2

  @[hott, elab_as_eliminator] def rec_on_t {a₁₀ : A}
    {P : Π {a₀₂ a₂₂ : A} {b : a₀₂ = a₂₂} {l : a₁₀ = a₀₂} {r : a₁₀ = a₂₂}, square idp b l r → Type _}
    {a₀₂ a₂₂ : A} {b : a₀₂ = a₂₂} {l : a₁₀ = a₀₂} {r : a₁₀ = a₂₂}
      (s : square idp b l r) (H : P ids) : P s :=
  let p : l ⬝ b = r := (eq_of_square s)⁻¹ ⬝ !idp_con in
  have H2 : P (square_of_eq ((p ⬝ !idp_con⁻¹)⁻¹)),
    from eq.rec_on p (by induction b; induction l; exact H),
  have H3 : P (square_of_eq ((eq_of_square s)⁻¹⁻¹)),
    by rwra con_inv_cancel_right at H2,
  have H4 : P (square_of_eq (eq_of_square s)),
    by hsimp at H3; apply H3,
  left_inv (square_equiv_eq _ _ _ _).to_fun s ▸ H4

  @[hott, elab_as_eliminator] def rec_on_tb {a : A}
    {P : Π{b : A} {l : a = b} {r : a = b}, square idp idp l r → Type _}
    {b : A} {l : a = b} {r : a = b}
      (s : square idp idp l r) (H : P ids) : P s :=
  have H2 : P (square_of_eq (eq_of_square s)),
    begin
      induction r,
      hgeneralize: eq_of_square s = es,
      dsimp at es, induction es,
      apply H,
    end,
  left_inv (square_equiv_eq _ _ _ _).to_fun s ▸ H2

  @[hott, elab_as_eliminator] def rec_on_lr {a : A}
    {P : Π{a' : A} {t : a = a'} {b : a = a'}, square t b idp idp → Type _}
    {a' : A} {t : a = a'} {b : a = a'}
      (s : square t b idp idp) (H : P ids) : P s :=
  let p : idp ⬝ b = t := (eq_of_square s)⁻¹ in
  have H2 : P (square_of_eq (eq_of_square s)⁻¹⁻¹),
    from @eq.rec_on _ _ (λx q, P (square_of_eq q⁻¹)) _ p (by induction b; exact H),
  have H3 : square_of_eq (eq_of_square s) = s,
    from left_inv (square_equiv_eq _ _ _ _).to_fun s,
  by rwra [inv_inv, H3] at H2

  --we can also do the other recursors (tl, tr, bl, br, tbl, tbr, tlr, blr), but let's postpone this until they are needed

  @[hott] def whisker_square (r₁₀ : p₁₀ = p₁₀') (r₁₂ : p₁₂ = p₁₂')
    (r₀₁ : p₀₁ = p₀₁') (r₂₁ : p₂₁ = p₂₁') (s : square p₁₀ p₁₂ p₀₁ p₂₁)
      : square p₁₀' p₁₂' p₀₁' p₂₁' :=
  by induction r₁₀; induction r₁₂; induction r₀₁; induction r₂₁; exact s

  /- squares commute with some operations on 2-paths -/

  @[hott] def square_inv2 {p₁ p₂ p₃ p₄ : a = a'}
    {t : p₁ = p₂} {b : p₃ = p₄} {l : p₁ = p₃} {r : p₂ = p₄} (s : square t b l r)
    : square (inverse2 t) (inverse2 b) (inverse2 l) (inverse2 r) :=
  by induction s;constructor

  @[hott] def square_con2 {p₁ p₂ p₃ p₄ : a₁ = a₂} {q₁ q₂ q₃ q₄ : a₂ = a₃}
    {t₁ : p₁ = p₂} {b₁ : p₃ = p₄} {l₁ : p₁ = p₃} {r₁ : p₂ = p₄}
    {t₂ : q₁ = q₂} {b₂ : q₃ = q₄} {l₂ : q₁ = q₃} {r₂ : q₂ = q₄}
    (s₁ : square t₁ b₁ l₁ r₁) (s₂ : square t₂ b₂ l₂ r₂)
      : square (t₁ ◾ t₂) (b₁ ◾ b₂) (l₁ ◾ l₂) (r₁ ◾ r₂) :=
  by induction s₂;induction s₁;constructor

  open is_trunc
  @[hott] def is_set.elims [H : is_set A] : square p₁₀ p₁₂ p₀₁ p₂₁ :=
  square_of_eq (is_set.elim _ _)

  @[hott, instance] def is_trunc_square (n : trunc_index) [H : is_trunc n .+2 A]
    : is_trunc n (square p₁₀ p₁₂ p₀₁ p₂₁) :=
  is_trunc_equiv_closed_rev n (square_equiv_eq _ _ _ _) (by apply_instance)

  -- @[hott] def square_of_con_inv_hsquare {p₁ p₂ p₃ p₄ : a₁ = a₂}
  --   {t : p₁ = p₂} {b : p₃ = p₄} {l : p₁ = p₃} {r : p₂ = p₄}
  --   (s : square (con_inv_eq_idp t) (con_inv_eq_idp b) (l ◾ r⁻²) idp)
  --     : square t b l r :=
  -- sorry --by induction s

  /- Square fillers -/
  -- TODO replace by "more algebraic" fillers?

  variables (p₁₀ p₁₂ p₀₁ p₂₁)
  @[hott] def square_fill_t : Σ (p : a₀₀ = a₂₀), square p p₁₂ p₀₁ p₂₁ :=
  by induction p₀₁; induction p₂₁; exact ⟨_, vrefl _⟩

  @[hott] def square_fill_b : Σ (p : a₀₂ = a₂₂), square p₁₀ p p₀₁ p₂₁ :=
  by induction p₀₁; induction p₂₁; exact ⟨_, vrefl _⟩

  @[hott] def square_fill_l : Σ (p : a₀₀ = a₀₂), square p₁₀ p₁₂ p p₂₁ :=
  by induction p₁₀; induction p₁₂; exact ⟨_, hrefl _⟩

  @[hott] def square_fill_r : Σ (p : a₂₀ = a₂₂) , square p₁₀ p₁₂ p₀₁ p :=
  by induction p₁₀; induction p₁₂; exact ⟨_, hrefl _⟩

  /- Squares having an 'ap' term on one face -/
  --TODO find better names
  @[hott] def square_Flr_ap_idp {c : B} {f : A → B} (p : Π a, f a = c)
    {a b : A} (q : a = b) : square (p a) (p b) (ap f q) idp  :=
  by induction q; apply vrfl

  @[hott] def square_Flr_idp_ap {c : B} {f : A → B} (p : Π a, c = f a)
    {a b : A} (q : a = b) : square (p a) (p b) idp (ap f q) :=
  by induction q; apply vrfl

  @[hott] def square_ap_idp_Flr {b : B} {f : A → B} (p : Π a, f a = b)
    {a b : A} (q : a = b) : square (ap f q) idp (p a) (p b) :=
  by induction q; apply hrfl

  /- Matching eq_hconcat with hconcat etc. -/
  -- TODO maybe rename hconcat_eq and the like?
  variable (s₁₁)
  @[hott] def ph_eq_pv_h_vp {p : a₀₀ = a₀₂} (r : p = p₀₁) :
    r ⬝ph s₁₁ =  !idp_con⁻¹ ⬝pv ((hdeg_square r) ⬝h s₁₁) ⬝vp !idp_con :=
  by induction r; induction s₁₁; refl

  @[hott] def hdeg_h_eq_pv_ph_vp {p : a₀₀ = a₀₂} (r : p = p₀₁) :
    hdeg_square r ⬝h s₁₁ = !idp_con ⬝pv (r ⬝ph s₁₁) ⬝vp !idp_con⁻¹ :=
  by induction r; induction s₁₁; refl

  @[hott] def hp_eq_h {p : a₂₀ = a₂₂} (r : p₂₁ = p) :
    s₁₁ ⬝hp r = s₁₁ ⬝h hdeg_square r :=
  by induction r; induction s₁₁; refl

  @[hott] def pv_eq_ph_vdeg_v_vh {p : a₀₀ = a₂₀} (r : p = p₁₀) :
    r ⬝pv s₁₁ = !idp_con⁻¹ ⬝ph ((vdeg_square r) ⬝v s₁₁) ⬝hp !idp_con :=
  by induction r; induction s₁₁; refl

  @[hott] def vdeg_v_eq_ph_pv_hp {p : a₀₀ = a₂₀} (r : p = p₁₀) :
    vdeg_square r ⬝v s₁₁ = !idp_con ⬝ph (r ⬝pv s₁₁) ⬝hp !idp_con⁻¹ :=
  by induction r; induction s₁₁; refl

  @[hott] def vp_eq_v {p : a₀₂ = a₂₂} (r : p₁₂ = p) :
    s₁₁ ⬝vp r = s₁₁ ⬝v vdeg_square r :=
  by induction r; induction s₁₁; refl

  @[hott] def natural_square {f g : A → B} (p : f ~ g) (q : a = a') :
    square (p a) (p a') (ap f q) (ap g q) :=
  square_of_pathover (apd p q)

  @[hott] def natural_square_tr {f g : A → B} (p : f ~ g) (q : a = a') :
    square (ap f q) (ap g q) (p a) (p a') :=
  transpose (natural_square p q)

  @[hott] def natural_square011 {A A' : Type _} {B : A → Type _}
    {a a' : A} {p : a = a'} {b : B a} {b' : B a'} (q : b =[p] b')
    {l r  : Π⦃a⦄, B a → A'} (g : Π⦃a⦄ (b : B a), l b = r b)
    : square (apd011 l p q) (apd011 r p q) (g b) (g b') :=
  begin
    induction q, exact hrfl
  end

  @[hott] def natural_square0111' {A A' : Type _} {B : A → Type _} (C : Π⦃a⦄, B a → Type _)
    {a a' : A} {p : a = a'} {b : B a} {b' : B a'} {q : b =[p] b'}
    {c : C b} {c' : C b'} (s : c =[apd011 C p q; id] c')
    {l r  : Π⦃a⦄ {b : B a}, C b → A'}
    (g : Π⦃a⦄ {b : B a} (c : C b), l c = r c)
    : square (apd0111 l p q s) (apd0111 r p q s) (g c) (g c') :=
  begin
    induction q, dsimp at s, apply idp_rec_on s, exact hrfl
  end

  -- this can be generalized a bit, by making the domain and codomain of k different, and also have
  -- a function at the RHS of s (similar to m)
  @[hott] def natural_square0111 {A A' : Type _} {B : A → Type _} (C : Π⦃a⦄, B a → Type _)
    {a a' : A} {p : a = a'} {b : B a} {b' : B a'} {q : b =[p] b'}
    {c : C b} {c' : C b'} (r : c =[apd011 C p q; id] c')
    {k : A → A} {l : Π⦃a⦄, B a → B (k a)} (m : Π⦃a⦄ {b : B a}, C b → C (l b))
    {f  : Π⦃a⦄ {b : B a}, C b → A'}
    (s : Π⦃a⦄ {b : B a} (c : C b), f (m c) = f c)
    : square (@apd0111 _ _ B _ _ _ _ _ _ _ (λa b (c : C b), f (m c)) p q r) (apd0111 f p q r) (s c) (s c') :=
  begin
    induction q, dsimp at r, apply idp_rec_on r, exact hrfl
  end

  /- some higher coherence conditions -/


  @[hott] theorem whisker_bl_whisker_tl_eq (p : a = a')
    : whisker_bl p (whisker_tl p ids) = con.right_inv p ⬝ph vrfl :=
  by induction p; reflexivity

  @[hott] theorem ap_is_constant_natural_square {g : B → C} {f : A → B} (H : Πa, g (f a) = c) (p : a = a') :
    (ap_is_constant H p)⁻¹ ⬝ph natural_square H p ⬝hp ap_constant p c =
      whisker_bl (H a') (whisker_tl (H a) ids) :=
  begin induction p, dsimp [ap_is_constant], rwr [inv_inv, whisker_bl_whisker_tl_eq] end

  @[hott] def inv_ph_eq_of_eq_ph {p : a₀₀ = a₀₂} {r : p₀₁ = p} {s₁₁ : square p₁₀ p₁₂ p₀₁ p₂₁}
    {s₁₁' : square p₁₀ p₁₂ p p₂₁} (t : s₁₁ = r ⬝ph s₁₁') : r⁻¹ ⬝ph s₁₁ = s₁₁' :=
  by induction r; exact t

  -- the following is used for torus.elim_surf
  @[hott] theorem whisker_square_aps_eq {f : A → B}
    {q₁₀ : f a₀₀ = f a₂₀} {q₀₁ : f a₀₀ = f a₀₂} {q₂₁ : f a₂₀ = f a₂₂} {q₁₂ : f a₀₂ = f a₂₂}
    {r₁₀ : ap f p₁₀ = q₁₀} {r₀₁ : ap f p₀₁ = q₀₁} {r₂₁ : ap f p₂₁ = q₂₁} {r₁₂ : ap f p₁₂ = q₁₂}
    {s₁₁ : p₁₀ ⬝ p₂₁ = p₀₁ ⬝ p₁₂} {t₁₁ : square q₁₀ q₁₂ q₀₁ q₂₁}
    (u : square (ap02 f s₁₁) (eq_of_square t₁₁)
                (ap_con f p₁₀ p₂₁ ⬝ (r₁₀ ◾ r₂₁)) (ap_con f p₀₁ p₁₂ ⬝ (r₀₁ ◾ r₁₂)))
    : whisker_square r₁₀ r₁₂ r₀₁ r₂₁ (aps f (square_of_eq s₁₁)) = t₁₁ :=
  begin
    induction r₁₀, induction r₀₁, induction r₁₂, induction r₂₁,
    induction p₁₂, induction p₁₀, induction p₂₁, dsimp at *, induction s₁₁, dsimp at *,
    dsimp [square_of_eq],
    apply eq_of_fn_eq_fn (square_equiv_eq _ _ _ _), dsimp,
    exact (eq_bot_of_square u)⁻¹
  end

  @[hott] def natural_square_eq {A B : Type _} {a a' : A} {f g : A → B} (p : f ~ g) (q : a = a')
    : natural_square p q = square_of_pathover (apd p q) :=
  idp

  @[hott] def eq_of_square_hrfl_hconcat_eq {A : Type _} {a a' : A} {p p' : a = a'} (q : p = p')
    : eq_of_square (hrfl ⬝hp q⁻¹) = !idp_con ⬝ q :=
  by induction q; induction p; reflexivity

  @[hott, hsimp] def aps_vrfl {A B : Type _} {a a' : A} (f : A → B) (p : a = a') :
    aps f (vrefl p) = vrefl (ap f p) :=
  by induction p; reflexivity

  @[hott, hsimp] def aps_hrfl {A B : Type _} {a a' : A} (f : A → B) (p : a = a') :
    aps f (hrefl p) = hrefl (ap f p) :=
  by induction p; reflexivity

  -- should the following two equalities be cubes?
  @[hott] def natural_square_ap_fn {A B C : Type _} {a a' : A} {g h : A → B} (f : B → C) (p : g ~ h)
    (q : a = a') : natural_square (λa, ap f (p a)) q =
      ap_compose f g q ⬝ph (aps f (natural_square p q) ⬝hp (ap_compose f h q)⁻¹) :=
  begin
    induction q, symmetry, exact (aps_vrfl _ _)
  end

  @[hott] def natural_square_compose {A B C : Type _} {a a' : A} {g g' : B → C}
    (p : g ~ g') (f : A → B) (q : a = a') : natural_square (λa, p (f a)) q =
    ap_compose g f q ⬝ph (natural_square p (ap f q) ⬝hp (ap_compose g' f q)⁻¹) :=
  by induction q; reflexivity

  @[hott] def natural_square_eq2 {A B : Type _} {a a' : A} {f f' : A → B} (p : f ~ f') {q q' : a = a'}
    (r : q = q') : natural_square p q = ap02 f r ⬝ph (natural_square p q' ⬝hp (ap02 f' r)⁻¹) :=
  by induction r; reflexivity

  @[hott, hsimp] def natural_square_refl {A B : Type _} {a a' : A} (f : A → B) (q : a = a')
    : natural_square (homotopy.refl f) q = hrfl :=
  by induction q; reflexivity

  @[hott] def aps_eq_hconcat {p₀₁'} (f : A → B) (q : p₀₁' = p₀₁) (s₁₁ : square p₁₀ p₁₂ p₀₁ p₂₁) :
    aps f (q ⬝ph s₁₁) = ap02 f q ⬝ph aps f s₁₁ :=
  by induction q; reflexivity

  @[hott] def aps_hconcat_eq {p₂₁'} (f : A → B) (s₁₁ : square p₁₀ p₁₂ p₀₁ p₂₁) (r : p₂₁' = p₂₁) :
    aps f (s₁₁ ⬝hp r⁻¹) = aps f s₁₁ ⬝hp (ap02 f r)⁻¹ :=
  by induction r; reflexivity

  @[hott] def aps_hconcat_eq' {p₂₁'} (f : A → B) (s₁₁ : square p₁₀ p₁₂ p₀₁ p₂₁) (r : p₂₁ = p₂₁') :
    aps f (s₁₁ ⬝hp r) = aps f s₁₁ ⬝hp ap02 f r :=
  by induction r; reflexivity

  @[hott] def aps_square_of_eq (f : A → B) (s : p₁₀ ⬝ p₂₁ = p₀₁ ⬝ p₁₂) :
    aps f (square_of_eq s) = square_of_eq ((ap_con f p₁₀ p₂₁)⁻¹ ⬝ ap02 f s ⬝ ap_con f p₀₁ p₁₂) :=
  by induction p₁₂; dsimp at *; induction s; induction p₂₁; induction p₁₀; reflexivity

  @[hott] def aps_eq_hconcat_eq {p₀₁' p₂₁'} (f : A → B) (q : p₀₁' = p₀₁) (s₁₁ : square p₁₀ p₁₂ p₀₁ p₂₁)
    (r : p₂₁' = p₂₁) : aps f (q ⬝ph s₁₁ ⬝hp r⁻¹) = ap02 f q ⬝ph aps f s₁₁ ⬝hp (ap02 f r)⁻¹ :=
  by induction q; induction r; reflexivity

end eq

end hott