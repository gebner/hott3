/-
Copyright (c) 2014 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Floris van Doorn

Partially ported from Coq HoTT
Theorems about path types (identity types)
-/
import hott.types.sigma

universes u v w
hott_theory

namespace hott

open eq hott.sigma equiv is_equiv is_trunc

namespace eq
  /- Path spaces -/
  section
  variables {A : Type u} {B : Type v} {a a₁ a₂ a₃ a₄ a' : A} {b b1 b2 : B} {f g : A → B} {h : B → A}
            {p p' p'' : a₁ = a₂}

  /- The path spaces of a path space are not, of course, determined; they are just the
      higher-dimensional structure of the original space. -/

  /- some lemmas about whiskering or other higher paths -/

  @[hott] def whisker_left_con_right (p : a₁ = a₂) {q q' q'' : a₂ = a₃} (r : q = q') (s : q' = q'')
    : whisker_left p (r ⬝ s) = whisker_left p r ⬝ whisker_left p s :=
  begin
    induction p, induction r, induction s, reflexivity
  end

  @[hott] def whisker_right_con_right (q : a₂ = a₃) (r : p = p') (s : p' = p'')
    : whisker_right q (r ⬝ s) = whisker_right q r ⬝ whisker_right q s :=
  begin
    induction q, induction r, induction s, reflexivity
  end

  @[hott] def whisker_left_con_left (p : a₁ = a₂) (p' : a₂ = a₃) {q q' : a₃ = a₄} (r : q = q')
    : whisker_left (p ⬝ p') r = con.assoc _ _ _ ⬝ whisker_left p (whisker_left p' r) ⬝ con.assoc' _ _ _ :=
  begin
    induction p', induction p, induction r, induction q, reflexivity
  end

  @[hott] def whisker_right_con_left {p p' : a₁ = a₂} (q : a₂ = a₃) (q' : a₃ = a₄) (r : p = p')
    : whisker_right (q ⬝ q') r = con.assoc' _ _ _ ⬝ whisker_right q' (whisker_right q r) ⬝ con.assoc _ _ _ :=
  begin
    induction q', induction q, induction r, induction p, reflexivity
  end

  @[hott] def whisker_left_inv_left (p : a₂ = a₁) {q q' : a₂ = a₃} (r : q = q')
    : (con_inv_cancel_left _ _).inverse ⬝ whisker_left p (whisker_left p⁻¹ r) ⬝ (con_inv_cancel_left _ _) = r :=
  begin
    induction p, induction r, induction q, reflexivity
  end

  @[hott] def whisker_left_inv (p : a₁ = a₂) {q q' : a₂ = a₃} (r : q = q')
    : whisker_left p r⁻¹ = (whisker_left p r)⁻¹ :=
  by induction r; reflexivity

  @[hott] def whisker_right_inv {p p' : a₁ = a₂} (q : a₂ = a₃) (r : p = p')
    : whisker_right q r⁻¹ = (whisker_right q r)⁻¹ :=
  by induction r; reflexivity

  @[hott] def ap_eq_apd10 {B : A → Type _} {f g : Πa, B a} (p : f = g) (a : A) :
    ap (λh : Π a, B a, h a) p = apd10 p a :=
  by induction p; reflexivity

  @[hott] def inverse2_right_inv (r : p = p') : r ◾ inverse2 r ⬝ con.right_inv p' = con.right_inv p :=
  by induction r;induction p;reflexivity

  @[hott] def inverse2_left_inv (r : p = p') : inverse2 r ◾ r ⬝ con.left_inv p' = con.left_inv p :=
  by induction r;induction p;reflexivity

  @[hott] def ap_con_right_inv (f : A → B) (p : a₁ = a₂)
    : ap_con f p p⁻¹ ⬝ whisker_left _ (ap_inv f p) ⬝ con.right_inv (ap f p)
      = ap (ap f) (con.right_inv p) :=
  by induction p;reflexivity

  @[hott] def ap_con_left_inv (f : A → B) (p : a₁ = a₂)
    : ap_con f p⁻¹ p ⬝ whisker_right _ (ap_inv f p) ⬝ con.left_inv (ap f p)
      = ap (ap f) (con.left_inv p) :=
  by induction p;reflexivity

  @[hott] def idp_con_whisker_left {q q' : a₂ = a₃} (r : q = q') :
  (idp_con _).inverse ⬝ whisker_left idp r = r ⬝ (idp_con _).inverse :=
  by induction r;induction q;reflexivity

  @[hott] def whisker_left_idp_con {q q' : a₂ = a₃} (r : q = q') :
  whisker_left idp r ⬝ !idp_con = !idp_con ⬝ r :=
  by induction r;induction q;reflexivity

  @[hott] def eq.cases_helper {A : Type u} {a b : A} (x : a = b) (C : Sort v) :
    (∀ b' : A, ∀ x' : a = b', ∀ hb : b = b', ∀ hx : x =[hb] x', C) → C :=
  by induction x; intro h; apply h; refl

  @[hott] def idp_con_idp {p : a = a} (q : p = idp) : idp_con p ⬝ q = ap (λp, idp ⬝ p) q :=
  by eq_cases q; refl

  @[hott] def ap_is_constant {A B : Type _} {f : A → B} {b : B} (p : Πx, f x = b)
    {x y : A} (q : x = y) : ap f q = p x ⬝ (p y)⁻¹ :=
  by induction q; symmetry; apply con.right_inv

  @[hott] def inv2_inv {p q : a = a'} (r : p = q) : inverse2 r⁻¹ = (inverse2 r)⁻¹ :=
  by induction r;reflexivity

  @[hott] def inv2_con {p p' p'' : a = a'} (r : p = p') (r' : p' = p'')
    : inverse2 (r ⬝ r') = inverse2 r ⬝ inverse2 r' :=
  by induction r';induction r;reflexivity

  @[hott] def con2_inv {p₁ q₁ : a₁ = a₂} {p₂ q₂ : a₂ = a₃} (r₁ : p₁ = q₁) (r₂ : p₂ = q₂)
    : (r₁ ◾ r₂)⁻¹ = r₁⁻¹ ◾ r₂⁻¹ :=
  by induction r₁;induction r₂;reflexivity

  @[hott] def eq_con_inv_of_con_eq_whisker_left {A : Type _} {a a₂ a₃ : A}
    {p : a = a₂} {q q' : a₂ = a₃} {r : a = a₃} (s' : q = q') (s : p ⬝ q' = r) :
    eq_con_inv_of_con_eq (whisker_left p s' ⬝ s)
      = eq_con_inv_of_con_eq s ⬝ whisker_left r (inverse2 s')⁻¹ :=
  by induction s';induction q;induction s;reflexivity

  @[hott] def right_inv_eq_idp {A : Type _} {a : A} {p : a = a} (r : p = idpath a) :
    con.right_inv p = r ◾ inverse2 r :=
  by eq_cases r; reflexivity

  /- Transporting in path spaces.

     There are potentially a lot of these lemmas, so we adopt a uniform naming scheme:

     - `l` means the left endpoint varies
     - `r` means the right endpoint varies
     - `F` means application of a function to that (varying) endpoint.
  -/

  @[hott] def eq_transport_l (p : a₁ = a₂) (q : a₁ = a₃)
    : transport (λx, x = a₃) p q = p⁻¹ ⬝ q :=
  by induction p; exact !idp_con⁻¹

  @[hott] def eq_transport_r (p : a₂ = a₃) (q : a₁ = a₂)
    : transport (λx, a₁ = x) p q = q ⬝ p :=
  by induction p; reflexivity

  @[hott] def eq_transport_lr (p : a₁ = a₂) (q : a₁ = a₁)
    : transport (λx, x = x) p q = p⁻¹ ⬝ q ⬝ p :=
  by induction p; exact !idp_con⁻¹

  @[hott] def eq_transport_Fl (p : a₁ = a₂) (q : f a₁ = b)
    : transport (λx, f x = b) p q = (ap f p)⁻¹ ⬝ q :=
  by induction p; exact !idp_con⁻¹

  @[hott] def eq_transport_Fr (p : a₁ = a₂) (q : b = f a₁)
    : transport (λx, b = f x) p q = q ⬝ (ap f p) :=
  by induction p; reflexivity

  @[hott] def eq_transport_FlFr (p : a₁ = a₂) (q : f a₁ = g a₁)
    : transport (λx, f x = g x) p q = (ap f p)⁻¹ ⬝ q ⬝ (ap g p) :=
  by induction p; exact !idp_con⁻¹

  @[hott] def eq_transport_FlFr_D {B : A → Type _} {f g : Πa, B a}
    (p : a₁ = a₂) (q : f a₁ = g a₁)
      : transport (λx, f x = g x) p q = (apdt f p)⁻¹ ⬝ ap (transport B p) q ⬝ (apdt g p) :=
  by eq_cases p; dsimp; hsimp

  @[hott] def eq_transport_FFlr (p : a₁ = a₂) (q : h (f a₁) = a₁)
    : transport (λx, h (f x) = x) p q = (ap h (ap f p))⁻¹ ⬝ q ⬝ p :=
  by induction p; exact !idp_con⁻¹

  @[hott] def eq_transport_lFFr (p : a₁ = a₂) (q : a₁ = h (f a₁))
    : transport (λx, x = h (f x)) p q = p⁻¹ ⬝ q ⬝ (ap h (ap f p)) :=
  by induction p; exact !idp_con⁻¹

  /- Pathovers -/

  -- In the comment we give the fibration of the pathover

  -- we should probably try to do everything just with pathover_eq (defined in cubical.square),

  @[hott] def eq_pathover_l (p : a₁ = a₂) (q : a₁ = a₃) : q =[p; λ x, x = a₃] p⁻¹ ⬝ q :=
  by induction p; induction q; exact idpo

  @[hott] def eq_pathover_r (p : a₂ = a₃) (q : a₁ = a₂) : q =[p; λ x, a₁ = x] q ⬝ p :=
  by induction p; induction q; exact idpo

  @[hott] def eq_pathover_lr (p : a₁ = a₂) (q : a₁ = a₁) : q =[p; λ x, x = x] p⁻¹ ⬝ q ⬝ p :=
  by induction p; dsimp [inverse]; rwr [idp_con]; exact idpo

  @[hott] def eq_pathover_Fl (p : a₁ = a₂) (q : f a₁ = b) : q =[p; λ x, f x = b] (ap f p)⁻¹ ⬝ q :=
  by induction p; induction q; exact idpo

  @[hott] def eq_pathover_Fl' (p : a₁ = a₂) (q : f a₂ = b) : (ap f p) ⬝ q =[p; λ x, f x = b] q :=
  by induction p; induction q; exact idpo

  @[hott] def eq_pathover_Fr (p : a₁ = a₂) (q : b = f a₁) : q =[p; λ x, b = f x] q ⬝ (ap f p) :=
  by induction p; exact idpo

  @[hott] def eq_pathover_FlFr (p : a₁ = a₂) (q : f a₁ = g a₁) : q =[p; λ x, f x = g x] (ap f p)⁻¹ ⬝ q ⬝ (ap g p) :=
  by induction p; hsimp

  @[hott] def eq_pathover_FlFr_D {B : A → Type _} {f g : Πa, B a} (p : a₁ = a₂) (q : f a₁ = g a₁)
    : q =[p; λ x, f x = g x] (apdt f p)⁻¹ ⬝ ap (transport B p) q ⬝ (apdt g p) :=
  by induction p; dsimp; hsimp

  @[hott] def eq_pathover_FFlr (p : a₁ = a₂) (q : h (f a₁) = a₁) : q =[p; λ x, h (f x) = x] (ap h (ap f p))⁻¹ ⬝ q ⬝ p :=
  by induction p; hsimp

  @[hott] def eq_pathover_lFFr (p : a₁ = a₂) (q : a₁ = h (f a₁)) : q =[p; λ x, x = h (f x)] p⁻¹ ⬝ q ⬝ (ap h (ap f p)) :=
  by induction p; hsimp

  @[hott] def eq_pathover_r_idp (p : a₁ = a₂) : idp =[p; λ x, a₁ = x] p :=
  by induction p; exact idpo

  @[hott] def eq_pathover_l_idp (p : a₁ = a₂) : idp =[p; λ x, x = a₁] p⁻¹ :=
  by induction p; exact idpo

  @[hott] def eq_pathover_l_idp' (p : a₁ = a₂) : idp =[p⁻¹; λ x, x = a₂] p :=
  by induction p; exact idpo

  -- The Functorial action of paths is [ap].

  /- Equivalences between path spaces -/

  /- [is_equiv_ap] is in init.equiv  -/

  @[hott] def equiv_ap (f : A → B) [H : is_equiv f] (a₁ a₂ : A)
    : (a₁ = a₂) ≃ (f a₁ = f a₂) :=
  equiv.mk (ap f) (by apply_instance)

  /- Path operations are equivalences -/

  @[hott, instance] def is_equiv_eq_inverse (a₁ a₂ : A)
    : is_equiv (inverse : a₁ = a₂ → a₂ = a₁) :=
  is_equiv.mk inverse inverse inv_inv inv_inv (λp, by induction p; refl)

  @[hott] def eq_equiv_eq_symm (a₁ a₂ : A) : (a₁ = a₂) ≃ (a₂ = a₁) :=
  equiv.mk inverse (by apply_instance)

  @[hott, instance] def is_equiv_concat_left (p : a₁ = a₂) (a₃ : A)
    : is_equiv (concat p : a₂ = a₃ → a₁ = a₃) :=
  is_equiv.mk (concat p) (concat p⁻¹)
              (con_inv_cancel_left p)
              (inv_con_cancel_left p)
              begin abstract { intro q, induction p;induction q;reflexivity } end

  @[hott] def equiv_eq_closed_left (a₃ : A) (p : a₁ = a₂) : (a₁ = a₃) ≃ (a₂ = a₃) :=
  equiv.mk (concat p⁻¹) (by apply_instance)

  @[hott, instance] def is_equiv_concat_right (p : a₂ = a₃) (a₁ : A)
    : is_equiv (λq : a₁ = a₂, q ⬝ p) :=
  is_equiv.mk (λq, q ⬝ p) (λq, q ⬝ p⁻¹)
              (λq, inv_con_cancel_right q p)
              (λq, con_inv_cancel_right q p)
              (λq, by induction p;induction q;reflexivity)

  @[hott] def equiv_eq_closed_right (a₁ : A) (p : a₂ = a₃) : (a₁ = a₂) ≃ (a₁ = a₃) :=
  equiv.mk (λq, q ⬝ p) (by apply_instance)

  @[hott] def eq_equiv_eq_closed (p : a₁ = a₂) (q : a₃ = a₄) : (a₁ = a₃) ≃ (a₂ = a₄) :=
  equiv.trans (equiv_eq_closed_left a₃ p) (equiv_eq_closed_right a₂ q)

  @[hott] def loop_equiv_eq_closed {A : Type _} {a a' : A} (p : a = a')
    : (a = a) ≃ (a' = a') :=
  eq_equiv_eq_closed p p

  @[hott] def is_equiv_whisker_left (p : a₁ = a₂) (q r : a₂ = a₃)
  : is_equiv (whisker_left p : q = r → p ⬝ q = p ⬝ r) :=
  begin
  fapply adjointify,
    {intro s, apply cancel_left _ s},
    {intro s,
      apply concat, {apply whisker_left_con_right},
      apply concat, tactic.swap, apply (whisker_left_inv_left p s),
      apply concat2,
        {apply concat, {apply whisker_left_con_right},
          apply concat2,
            {induction p, induction q, reflexivity},
            {reflexivity}},
        {induction p, induction r, reflexivity}},
    {intro s, induction s, induction q, induction p, reflexivity}
  end

  @[hott] def eq_equiv_con_eq_con_left (p : a₁ = a₂) (q r : a₂ = a₃)
    : (q = r) ≃ (p ⬝ q = p ⬝ r) :=
  equiv.mk _ (is_equiv_whisker_left _ _ _)

  @[hott] def is_equiv_whisker_right {p q : a₁ = a₂} (r : a₂ = a₃)
    : is_equiv (λs, whisker_right r s : p = q → p ⬝ r = q ⬝ r) :=
  begin
  fapply adjointify,
    {intro s, apply cancel_right _ s},
    {intro s, induction r, eq_cases s, induction q, dsimp at *, induction hb, rwr eq_of_pathover_idp hx},
    {intro s, induction s, induction r, induction p, reflexivity}
  end

  @[hott] def eq_equiv_con_eq_con_right (p q : a₁ = a₂) (r : a₂ = a₃)
    : (p = q) ≃ (p ⬝ r = q ⬝ r) :=
  equiv.mk _ (is_equiv_whisker_right _)

  local attribute [hsimp] con.assoc

  /-
    The following proofs can be simplified a bit by concatenating previous equivalences.
    However, these proofs have the advantage that the inverse is definitionally equal to
    what we would expect
  -/
  @[hott] def is_equiv_con_eq_of_eq_inv_con (p : a₁ = a₃) (q : a₂ = a₃) (r : a₂ = a₁)
    : is_equiv (con_eq_of_eq_inv_con : p = r⁻¹ ⬝ q → r ⬝ p = q) :=
  begin
    fapply adjointify,
    { apply eq_inv_con_of_con_eq},
    { intro s, induction r, dsimp [con_eq_of_eq_inv_con,eq_inv_con_of_con_eq], hsimp },
    { intro s, induction r, dsimp [con_eq_of_eq_inv_con,eq_inv_con_of_con_eq], hsimp },
  end

  @[hott] def eq_inv_con_equiv_con_eq (p : a₁ = a₃) (q : a₂ = a₃) (r : a₂ = a₁)
    : (p = r⁻¹ ⬝ q) ≃ (r ⬝ p = q) :=
  equiv.mk _ (is_equiv_con_eq_of_eq_inv_con _ _ _)

  @[hott] def is_equiv_con_eq_of_eq_con_inv (p : a₁ = a₃) (q : a₂ = a₃) (r : a₂ = a₁)
    : is_equiv (con_eq_of_eq_con_inv : r = q ⬝ p⁻¹ → r ⬝ p = q) :=
  begin
    fapply adjointify,
    { apply eq_con_inv_of_con_eq},
    { intro s, induction p, refl },
    { intro s, induction p, refl },
  end

  @[hott] def eq_con_inv_equiv_con_eq (p : a₁ = a₃) (q : a₂ = a₃) (r : a₂ = a₁)
    : (r = q ⬝ p⁻¹) ≃ (r ⬝ p = q) :=
  equiv.mk _ (is_equiv_con_eq_of_eq_con_inv _ _ _)

  @[hott] def is_equiv_inv_con_eq_of_eq_con (p : a₁ = a₃) (q : a₂ = a₃) (r : a₁ = a₂)
    : is_equiv (inv_con_eq_of_eq_con : p = r ⬝ q → r⁻¹ ⬝ p = q) :=
  begin
    fapply adjointify,
    { apply eq_con_of_inv_con_eq},
    { intro s, induction r, dsimp [inv_con_eq_of_eq_con,eq_con_of_inv_con_eq], hsimp },
    { intro s, induction r, dsimp [inv_con_eq_of_eq_con,eq_con_of_inv_con_eq], hsimp },
  end

  @[hott] def eq_con_equiv_inv_con_eq (p : a₁ = a₃) (q : a₂ = a₃) (r : a₁ = a₂)
    : (p = r ⬝ q) ≃ (r⁻¹ ⬝ p = q) :=
  equiv.mk _ (is_equiv_inv_con_eq_of_eq_con _ _ _)

  @[hott] def is_equiv_con_inv_eq_of_eq_con (p : a₃ = a₁) (q : a₂ = a₃) (r : a₂ = a₁)
    : is_equiv (con_inv_eq_of_eq_con : r = q ⬝ p → r ⬝ p⁻¹ = q) :=
  begin
    fapply adjointify,
    { apply eq_con_of_con_inv_eq},
    { intro s, induction p, refl },
    { intro s, induction p, refl },
  end

  @[hott] def eq_con_equiv_con_inv_eq (p : a₃ = a₁) (q : a₂ = a₃) (r : a₂ = a₁)
    : (r = q ⬝ p) ≃ (r ⬝ p⁻¹ = q) :=
   equiv.mk _ (is_equiv_con_inv_eq_of_eq_con _ _ _)

  local attribute [instance]
                  is_equiv_inv_con_eq_of_eq_con
                  is_equiv_con_inv_eq_of_eq_con
                  is_equiv_con_eq_of_eq_con_inv
                  is_equiv_con_eq_of_eq_inv_con

  @[hott] def is_equiv_eq_con_of_inv_con_eq (p : a₁ = a₃) (q : a₂ = a₃) (r : a₂ = a₁)
    : is_equiv (eq_con_of_inv_con_eq : r⁻¹ ⬝ q = p → q = r ⬝ p) :=
  is_equiv_inv (@inv_con_eq_of_eq_con _ _ _ _ q p r)

  @[hott] def is_equiv_eq_con_of_con_inv_eq (p : a₁ = a₃) (q : a₂ = a₃) (r : a₂ = a₁)
    : is_equiv (eq_con_of_con_inv_eq : q ⬝ p⁻¹ = r → q = r ⬝ p) :=
  is_equiv_inv (@con_inv_eq_of_eq_con _ _ _ _ p r q)

  @[hott] def is_equiv_eq_con_inv_of_con_eq (p : a₁ = a₃) (q : a₂ = a₃) (r : a₂ = a₁)
    : is_equiv (eq_con_inv_of_con_eq : r ⬝ p = q → r = q ⬝ p⁻¹) :=
  is_equiv_inv (@con_eq_of_eq_con_inv _ _ _ _ p q r)

  @[hott] def is_equiv_eq_inv_con_of_con_eq (p : a₁ = a₃) (q : a₂ = a₃) (r : a₂ = a₁)
    : is_equiv (eq_inv_con_of_con_eq : r ⬝ p = q → p = r⁻¹ ⬝ q) :=
  is_equiv_inv (@con_eq_of_eq_inv_con _ _ _ _ p q r)

  @[hott] def is_equiv_con_inv_eq_idp (p q : a₁ = a₂)
    : is_equiv (con_inv_eq_idp : p = q → p ⬝ q⁻¹ = idp) :=
  begin
    fapply adjointify,
    { apply eq_of_con_inv_eq_idp},
    { intro s, induction q, dsimp [con_inv_eq_idp, eq_of_con_inv_eq_idp] at *, eq_cases s, reflexivity},
    { intro s, induction s, induction p, reflexivity},
  end

  @[hott] def is_equiv_inv_con_eq_idp (p q : a₁ = a₂)
    : is_equiv (inv_con_eq_idp : p = q → q⁻¹ ⬝ p = idp) :=
  begin
    fapply adjointify,
    { apply eq_of_inv_con_eq_idp},
    { intro s, induction q,
      apply is_equiv_rect (eq_equiv_con_eq_con_left idp p idp).to_fun _ _ s; intro s',
      eq_cases s', refl },
    { intro s, induction s, induction p, reflexivity},
  end

  @[hott] def eq_equiv_con_inv_eq_idp (p q : a₁ = a₂) : (p = q) ≃ (p ⬝ q⁻¹ = idp) :=
  equiv.mk _ (is_equiv_con_inv_eq_idp _ _)

  @[hott] def eq_equiv_inv_con_eq_idp (p q : a₁ = a₂) : (p = q) ≃ (q⁻¹ ⬝ p = idp) :=
  equiv.mk _ (is_equiv_inv_con_eq_idp _ _)

  /- Pathover Equivalences -/

  @[hott] def eq_pathover_equiv_l (p : a₁ = a₂) (q : a₁ = a₃) (r : a₂ = a₃) : q =[p; λ x, x = a₃] r ≃ q = p ⬝ r :=
  by induction p; exact pathover_idp _ _ ⬝e equiv_eq_closed_right _ !idp_con.inverse

  @[hott] def eq_pathover_equiv_r (p : a₂ = a₃) (q : a₁ = a₂) (r : a₁ = a₃) : q =[p; λ x, a₁ = x] r ≃ q ⬝ p = r :=
  by induction p; apply pathover_idp

  @[hott] def eq_pathover_equiv_lr (p : a₁ = a₂) (q : a₁ = a₁) (r : a₂ = a₂)
    : q =[p; λ x, x = x] r ≃ q ⬝ p = p ⬝ r :=
  by induction p; exact pathover_idp _ _ ⬝e equiv_eq_closed_right _ !idp_con.inverse

  @[hott] def eq_pathover_equiv_Fl (p : a₁ = a₂) (q : f a₁ = b) (r : f a₂ = b)
    : q =[p; λ x, f x = b] r ≃ q = ap f p ⬝ r :=
  by induction p; exact pathover_idp _ _ ⬝e equiv_eq_closed_right _ !idp_con⁻¹

  @[hott] def eq_pathover_equiv_Fr (p : a₁ = a₂) (q : b = f a₁) (r : b = f a₂)
    : q =[p; λ x, b = f x] r ≃ q ⬝ ap f p = r :=
  by induction p; apply pathover_idp

  @[hott] def eq_pathover_equiv_FlFr (p : a₁ = a₂) (q : f a₁ = g a₁) (r : f a₂ = g a₂)
    : q =[p; λ x, f x = g x] r ≃ q ⬝ ap g p = ap f p ⬝ r :=
  by induction p; exact pathover_idp _ _ ⬝e equiv_eq_closed_right _ !idp_con⁻¹

  @[hott] def eq_pathover_equiv_FFlr (p : a₁ = a₂) (q : h (f a₁) = a₁) (r : h (f a₂) = a₂)
    : q =[p; λ x, h (f x) = x] r ≃ q ⬝ p = ap h (ap f p) ⬝ r :=
  by induction p; exact pathover_idp _ _ ⬝e equiv_eq_closed_right _ !idp_con⁻¹

  @[hott] def eq_pathover_equiv_lFFr (p : a₁ = a₂) (q : a₁ = h (f a₁)) (r : a₂ = h (f a₂))
    : q =[p; λ x, x = h (f x)] r ≃ q ⬝ ap h (ap f p) = p ⬝ r :=
  by induction p; exact pathover_idp _ _ ⬝e equiv_eq_closed_right _ !idp_con⁻¹

  -- a lot of this library still needs to be ported from Coq HoTT

  -- the behavior of equality in other types is described in the corresponding type files

  -- encode decode method

  open is_trunc
  @[hott] def encode_decode_method' (a₀ a : A) (code : A → Type _) (c₀ : code a₀)
    (decode : Π(a : A) (c : code a), a₀ = a)
    (encode_decode : Π(a : A) (c : code a), c₀ =[decode a c] c)
    (decode_encode : decode a₀ c₀ = idp) : (a₀ = a) ≃ code a :=
  begin
    fapply equiv.MK,
    { intro p, exact p ▸ c₀},
    { apply decode},
    { intro c, apply tr_eq_of_pathover, apply encode_decode},
    { intro p, induction p, apply decode_encode},
  end

  end

  section
    parameters {A : Type _} (a₀ : A) (code : A → Type _) (H : is_contr (Σa, code a))
      (p : (center (Σa, code a)).1 = a₀)
    include p
    @[hott] protected def encode {a : A} (q : a₀ = a) : code a :=
    (p ⬝ q) ▸ (center (Σa, code a)).2

    @[hott] protected def decode' {a : A} (c : code a) : a₀ = a :=
    (@is_prop.elim (Σ a, code a) _ ⟨a₀, encode idp⟩ ⟨a, c⟩)..1

    @[hott] protected def decode {a : A} (c : code a) : a₀ = a :=
    (decode' (encode idp))⁻¹ ⬝ decode' c

    @[hott] def total_space_method (a : A) : (a₀ = a) ≃ code a :=
    begin
      fapply equiv.MK,
      { exact hott.eq.encode},
      { exact hott.eq.decode},
      { intro c, induction p, apply tr_eq_of_pathover,
        dsimp [eq.decode, eq.decode', eq.encode, eq_pr1], rwr [idp_con, is_prop_elim_self],
        dsimp, rwr idp_con,
        refine @sigma.rec_on _ _
          (λx, x.2 =[((@is_prop.elim (Σ a, code a) _ ⟨x.1, x.2⟩ ⟨a, c⟩)..1: _); code] c)
          (center (sigma code)) _,
        intros a c, apply eq_pr2},
      { intro q, induction q, dsimp [eq.encode], apply con.left_inv, },
    end
  end

  @[hott] def encode_decode_method {A : Type _} (a₀ a : A) (code : A → Type _) (c₀ : code a₀)
    (decode : Π(a : A) (c : code a), a₀ = a)
    (encode_decode : Π(a : A) (c : code a), c₀ =[decode a c] c) : (a₀ = a) ≃ code a :=
  begin
    fapply total_space_method,
    { fapply @is_contr.mk,
      { exact ⟨a₀, c₀⟩},
      { intro p, fapply sigma_eq,
          apply decode, exact p.2,
        apply encode_decode}},
    { reflexivity}
  end

end eq

end hott