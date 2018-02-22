/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Floris van Doorn

Theorems about 2-dimensional paths
-/

import .cubical.square
universes u v w
hott_theory

namespace hott
open function hott.is_equiv hott.equiv

namespace eq
  variables {A : Type _} {B : Type _} {C : Type _} {f : A → B} {a a' a₁ a₂ a₃ a₄ : A} {b b' : B}

  @[hott] theorem ap_is_constant_eq (p : Πx, f x = b) (q : a = a') :
      ap_is_constant f p q =
      eq_con_inv_of_con_eq ((eq_of_square (square_of_pathover (apd p q)))⁻¹ ⬝
      whisker_left (p a) (ap_constant q b)) :=
  begin
    induction q, dsimp [ap_constant, ap_is_constant, apd], 
    hinduction p a, refl
  end

  @[hott] def ap_inv2 {p q : a = a'} (r : p = q)
    : square (ap (ap f) (inverse2 r))
             (inverse2 (ap (ap f) r))
             (ap_inv f p)
             (ap_inv f q) :=
  by induction r;exact hrfl

  @[hott] def ap_con2 {p₁ q₁ : a₁ = a₂} {p₂ q₂ : a₂ = a₃} (r₁ : p₁ = q₁) (r₂ : p₂ = q₂)
    : square (ap (ap f) (r₁ ◾ r₂))
             (ap (ap f) r₁ ◾ ap (ap f) r₂)
             (ap_con f p₁ p₂)
             (ap_con f q₁ q₂) :=
  by induction r₂;induction r₁;exact hrfl

  @[hott] theorem ap_con_right_inv_sq {A B : Type _} {a1 a2 : A} (f : A → B) (p : a1 = a2) :
    square (ap (ap f) (con.right_inv p))
           (con.right_inv (ap f p))
           (ap_con f p p⁻¹ ⬝ whisker_left _ (ap_inv f p))
           idp :=
  by cases p;apply hrefl

  @[hott] theorem ap_con_left_inv_sq {A B : Type _} {a1 a2 : A} (f : A → B) (p : a1 = a2) :
    square (ap (ap f) (con.left_inv p))
           (con.left_inv (ap f p))
           (ap_con f p⁻¹ p ⬝ whisker_right _ (ap_inv f p))
           idp :=
  by cases p;apply vrefl

  @[hott] def ap02_compose {A B C : Type _} (g : B → C) (f : A → B) {a a' : A}
    {p₁ p₂ : a = a'} (q : p₁ = p₂) :
    square (ap_compose g f p₁) (ap_compose g f p₂) (ap02 (g ∘ f) q) (ap02 g (ap02 f q)) :=
  by induction q; exact vrfl

  @[hott] def ap02_id {A : Type _} {a a' : A}
    {p₁ p₂ : a = a'} (q : p₁ = p₂) :
    square (ap_id p₁) (ap_id p₂) (ap02 id q) q :=
  by induction q; exact vrfl

  @[hott] theorem ap_ap_is_constant {A B C : Type _} (g : B → C) {f : A → B} {b : B}
    (p : Πx, f x = b) {x y : A} (q : x = y) :
    square (ap (ap g) (ap_is_constant f p q))
           (by exact (ap_is_constant (g ∘ f) (λa, ap g (p a)) q))
           (ap_compose g f q)⁻¹
           (ap_con _ _ _ ⬝ whisker_left _ (ap_inv _ _)) :=
  begin
    induction q, dsimp [ap_is_constant], hinduction (p x), apply ids
  end

  @[hott] theorem ap_ap_compose {A B C D : Type _} (h : C → D) (g : B → C) (f : A → B)
    {x y : A} (p : x = y) :
    square (ap_compose (h ∘ g) f p)
           (ap (ap h) (ap_compose g f p))
           (ap_compose h (g ∘ f) p)
           (ap_compose h g (ap f p)) :=
  by induction p; exact ids

  @[hott] def ap_compose_inv {A B C : Type _} (g : B → C) (f : A → B)
    {x y : A} (p : x = y) :
    square (ap_compose g f p⁻¹)
           (inverse2 (ap_compose g f p) ⬝ (ap_inv g (ap f p))⁻¹)
           (ap_inv (g ∘ f) p)
           (ap (ap g) (ap_inv f p)) :=
  by induction p; exact ids

  @[hott] def ap_compose_con (g : B → C) (f : A → B) (p : a₁ = a₂) (q : a₂ = a₃) :
    square (ap_compose g f (p ⬝ q))
           (ap_compose g f p ◾ ap_compose g f q ⬝ (ap_con g (ap f p) (ap f q))⁻¹)
           (ap_con (g ∘ f) p q)
           (ap (ap g) (ap_con f p q)) :=
  by induction q; induction p; exact ids

  @[hott] theorem ap_compose_natural {A B C : Type _} (g : B → C) (f : A → B)
    {x y : A} {p q : x = y} (r : p = q) :
    square (ap (ap (g ∘ f)) r)
           (ap (ap g ∘ ap f) r)
           (ap_compose g f p)
           (ap_compose g f q) :=
  natural_square_tr (ap_compose g f) r

  @[hott] theorem whisker_right_eq_of_con_inv_eq_idp {p q : a₁ = a₂} (r : p ⬝ q⁻¹ = idp) :
    whisker_right q⁻¹ (eq_of_con_inv_eq_idp r) ⬝ con.right_inv q = r :=
  by induction q; cases r; reflexivity

  @[hott] theorem ap_eq_of_con_inv_eq_idp (f : A → B) {p q : a₁ = a₂} (r : p ⬝ q⁻¹ = idp)
  : ap02 f (eq_of_con_inv_eq_idp r) =
           eq_of_con_inv_eq_idp (whisker_left _ (ap_inv _ _)⁻¹ ⬝ (ap_con _ _ _)⁻¹ ⬝ ap02 f r)
            :=
  by induction q; cases r; reflexivity

  @[hott] theorem eq_of_con_inv_eq_idp_con2 {p p' q q' : a₁ = a₂} (r : p = p') (s : q = q')
    (t : p' ⬝ q'⁻¹ = idp)
  : eq_of_con_inv_eq_idp (r ◾ inverse2 s ⬝ t) = r ⬝ eq_of_con_inv_eq_idp t ⬝ s⁻¹ :=
  by induction s; induction r; induction q; reflexivity

  @[hott] def naturality_apd_eq {A : Type _} {B : A → Type _} {a a₂ : A} {f g : Πa, B a}
    (H : f ~ g) (p : a = a₂)
    : apd f p = concato_eq (eq_concato (H a) (apd g p)) (H a₂)⁻¹ :=
  begin
    induction p, dsimp, 
    hgeneralize : H a = p, revert p,
    hgeneralize : g a = x, intro p, 
    induction p,
    reflexivity
  end

  @[hott] theorem con_tr_idp {P : A → Type _} {x y : A} (q : x = y) (u : P x) :
    con_tr idp q u = ap (λp, p ▸ u) (idp_con q) :=
  by induction q;reflexivity

  @[hott] def whisker_left_idp_con_eq_assoc
    {A : Type _} {a₁ a₂ a₃ : A} (p : a₁ = a₂) (q : a₂ = a₃)
    : whisker_left p (idp_con q)⁻¹ = con.assoc p idp q :=
  by induction q; reflexivity

  @[hott] def whisker_left_inverse2 {A : Type _} {a : A} {p : a = a} (q : p = idp)
    : whisker_left p q⁻² ⬝ q = con.right_inv p :=
  by cases q; reflexivity

  @[hott] def cast_fn_cast_square {A : Type _} {B C : A → Type _} (f : Π⦃a⦄, B a → C a) {a₁ a₂ : A}
    (p : a₁ = a₂) (q : a₂ = a₁) (r : p ⬝ q = idp) (b : B a₁) :
    cast (ap C q) (f (cast (ap B p) b)) = f b :=
  have q⁻¹ = p, from inv_eq_of_idp_eq_con r⁻¹,
  begin induction this, induction q, reflexivity end

  @[hott] def ap011_ap_square_right {A B C : Type _} (f : A → B → C) {a a' : A} (p : a = a')
    {b₁ b₂ b₃ : B} {q₁₂ : b₁ = b₂} {q₂₃ : b₂ = b₃} {q₁₃ : b₁ = b₃} (r : q₁₂ ⬝ q₂₃ = q₁₃) :
    square (ap011 f p q₁₂) (ap (λx, f x b₃) p) (ap (f a) q₁₃) (ap (f a') q₂₃) :=
  by induction r; induction q₂₃; induction q₁₂; induction p; exact ids

  @[hott] def ap011_ap_square_left {A B C : Type _} (f : B → A → C) {a a' : A} (p : a = a')
    {b₁ b₂ b₃ : B} {q₁₂ : b₁ = b₂} {q₂₃ : b₂ = b₃} {q₁₃ : b₁ = b₃} (r : q₁₂ ⬝ q₂₃ = q₁₃) :
    square (ap011 f q₁₂ p) (ap (f b₃) p) (ap (λx, f x a) q₁₃) (ap (λx, f x a') q₂₃) :=
  by induction r; induction q₂₃; induction q₁₂; induction p; exact ids

  @[hott] def con2_assoc {A : Type _} {x y z t : A} {p p' : x = y} {q q' : y = z} {r r' : z = t}
    (h : p = p') (h' : q = q') (h'' : r = r') :
    square ((h ◾ h') ◾ h'') (h ◾ (h' ◾ h'')) (con.assoc p q r) (con.assoc p' q' r') :=
  by induction h; induction h'; induction h''; exact hrfl

  @[hott] def con_left_inv_idp {A : Type _} {x : A} {p : x = x} (q : p = idp)
    : con.left_inv p = q⁻² ◾ q :=
  by cases q; reflexivity

  @[hott] def eckmann_hilton_con2 {A : Type _} {x : A} {p p' q q': idp = idp :> x = x}
    (h : p = p') (h' : q = q') : square (h ◾ h') (h' ◾ h) (eckmann_hilton p q) (eckmann_hilton p' q') :=
  by induction h; induction h'; exact hrfl

  @[hott] def ap_con_fn {A B : Type _} {a a' : A} {b : B} (g h : A → b = b) (p : a = a') :
    ap (λa, g a ⬝ h a) p = ap g p ◾ ap h p :=
  by induction p; reflexivity

  @[hott] def ap_eq_ap011 {A B C X : Type _} (f : A → B → C) (g : X → A) (h : X → B) {x x' : X}
    (p : x = x') : ap (λx, f (g x) (h x)) p = ap011 f (ap g p) (ap h p) :=
  by induction p; reflexivity

  @[hott] def ap_is_weakly_constant {A B : Type _} {f : A → B}
    (h : is_weakly_constant f) {a a' : A} (p : a = a') : ap f p = (h a a)⁻¹ ⬝ h a a' :=
  by induction p; exact (con.left_inv _)⁻¹

  @[hott] def ap_is_constant_idp {A B : Type _} {f : A → B} {b : B} (p : Πa, f a = b) {a : A} (q : a = a)
    (r : q = idp) : ap_is_constant f p q = ap02 f r ⬝ (con.right_inv (p a))⁻¹ :=
  by cases r; exact (idp_con _)⁻¹

  @[hott] def con_right_inv_natural {A : Type _} {a a' : A} {p p' : a = a'} (q : p = p') :
    con.right_inv p = q ◾ q⁻² ⬝ con.right_inv p' :=
  by induction q; induction p; reflexivity

  @[hott] def whisker_right_ap {A B : Type _} {a a' : A}{b₁ b₂ b₃ : B} (q : b₂ = b₃) (f : A → b₁ = b₂)
    (p : a = a') : whisker_right q (ap f p) = ap (λa, f a ⬝ q) p :=
  by induction p; reflexivity

  @[hott] def ap02_ap_constant {A B C : Type _} {a a' : A} (f : B → C) (b : B) (p : a = a') :
    square (ap_constant p (f b)) (ap02 f (ap_constant p b)) (ap_compose f (λx, b) p) idp :=
  by induction p; exact ids

  @[hott] def ap_constant_compose {A B C : Type _} {a a' : A} (c : C) (f : A → B) (p : a = a') :
    square (ap_constant p c) (ap_constant (ap f p) c) (ap_compose (λx, c) f p) idp :=
  by induction p; exact ids

  @[hott] def ap02_constant {A B : Type _} {a a' : A} (b : B) {p p' : a = a'}
    (q : p = p') : square (ap_constant p b) (ap_constant p' b) (ap02 (λx, b) q) idp :=
  by induction q; exact vrfl

end eq
end hott