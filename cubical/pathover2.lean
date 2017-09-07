/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Floris van Doorn

Coherence conditions for operations on pathovers
-/

import ..init
universe u
hott_theory

namespace hott

open function equiv

namespace eq

  variables {A : Type _} {A' : Type _} {A'' : Type _} {B : A → Type _} {B' : A → Type _} {B'' : A' → Type _} 
            {C : Π⦃a⦄, B a → Type _}
            {a a₂ a₃ a₄ : A} {p p' p'' : a = a₂} {p₂ p₂' : a₂ = a₃} {p₃ : a₃ = a₄} {p₁₃ : a = a₃}
            {a' : A'}
            {b b' : B a} {b₂ b₂' : B a₂} {b₃ : B a₃} {b₄ : B a₄}
            {c : C b} {c₂ : C b₂}

  @[hott] def pathover_ap_id (q : b =[p] b₂) : pathover_ap B id q = change_path (ap_id p)⁻¹ q :=
  by induction q; reflexivity

  @[hott] def pathover_ap_compose (B : A'' → Type _) (g : A' → A'') (f : A → A')
    {b : B (g (f a))} {b₂ : B (g (f a₂))} (q : b =[p; λa, B (g (f a))] b₂) : pathover_ap B (g ∘ f) q
      = change_path (ap_compose g f p)⁻¹ (pathover_ap B g (pathover_ap (B ∘ g) f q)) :=
  by induction q; reflexivity

  @[hott] def pathover_ap_compose_rev (B : A'' → Type _) (g : A' → A'') (f : A → A')
    {b : B (g (f a))} {b₂ : B (g (f a₂))} (q : b =[p; λa, B (g (f a))] b₂) :
    pathover_ap B g (pathover_ap (B ∘ g) f q)
      = change_path (ap_compose g f p) (pathover_ap B (g ∘ f) q) :=
  by induction q; reflexivity

  @[hott, hsimp] def pathover_of_tr_eq_idp (r : b = b') : 
    @pathover_of_tr_eq _ _ _ _ idp _ _ r = pathover_idp_of_eq B r :=
  idp

  @[hott] def pathover_of_tr_eq_eq_concato (r : p ▸ b = b₂)
    : pathover_of_tr_eq r = pathover_tr p b ⬝o pathover_idp_of_eq B r :=
  by induction r; induction p; reflexivity

  @[hott] def apd011_eq_apo11_apd (f : Πa, B a → A') (p : a = a₂) (q : b =[p] b₂)
      : apd011 f p q = apo11_constant_right (apd f p) q :=
  by induction q; reflexivity

  @[hott] def change_path_con (q : p = p') (q' : p' = p'') (r : b =[p] b₂) :
    change_path (q ⬝ q') r = change_path q' (change_path q r) :=
  by induction q; induction q'; reflexivity

  @[hott] def change_path_invo (q : p = p') (r : b =[p] b₂) :
    change_path (inverse2 q) r⁻¹ᵒ = (change_path q r)⁻¹ᵒ :=
  by induction q; reflexivity

  @[hott] def change_path_cono (q : p = p') (q₂ : p₂ = p₂') (r : b =[p] b₂) (r₂ : b₂ =[p₂] b₃):
    change_path (q ◾ q₂) (r ⬝o r₂) = change_path q r ⬝o change_path q₂ r₂ :=
  by induction q; induction q₂; reflexivity

  @[hott] def pathover_of_pathover_ap_invo (B' : A' → Type _) (f : A → A')
    {b : B' (f a)} {b₂ : B' (f a₂)} (q : b =[ap f p] b₂) :
    pathover_of_pathover_ap B' f (change_path (ap_inv f p)⁻¹ q⁻¹ᵒ) =
      (pathover_of_pathover_ap B' f q)⁻¹ᵒ:=
  by induction p; eapply idp_rec_on q; reflexivity

  @[hott] def pathover_of_pathover_ap_cono (B' : A' → Type _) (f : A → A')
    {b : B' (f a)} {b₂ : B' (f a₂)} {b₃ : B' (f a₃)} (q : b =[ap f p] b₂) (q₂ : b₂ =[ap f p₂] b₃) :
    pathover_of_pathover_ap B' f (change_path (ap_con f p p₂)⁻¹ (q ⬝o q₂)) =
      pathover_of_pathover_ap B' f q ⬝o pathover_of_pathover_ap B' f q₂ :=
  begin induction p₂, apply idp_rec_on q₂, refl end

  @[hott] def pathover_ap_pathover_of_pathover_ap (P : A'' → Type _) (g : A' → A'') (f : A → A')
    {p : a = a₂} {b : P (g (f a))} {b₂ : P (g (f a₂))} (q : b =[ap f p; P ∘ g] b₂) :
    pathover_ap P (g ∘ f) ((pathover_of_pathover_ap (P ∘ g) f q) : b =[p; (P ∘ g) ∘ f] b₂) =
    change_path (ap_compose g f p)⁻¹ (pathover_ap P g q) :=
  by induction p; eapply (idp_rec_on q); reflexivity

  @[hott] def change_path_pathover_of_pathover_ap (B' : A' → Type _) (f : A → A') {p p' : a = a₂}
    (r : p = p') {b : B' (f a)} {b₂ : B' (f a₂)} (q : b =[ap f p] b₂) :
    change_path r (pathover_of_pathover_ap B' f q) =
      pathover_of_pathover_ap B' f (change_path (ap02 f r) q) :=
  by induction r; reflexivity

  @[hott] def pathover_ap_change_path (B' : A' → Type _) (f : A → A') {p p' : a = a₂}
    (r : p = p') {b : B' (f a)} {b₂ : B' (f a₂)} (q : b =[p; B' ∘ f] b₂) :
    pathover_ap B' f (change_path r q) = change_path (ap02 f r) (pathover_ap B' f q) :=
  by induction r; reflexivity

  @[hott] def change_path_equiv (b : B a) (b₂ : B a₂) (q : p = p')
    : (b =[p] b₂) ≃ (b =[p'] b₂) :=
  begin
    fapply equiv.MK,
    { exact change_path q},
    { exact change_path q⁻¹},
    { intro r, induction q, reflexivity},
    { intro r, induction q, reflexivity},
  end

  @[hott] def apd_ap {B : A' → Type _} (g : Πb, B b) (f : A → A') (p : a = a₂)
    :  apd g (ap f p) = pathover_ap B f (apd (λx, g (f x)) p)  :=
  by induction p; reflexivity

  @[hott] def apd_eq_apd_ap {B : A' → Type _} (g : Πb, B b) (f : A → A') (p : a = a₂)
    : apd (λx, g (f x)) p = pathover_of_pathover_ap B f (apd g (ap f p)) :=
  by induction p; reflexivity

  @[hott] def ap_compose_ap02_constant {A B C : Type _} {a a' : A} (p : a = a') (b : B) (c : C) :
  ap_compose (λc, b) (λa, c) p ⬝ ap02 (λc, b) (ap_constant p c) = ap_constant p b :=
  by induction p; reflexivity

  @[hott] def pathover_ap_pathover_of_eq (p : a₂ = a₃) (q : b = b') :
    pathover_ap B (λa', a) (pathover_of_eq p q) = change_path (ap_constant p a)⁻¹ (pathover_idp_of_eq B q) :=
  by induction p; induction q; refl

  @[hott] theorem apd_constant (b : B'' a') (p : a = a₂) :
    pathover_ap B'' (λa, a') (apd (λa, b) p) = change_path (ap_constant p a')⁻¹ idpo :=
  by induction p; reflexivity

  @[hott] theorem apd_constant' {A A' : Type _} {B : A' → Type _} {a₁ a₂ : A} {a' : A'} (b : B a')
    (p : a₁ = a₂) : apd (λx, b) p = pathover_of_eq p idp :=
  by induction p; reflexivity

  @[hott] def apd_change_path {B : A → Type _} {a a₂ : A} (f : Πa, B a) {p p' : a = a₂} (s : p = p')
    : apd f p' = change_path s (apd f p) :=
  by induction s; reflexivity

  @[hott] def cono_invo_eq_idpo {q q' : b =[p] b₂} (r : q = q')
    : change_path (con.right_inv p) (q ⬝o q'⁻¹ᵒ) = idpo :=
  by induction r; induction q; reflexivity

  @[hott] def tr_eq_of_pathover_concato_eq {A : Type _} {B : A → Type _} {a a' : A} {p : a = a'}
    {b : B a} {b' b'' : B a'} (q : b =[p] b') (r : b' = b'') :
    tr_eq_of_pathover (q ⬝op r) = tr_eq_of_pathover q ⬝ r :=
  by induction r; reflexivity

end eq
end hott