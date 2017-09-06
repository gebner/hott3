/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Floris van Doorn

Basic theorems about pathovers
-/
import .path .equiv

universes u v l
hott_theory

namespace hott
open equiv is_equiv function

variables {A : Type _} {A' : Type _} {B : A → Type _} {B' : A → Type _} {B'' : A' → Type _} {C : Π⦃a⦄, B a → Type _}
          {a a₂ a₃ a₄ : A} {p p' : a = a₂} {p₂ : a₂ = a₃} {p₃ : a₃ = a₄} {p₁₃ : a = a₃}
          {b b' : B a} {b₂ b₂' : B a₂} {b₃ : B a₃} {b₄ : B a₄}
          {c : C b} {c₂ : C b₂}

namespace eq
  inductive pathover (B : A → Type.{l}) (b : B a) : Π{a₂ : A}, a = a₂ → B a₂ → Type.{l}
  | idpatho : pathover (refl a) b

  notation b ` =[`:50 p:0 `] `:0 b₂:50 := pathover _ b p b₂
  notation b ` =[`:50 p:0 `; `:0 B `] `:0 b₂:50 := pathover B b p b₂

  @[hott, refl, reducible]
  def idpo : b =[refl a] b :=
  pathover.idpatho b

  @[hott, reducible] def idpatho (b : B a) : b =[refl a] b :=
  pathover.idpatho b

  /- equivalences with equality using transport -/
  @[hott] def pathover_of_tr_eq (r : p ▸ b = b₂) : b =[p] b₂ :=
  by induction p; induction r; constructor

  @[hott] def pathover_of_eq_tr (r : b = p⁻¹ ▸ b₂) : b =[p] b₂ :=
  begin induction p, change b = b₂ at r, induction r, constructor end

  @[hott] def tr_eq_of_pathover (r : b =[p] b₂) : p ▸ b = b₂ :=
  by induction r; reflexivity

  @[hott] def eq_tr_of_pathover (r : b =[p] b₂) : b = p⁻¹ ▸ b₂ :=
  by induction r; reflexivity

  @[hott] def pathover_equiv_tr_eq (p : a = a₂) (b : B a) (b₂ : B a₂)
    : (b =[p] b₂) ≃ (p ▸ b = b₂) :=
  begin
    fapply equiv.MK,
    { exact tr_eq_of_pathover},
    { exact pathover_of_tr_eq},
    { intro r, induction p, induction r, apply idp},
    { intro r, induction r, apply idp},
  end

  @[hott] def pathover_equiv_eq_tr (p : a = a₂) (b : B a) (b₂ : B a₂)
    : (b =[p] b₂) ≃ (b = p⁻¹ ▸ b₂) :=
  begin
    fapply equiv.MK,
    { exact eq_tr_of_pathover},
    { exact pathover_of_eq_tr},
    { intro r, induction p, change b = b₂ at r, induction r, apply idp},
    { intro r, induction r, apply idp},
  end

  @[hott] def pathover_tr (p : a = a₂) (b : B a) : b =[p] p ▸ b :=
  by induction p; constructor

  @[hott] def tr_pathover (p : a = a₂) (b : B a₂) : p⁻¹ ▸ b =[p] b :=
  by induction p; constructor

  @[hott] def concato (r : b =[p] b₂) (r₂ : b₂ =[p₂] b₃) : b =[p ⬝ p₂] b₃ :=
  by induction r₂; exact r

  @[hott] def inverseo (r : b =[p] b₂) : b₂ =[p⁻¹] b :=
  by induction r; constructor

  @[hott] def concato_eq (r : b =[p] b₂) (q : b₂ = b₂') : b =[p] b₂' :=
  by induction q; exact r

  @[hott] def eq_concato (q : b = b') (r : b' =[p] b₂) : b =[p] b₂ :=
  by induction q; exact r

  @[hott] def change_path (q : p = p') (r : b =[p] b₂) : b =[p'] b₂ :=
  q ▸ r

  @[hott, hsimp] def change_path_idp (r : b =[p] b₂) : change_path idp r = r :=
  by reflexivity

  -- infix ` ⬝ ` := concato
  infix ` ⬝o `:72 := concato
  infix ` ⬝op `:73 := concato_eq
  infix ` ⬝po `:73 := eq_concato
  -- postfix `⁻¹` := inverseo
  postfix `⁻¹ᵒ`:(max+10) := inverseo

  @[hott] def pathover_cancel_right (q : b =[p ⬝ p₂] b₃) (r : b₃ =[p₂⁻¹] b₂) : b =[p] b₂ :=
  change_path (con_inv_cancel_right _ _) (q ⬝o r)

  @[hott] def pathover_cancel_right' (q : b =[p₁₃ ⬝ p₂⁻¹] b₂) (r : b₂ =[p₂] b₃) : b =[p₁₃] b₃ :=
  change_path (inv_con_cancel_right _ _) (q ⬝o r)

  @[hott] def pathover_cancel_left (q : b₂ =[p⁻¹] b) (r : b =[p ⬝ p₂] b₃) : b₂ =[p₂] b₃ :=
  change_path (inv_con_cancel_left _ _) (q ⬝o r)

  @[hott] def pathover_cancel_left' (q : b =[p] b₂) (r : b₂ =[p⁻¹ ⬝ p₁₃] b₃) : b =[p₁₃] b₃ :=
  change_path (con_inv_cancel_left _ _) (q ⬝o r)

  /- Some of the theorems analogous to theorems for = in init.path -/

  @[hott, hsimp] def idpo_invo : idpo⁻¹ᵒ = idpo :> b =[idp] b :=
  by refl

  @[hott, hsimp] def cono_idpo (r : b =[p] b₂) : r ⬝o idpo = r :=
  by refl

  @[hott] def idpo_cono (r : b =[p] b₂) : idpo ⬝o r =[idp_con p; λ x, b =[x] b₂] r :=
  by induction r; refl

  @[hott] def cono.assoc' (r : b =[p] b₂) (r₂ : b₂ =[p₂] b₃) (r₃ : b₃ =[p₃] b₄) :
    r ⬝o (r₂ ⬝o r₃) =[con.assoc' _ _ _; λ x, b =[x] b₄] ((r ⬝o r₂) ⬝o r₃) :=
  by induction r₃; induction r₂; induction r; refl

  @[hott] def cono.assoc (r : b =[p] b₂) (r₂ : b₂ =[p₂] b₃) (r₃ : b₃ =[p₃] b₄) :
    (r ⬝o r₂) ⬝o r₃ =[con.assoc _ _ _; λ x, b =[x] b₄] r ⬝o (r₂ ⬝o r₃) :=
  by induction r₃; induction r₂; induction r; refl

  @[hott] def cono.right_inv (r : b =[p] b₂) : r ⬝o r⁻¹ᵒ =[con.right_inv _; λ x, b =[x] b] idpo :=
  by induction r; refl

  @[hott] def cono.left_inv (r : b =[p] b₂) : r⁻¹ᵒ ⬝o r =[con.left_inv _; λ x, b₂ =[x] b₂] idpo :=
  by induction r; refl

  @[hott] def eq_of_pathover {a' a₂' : A'} (q : a' =[p; λ _, A'] a₂') : a' = a₂' :=
  by induction q; refl

  @[hott] def pathover_of_eq (p : a = a₂) {a' a₂' : A'} (q : a' = a₂') : a' =[p; λ _, A'] a₂' :=
  by induction p; induction q; constructor

  @[hott] def pathover_constant (p : a = a₂) (a' a₂' : A') : a' =[p; λ _, A'] a₂' ≃ a' = a₂' :=
  begin
    fapply equiv.MK,
    { exact eq_of_pathover},
    { exact pathover_of_eq p},
    abstract { intro r, induction p, induction r, refl},
    abstract { intro r, induction r, refl},
  end

  @[hott]
  def pathover_of_eq_tr_constant_inv (p : a = a₂) (a' : A')
    : pathover_of_eq p (tr_constant p a')⁻¹ = pathover_tr p a' :=
  by induction p; constructor

  @[hott, elab_simple]
  def eq_of_pathover_idp {b' : B a} (q : b =[idpath a] b') : b = b' :=
  tr_eq_of_pathover q

  --should B be explicit in the next two defs?
  @[hott]
  def pathover_idp_of_eq {b' : B a} (q : b = b') : b =[idpath a] b' :=
  pathover_of_tr_eq q

  @[hott]
  def pathover_idp (b : B a) (b' : B a) : b =[idpath a] b' ≃ b = b' :=
  begin
    fapply equiv.MK,
    {exact eq_of_pathover_idp},
    {exact pathover_idp_of_eq},
    {intros, refine to_right_inv (pathover_equiv_tr_eq _ _ _) _ },
    {intro r, refine to_left_inv (pathover_equiv_tr_eq _ _ _) r, }
  end

  @[hott, hsimp]
  def eq_of_pathover_idp_pathover_of_eq {A X : Type _} (x : X) {a a' : A} (p : a = a') :
    eq_of_pathover_idp (pathover_of_eq (idpath x) p) = p :=
  by induction p; refl

  variable (B)
  @[hott, hsimp] def idpo_concato_eq (r : b = b') : eq_of_pathover_idp (@idpo A B a b ⬝op r) = r :=
  by induction r; reflexivity
  variable {B}

  -- def pathover_idp (b : B a) (b' : B a) : b =[idpath a] b' ≃ b = b' :=
  -- pathover_equiv_tr_eq idp b b'

  -- def eq_of_pathover_idp [reducible] {b' : B a} (q : b =[idpath a] b') : b = b' :=
  -- to_fun !pathover_idp q

  -- def pathover_idp_of_eq [reducible] {b' : B a} (q : b = b') : b =[idpath a] b' :=
  -- to_inv !pathover_idp q

  @[hott, elab_as_eliminator] def idp_rec_on {P : Π⦃b₂ : B a⦄, b =[idpath a] b₂ → Type _}
    {b₂ : B a} (r : b =[idpath a] b₂) (H : P idpo) : P r :=
  have H2 : P (pathover_idp_of_eq (eq_of_pathover_idp r)), from
    eq.rec_on (eq_of_pathover_idp r) H,
  have H3: pathover_idp_of_eq (eq_of_pathover_idp r) = r,
    from to_left_inv (pathover_idp b b₂) r,
  H3 ▸ H2

  @[hott] def rec_on_right {P : Π⦃b₂ : B a₂⦄, b =[p] b₂ → Type _}
    {b₂ : B a₂} (r : b =[p] b₂) (H : P (pathover_tr _ _)) : P r :=
  by induction r; exact H

  @[hott] def rec_on_left {P : Π⦃b : B a⦄, b =[p] b₂ → Type _}
    {b : B a} (r : b =[p] b₂) (H : P (tr_pathover _ _)) : P r :=
  by induction r; exact H

  --pathover with fibration B' ∘ f
  @[hott] def pathover_ap (B' : A' → Type _) (f : A → A') {p : a = a₂}
    {b : B' (f a)} {b₂ : B' (f a₂)} (q : b =[p; B' ∘ f] b₂) : b =[ap f p] b₂ :=
  by induction q; constructor

  @[hott] def pathover_of_pathover_ap (B' : A' → Type _) (f : A → A') {p : a = a₂}
    {b : B' (f a)} {b₂ : B' (f a₂)} (q : b =[ap f p] b₂) : b =[p; B' ∘ f] b₂ :=
  by induction p; apply (idp_rec_on q); apply idpo

  @[hott] def pathover_compose (B' : A' → Type _) (f : A → A') (p : a = a₂)
    (b : B' (f a)) (b₂ : B' (f a₂)) : b =[p; B' ∘ f] b₂ ≃ b =[ap f p] b₂ :=
  begin
    fapply equiv.MK,
    { exact pathover_ap B' f},
    { exact pathover_of_pathover_ap B' f},
    { intro q, induction p, dsimp [pathover_of_pathover_ap], apply (idp_rec_on q), apply idp},
    { intro q, induction q, reflexivity},
  end

  @[hott] def pathover_of_pathover_tr (q : b =[p ⬝ p₂] p₂ ▸ b₂) : b =[p] b₂ :=
  pathover_cancel_right q (pathover_tr _ _)⁻¹ᵒ

  @[hott] def pathover_tr_of_pathover (q : b =[p₁₃ ⬝ p₂⁻¹] b₂) : b =[p₁₃] p₂ ▸ b₂ :=
  pathover_cancel_right' q (pathover_tr _ _)

  @[hott] def pathover_of_tr_pathover (q : p ▸ b =[p⁻¹ ⬝ p₁₃] b₃) : b =[p₁₃] b₃ :=
  pathover_cancel_left' (pathover_tr _ _) q

  @[hott] def tr_pathover_of_pathover (q : b =[p ⬝ p₂] b₃) : p ▸ b =[p₂] b₃ :=
  pathover_cancel_left (pathover_tr _ _)⁻¹ᵒ q

  @[hott] def pathover_tr_of_eq (q : b = b') : b =[p] p ▸ b' :=
  by induction q;apply pathover_tr

  @[hott] def tr_pathover_of_eq (q : b₂ = b₂') : p⁻¹ ▸ b₂ =[p] b₂' :=
  by induction q;apply tr_pathover

  @[hott] def eq_of_parallel_po_right (q : b =[p] b₂) (q' : b =[p] b₂') : b₂ = b₂' :=
  begin
    apply @eq_of_pathover_idp A B, apply change_path (con.left_inv p),
    exact q⁻¹ᵒ ⬝o q'
  end

  @[hott] def eq_of_parallel_po_left (q : b =[p] b₂) (q' : b' =[p] b₂) : b = b' :=
  begin
    apply @eq_of_pathover_idp A B, apply change_path (con.right_inv p),
    exact q ⬝o q'⁻¹ᵒ
  end

  variable (C)
  @[hott, elab_simple] def transporto (r : b =[p] b₂) (c : C b) : C b₂ :=
  by induction r;exact c
  infix ` ▸o `:75 := transporto _

  @[hott] def fn_tro_eq_tro_fn {C' : Π ⦃a : A⦄, B a → Type _} (q : b =[p] b₂)
    (f : Π⦃a : A⦄ (b : B a), C b → C' b) (c : C b) : f b₂ (q ▸o c) = q ▸o (f b c) :=
  by induction q; reflexivity
  variable {C}

  /- various variants of ap for pathovers -/
  @[hott] def apd (f : Πa, B a) (p : a = a₂) : f a =[p] f a₂ :=
  by induction p; constructor

  @[hott] def apd_idp (f : Πa, B a) : apd f idp = @idpo A B a (f a) :=
  by reflexivity

  @[hott] def apo {f : A → A'} (g : Πa, B a → B'' (f a)) (q : b =[p] b₂) :
    g a b =[p; B'' ∘ f] g a₂ b₂ :=
  by induction q; constructor

  @[hott] def apd011 (f : Πa, B a → A') (Ha : a = a₂) (Hb : b =[Ha] b₂)
      : f a b = f a₂ b₂ :=
  by induction Hb; reflexivity

  @[hott] def apd0111 (f : Πa b, C b → A') (Ha : a = a₂) (Hb : b =[Ha] b₂)
    (Hc : c =[apd011 C Ha Hb; id] c₂) : f a b c = f a₂ b₂ c₂ :=
  by induction Hb; apply idp_rec_on Hc; refl

  @[hott] def apod11 {f : Πb, C b} {g : Πb₂, C b₂} (r : f =[p; λ a, Π b : B a, C b] g)
    {b : B a} {b₂ : B a₂} (q : b =[p] b₂) : f b =[apd011 C p q; id] g b₂ :=
  by induction r; apply (idp_rec_on q); constructor

  @[hott] def apdo10 {f : Πb, C b} {g : Πb₂, C b₂} (r : f =[p; λ a, Π b : B a, C b] g)
    (b : B a) : f b =[apd011 C p (pathover_tr _ _); id] g (p ▸ b) :=
  by induction r; constructor

  @[hott] def apo10 {f : B a → B' a} {g : B a₂ → B' a₂} (r : f =[p; λ a, B a → B' a] g)
    (b : B a) : f b =[p] g (p ▸ b) :=
  by induction r; constructor

  @[hott] def apo10_constant_right {f : B a → A'} {g : B a₂ → A'} (r : f =[p; λ a, B a → A'] g)
    (b : B a) : f b = g (p ▸ b) :=
  by induction r; constructor

  @[hott] def apo10_constant_left {f : A' → B a} {g : A' → B a₂} (r : f =[p; λ a, A' → B a] g)
    (a' : A') : f a' =[p] g a' :=
  by induction r; constructor

  @[hott] def apo11 {f : B a → B' a} {g : B a₂ → B' a₂} (r : f =[p; λ a, B a → B' a] g)
    (q : b =[p] b₂) : f b =[p] g b₂ :=
  by induction q; exact apo10 r b

  @[hott] def apo011 {A : Type _} {B C D : A → Type _} {a a' : A} {p : a = a'} {b : B a} {b' : B a'}
    {c : C a} {c' : C a'} (f : Π⦃a⦄, B a → C a → D a) (q : b =[p] b') (r : c =[p] c') :
    f b c =[p] f b' c' :=
  begin induction q, refine idp_rec_on r _, exact idpo end

  @[hott] def apdo011 {A : Type _} {B : A → Type _} {C : Π⦃a⦄, B a → Type _}
    (f : Π⦃a⦄ (b : B a), C b) {a a' : A} (p : a = a') {b : B a} {b' : B a'} (q : b =[p] b')
      : f b =[apd011 C p q; id] f b' :=
  by induction q; constructor

  @[hott] def apdo0111 {A : Type _} {B : A → Type _} {C C' : Π⦃a⦄, B a → Type _}
    (f : Π⦃a⦄ {b : B a}, C b → C' b) {a a' : A} (p : a = a') {b : B a} {b' : B a'} (q : b =[p] b')
    {c : C b} {c' : C b'} (r : c =[apd011 C p q; id] c')
      : f c =[apd011 C' p q; id] f c' :=
  begin
    induction q, dsimp [apd011] at r,
    apply idp_rec_on r, refl
  end

  @[hott] def apo11_constant_right {f : B a → A'} {g : B a₂ → A'}
    (q : f =[p; λ a, B a → A'] g) (r : b =[p] b₂) : f b = g b₂ :=
  eq_of_pathover (apo11 q r)

  /- properties about these "ap"s, transporto and pathover_ap -/
  @[hott] def apd_con (f : Πa, B a) (p : a = a₂) (q : a₂ = a₃)
    : apd f (p ⬝ q) = apd f p ⬝o apd f q :=
  by induction p; induction q; reflexivity

  @[hott] def apd_inv (f : Πa, B a) (p : a = a₂) : apd f p⁻¹ = (apd f p)⁻¹ᵒ :=
  by induction p; reflexivity

  @[hott] def apd_eq_pathover_of_eq_ap (f : A → A') (p : a = a₂) :
    apd f p = pathover_of_eq p (ap f p) :=
  eq.rec_on p idp

  @[hott] def apo_invo (f : Πa, B a → B' a) {Ha : a = a₂} (Hb : b =[Ha] b₂)
      : (apo f Hb)⁻¹ᵒ = apo f Hb⁻¹ᵒ :=
  by induction Hb; reflexivity

  @[hott] def apd011_inv (f : Πa, B a → A') (Ha : a = a₂) (Hb : b =[Ha] b₂)
      : (apd011 f Ha Hb)⁻¹ = (apd011 f Ha⁻¹ Hb⁻¹ᵒ) :=
  by induction Hb; reflexivity

  @[hott] def cast_apd011 (q : b =[p] b₂) (c : C b) : cast (apd011 C p q) c = q ▸o c :=
  by induction q; reflexivity

  @[hott] def apd_compose1 (g : Πa, B a → B' a) (f : Πa, B a) (p : a = a₂)
    : apd (g ∘' f) p = apo g (apd f p) :=
  by induction p; reflexivity

  @[hott] def apd_compose2 (g : Πa', B'' a') (f : A → A') (p : a = a₂)
    : apd (λa, g (f a)) p = pathover_of_pathover_ap B'' f (apd g (ap f p)) :=
  by induction p; reflexivity

  @[hott] def apo_tro (C : Π⦃a⦄, B' a → Type _) (f : Π⦃a⦄, B a → B' a) (q : b =[p] b₂)
    (c : C (f b)) : apo f q ▸o c = q ▸o c :=
  by induction q; reflexivity

  @[hott] def pathover_ap_tro {B' : A' → Type _} (C : Π⦃a'⦄, B' a' → Type _) (f : A → A')
    {b : B' (f a)} {b₂ : B' (f a₂)} (q : b =[p; B' ∘ f] b₂) (c : C b) :
    pathover_ap B' f q ▸o c = q ▸o c :=
  by induction q; reflexivity

  @[hott] def pathover_ap_invo_tro {B' : A' → Type _} (C : Π⦃a'⦄, B' a' → Type _) (f : A → A')
    {b : B' (f a)} {b₂ : B' (f a₂)} (q : b =[p; B' ∘ f] b₂) (c : C b₂)
    : (pathover_ap B' f q)⁻¹ᵒ ▸o c = q⁻¹ᵒ ▸o c :=
  by induction q; reflexivity

  @[hott, elab_simple] def pathover_tro (q : b =[p] b₂) (c : C b) : c =[apd011 C p q; id] q ▸o c :=
  by induction q; constructor

  @[hott] def pathover_ap_invo {B' : A' → Type _} (f : A → A') {p : a = a₂}
    {b : B' (f a)} {b₂ : B' (f a₂)} (q : b =[p; B' ∘ f] b₂)
    : pathover_ap B' f q⁻¹ᵒ =[ap_inv f p; λ x, b₂ =[x] b] (pathover_ap B' f q)⁻¹ᵒ :=
  by induction q; exact idpo

  @[hott] def tro_invo_tro {A : Type _} {B : A → Type _} (C : Π⦃a⦄, B a → Type _)
    {a a' : A} {p : a = a'} {b : B a} {b' : B a'} (q : b =[p] b') (c : C b') :
    q ▸o (q⁻¹ᵒ ▸o c) = c :=
  by induction q; reflexivity

  @[hott] def invo_tro_tro {A : Type _} {B : A → Type _} (C : Π⦃a⦄, B a → Type _)
    {a a' : A} {p : a = a'} {b : B a} {b' : B a'} (q : b =[p] b') (c : C b) :
    q⁻¹ᵒ ▸o (q ▸o c) = c :=
  by induction q; reflexivity

  @[hott] def cono_tro {A : Type _} {B : A → Type _} (C : Π⦃a⦄, B a → Type _)
    {a₁ a₂ a₃ : A} {p₁ : a₁ = a₂} {p₂ : a₂ = a₃} {b₁ : B a₁} {b₂ : B a₂} {b₃ : B a₃}
    (q₁ : b₁ =[p₁] b₂) (q₂ : b₂ =[p₂] b₃) (c : C b₁) :
    transporto C (q₁ ⬝o q₂) c = transporto C q₂ (transporto C q₁ c) :=
  by induction q₂; reflexivity

  @[hott] def is_equiv_transporto {A : Type _} {B : A → Type _} (C : Π⦃a⦄, B a → Type _)
    {a a' : A} {p : a = a'} {b : B a} {b' : B a'} (q : b =[p] b') : is_equiv (transporto C q) :=
  begin
    fapply adjointify,
    { exact transporto C q⁻¹ᵒ},
    { exact tro_invo_tro C q},
    { exact invo_tro_tro C q}
  end

  @[hott] def equiv_apd011 {A : Type _} {B : A → Type _} (C : Π⦃a⦄, B a → Type _)
    {a a' : A} {p : a = a'} {b : B a} {b' : B a'} (q : b =[p] b') : C b ≃ C b' :=
  equiv.mk (transporto C q) (is_equiv_transporto _ _)

  /- some cancellation laws for concato_eq an variants -/

  @[hott] def cono.right_inv_eq (q : b = b') :
    pathover_idp_of_eq q ⬝op q⁻¹ = (idpo : b =[refl a] b) :=
  by induction q;constructor

  @[hott] def cono.right_inv_eq' (q : b = b') :
    q ⬝po (pathover_idp_of_eq q⁻¹) = (idpo : b =[refl a] b) :=
  by induction q;constructor

  @[hott] def cono.left_inv_eq (q : b = b') :
    pathover_idp_of_eq q⁻¹ ⬝op q = (idpo : b' =[refl a] b') :=
  by induction q;constructor

  @[hott] def cono.left_inv_eq' (q : b = b') :
    q⁻¹ ⬝po pathover_idp_of_eq q = (idpo : b' =[refl a] b') :=
  by induction q;constructor

  @[hott] def pathover_of_fn_pathover_fn (f : Π{a}, B a ≃ B' a) (r : f.to_fun b =[p] f.to_fun b₂) : b =[p] b₂ :=
  (left_inv f.to_fun b)⁻¹ ⬝po apo (λa, to_fun f⁻¹ᵉ) r ⬝op left_inv f.to_fun b₂

  /- a pathover in a pathover type where the only thing which varies is the path is the same as
    an equality with a change_path -/
  @[hott] def change_path_of_pathover (s : p = p') (r : b =[p] b₂) (r' : b =[p'] b₂)
    (q : r =[s; λ p, b =[p] b₂] r') : change_path s r = r' :=
  by induction s; eapply idp_rec_on q; reflexivity

  @[hott] def pathover_of_change_path (s : p = p') (r : b =[p] b₂) (r' : b =[p'] b₂)
    (q : change_path s r = r') : r =[s; λ p, b =[p] b₂] r' :=
  by induction s; induction q; constructor

  @[hott] def pathover_pathover_path (s : p = p') (r : b =[p] b₂) (r' : b =[p'] b₂) :
    (r =[s; λ p, b =[p] b₂] r') ≃ change_path s r = r' :=
  begin
    fapply equiv.MK,
    { apply change_path_of_pathover},
    { apply pathover_of_change_path},
    { intro q, induction s, induction q, reflexivity},
    { intro q, induction s, eapply idp_rec_on q, reflexivity},
  end

  /- variants of inverse2 and concat2 -/
  @[hott] def inverseo2 {r r' : b =[p] b₂} (s : r = r') : r⁻¹ᵒ = r'⁻¹ᵒ :=
  by induction s; reflexivity

  @[hott] def concato2 {r r' : b =[p] b₂} {r₂ r₂' : b₂ =[p₂] b₃}
    (s : r = r') (s₂ : r₂ = r₂') : r ⬝o r₂ = r' ⬝o r₂' :=
  by induction s; induction s₂; reflexivity

  infixl ` ◾o `:75 := concato2
  postfix [parsing_only] `⁻²ᵒ`:(max+10) := inverseo2 --this notation is abusive, should we use it?

  -- find a better name for this
  @[hott] def fn_tro_eq_tro_fn2 (q : b =[p] b₂)
    {k : A → A} {l : Π⦃a⦄, B a → B (k a)} (m : Π⦃a⦄ {b : B a}, C b → C (l b))
    (c : C b) :
    m (q ▸o c) = (pathover_ap B k (apo l q)) ▸o (m c) :=
  by induction q; reflexivity

  @[hott] def apd0111_precompose (f  : Π⦃a⦄ {b : B a}, C b → A')
    {k : A → A} {l : Π⦃a⦄, B a → B (k a)} (m : Π⦃a⦄ {b : B a}, C b → C (l b))
    {q : b =[p] b₂} (c : C b)
    : apd0111 (λa b (c : C b), f (m c)) p q (pathover_tro q c) ⬝ ap (@f _ _) (fn_tro_eq_tro_fn2 q m c) =
      apd0111 f (ap k p) (pathover_ap B k (apo l q)) (pathover_tro _ (m c)) :=
  by induction q; reflexivity

end eq

end hott