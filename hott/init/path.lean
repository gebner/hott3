/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Jakob von Raumer, Floris van Doorn

Ported from Coq HoTT
-/
import hott.init.support hott.init.simp_attr

universes u v w
hott_theory

namespace hott
open function

/- Path equality -/

inductive eq {A : Type u} (a : A) : A → Type u
| refl : eq a

hott_theory_cmd "open hott.eq"
hott_theory_cmd "local infix ` = ` := hott.eq"

@[hott] def rfl {A : Type u} {a : A} := eq.refl a

namespace eq
  variables {A : Type _} {a b c : A}

  @[elab_as_eliminator, hott]
  def subst {P : A → Type u} (H₁ : a = b) (H₂ : P a) : P b :=
  eq.rec H₂ H₁

  @[hott] def trans (H₁ : a = b) (H₂ : b = c) : a = c :=
  subst H₂ H₁

  @[hott] def symm (H : a = b) : b = a :=
  subst H (refl a)

  @[hott] def mp {a b : Type _} : (a = b) → a → b :=
  @eq.rec_on _ a (λ c _, c) b

  @[hott] def mpr {a b : Type _} : (a = b) → b → a :=
  assume H₁ H₂, eq.rec_on (eq.symm H₁) H₂

  @[hott] def congr {A B : Type _} {f₁ f₂ : A → B} {a₁ a₂ : A} (H₁ : f₁ = f₂) (H₂ : a₁ = a₂) : f₁ a₁ = f₂ a₂ :=
  eq.subst H₁ (eq.subst H₂ rfl)

  @[hott] def congr_fun {A : Type _} {B : A → Type _} {f g : Π x, B x} (H : f = g) (a : A) : f a = g a :=
  eq.subst H (eq.refl (f a))

  @[hott] def congr_arg {A B : Type _} (a a' : A) (f : A → B) (Ha : a = a') : f a = f a' :=
  eq.subst Ha rfl

  @[hott] def congr_arg2 {A B C : Type _} (a a' : A) (b b' : B) (f : A → B → C) (Ha : a = a') (Hb : b = b') : f a b = f a' b' :=
  eq.subst Ha (eq.subst Hb rfl)
end eq

namespace eq
  variables {A : Type _} {B : Type _} {C : Type _} {P : A → Type _} {a a' x y z t : A} {b b' : B}

  notation x = y `:>`:50 A:49 := @eq A x y
  @[refl, reducible, hott] def idp {a : A} := refl a
  @[hott, reducible] def idpath (a : A) := refl a

  -- unbased path induction
  @[hott]
  def rec_unbased {P : Π (a b : A), (a = b) → Type v}
    (H : Π (a : A), P a a idp) {a b : A} (p : a = b) : P a b p :=
  eq.rec (H a) p

  @[hott]
  def rec_on_unbased {P : Π (a b : A), (a = b) → Type v}
    {a b : A} (p : a = b) (H : Π (a : A), P a a idp) : P a b p :=
  eq.rec (H a) p

  /- Concatenation and inverse -/

  @[trans, hott]
  def concat (p : x = y) (q : y = z) : x = z :=
  by induction q; exact p

  @[symm, hott]
  def inverse (p : x = y) : y = x :=
  by induction p; reflexivity

  attribute [congr] congr

  infix   ⬝  := concat
  postfix ⁻¹ := inverse
  --a second notation for the inverse, which is not overloaded
  postfix [parsing_only] `⁻¹ᵖ`:std.prec.max_plus := inverse

  /- The 1-dimensional groupoid structure -/

  -- The identity path is a right unit.
  @[hott, hsimp] def con_idp (p : x = y) : p ⬝ idp = p :=
  idp

  -- The identity path is a left unit.
  @[hott, hsimp] def idp_con (p : x = y) : idp ⬝ p = p :=
  by induction p; reflexivity

  @[hott, hsimp] def idp_inv : (@idp _ x)⁻¹ = idp := idp

  -- Concatenation is associative.
  @[hott] def con.assoc' (p : x = y) (q : y = z) (r : z = t) :
    p ⬝ (q ⬝ r) = (p ⬝ q) ⬝ r :=
  by induction r; reflexivity

  @[hott] def con.assoc (p : x = y) (q : y = z) (r : z = t) :
    (p ⬝ q) ⬝ r = p ⬝ (q ⬝ r) :=
  by induction r; reflexivity

  @[hott] def con.assoc5 {a₁ a₂ a₃ a₄ a₅ a₆ : A}
    (p₁ : a₁ = a₂) (p₂ : a₂ = a₃) (p₃ : a₃ = a₄) (p₄ : a₄ = a₅) (p₅ : a₅ = a₆) :
    p₁ ⬝ (p₂ ⬝ p₃ ⬝ p₄) ⬝ p₅ = (p₁ ⬝ p₂) ⬝ p₃ ⬝ (p₄ ⬝ p₅) :=
  by induction p₅; induction p₄; induction p₃; reflexivity

  -- The left inverse law.
  @[hott, hsimp] def con.right_inv (p : x = y) : p ⬝ p⁻¹ = idp :=
  by induction p; reflexivity

  -- The right inverse law.
  @[hott, hsimp] def con.left_inv (p : x = y) : p⁻¹ ⬝ p = idp :=
  by induction p; reflexivity

  /- Several auxiliary theorems about canceling inverses across associativity. These are somewhat
     redundant, following from earlier theorems. -/

  @[hott, hsimp] def inv_con_cancel_left (p : x = y) (q : y = z) : p⁻¹ ⬝ (p ⬝ q) = q :=
  by induction q; induction p; reflexivity

  @[hott, hsimp] def con_inv_cancel_left (p : x = y) (q : x = z) : p ⬝ (p⁻¹ ⬝ q) = q :=
  by induction q; induction p; reflexivity

  @[hott, hsimp] def con_inv_cancel_right (p : x = y) (q : y = z) : (p ⬝ q) ⬝ q⁻¹ = p :=
  by induction q; reflexivity

  @[hott, hsimp] def inv_con_cancel_right (p : x = z) (q : y = z) : (p ⬝ q⁻¹) ⬝ q = p :=
  by induction q; reflexivity

  -- Inverse distributes over concatenation
  @[hott]
  def con_inv (p : x = y) (q : y = z) : (p ⬝ q)⁻¹ = q⁻¹ ⬝ p⁻¹ :=
  by induction q; induction p; reflexivity

  @[hott]
  def inv_con_inv_left (p : y = x) (q : y = z) : (p⁻¹ ⬝ q)⁻¹ = q⁻¹ ⬝ p :=
  by induction q; induction p; reflexivity

  @[hott]
  def inv_con_inv_right (p : x = y) (q : z = y) : (p ⬝ q⁻¹)⁻¹ = q ⬝ p⁻¹ :=
  by induction q; induction p; reflexivity

  @[hott]
  def inv_con_inv_inv (p : y = x) (q : z = y) : (p⁻¹ ⬝ q⁻¹)⁻¹ = q ⬝ p :=
  by induction q; induction p; reflexivity

  -- Inverse is an involution.
  @[hott, hsimp] def inv_inv  (p : x = y) : p⁻¹⁻¹ = p :=
  by induction p; reflexivity

  -- auxiliary def used by 'cases' tactic
  @[hott]
  def elim_inv_inv  {A : Type u} {a b : A} {C : a = b → Type v}
    (H₁ : a = b) (H₂ : C (H₁⁻¹⁻¹)) : C H₁ :=
  @eq.rec_on _ _ (λ a h, C a) _ (inv_inv H₁) H₂

  @[hott] def eq.rec_symm {A : Type u} {a₀ : A} {P : Π⦃a₁⦄, a₁ = a₀ → Type v}
    (H : P idp) ⦃a₁ : A⦄ (p : a₁ = a₀) : P p :=
  by induction p; exact H

  /- Theorems for moving things around in equations -/

  notation `!idp_con` := idp_con _

  @[hott]
  def con_eq_of_eq_inv_con {p : x = z} {q : y = z} {r : y = x} :
    p = r⁻¹ ⬝ q → r ⬝ p = q :=
  begin
    induction r, intro h, exact !idp_con ⬝ h ⬝ !idp_con
  end

  @[hott]
  def con_eq_of_eq_con_inv  {p : x = z} {q : y = z} {r : y = x} :
    r = q ⬝ p⁻¹ → r ⬝ p = q :=
  by induction p; exact id

  @[hott]
  def inv_con_eq_of_eq_con {p : x = z} {q : y = z} {r : x = y} :
    p = r ⬝ q → r⁻¹ ⬝ p = q :=
  by induction r; intro h; exact !idp_con ⬝ h ⬝ !idp_con

  @[hott]
  def con_inv_eq_of_eq_con  {p : z = x} {q : y = z} {r : y = x} :
    r = q ⬝ p → r ⬝ p⁻¹ = q :=
  by induction p; exact id

  @[hott] def eq_con_of_inv_con_eq {p : x = z} {q : y = z} {r : y = x} :
    r⁻¹ ⬝ q = p → q = r ⬝ p :=
  by induction r; intro h; exact !idp_con⁻¹ ⬝ h ⬝ !idp_con⁻¹

  @[hott] def eq_con_of_con_inv_eq  {p : x = z} {q : y = z} {r : y = x} :
    q ⬝ p⁻¹ = r → q = r ⬝ p :=
  by induction p; exact id

  @[hott] def eq_inv_con_of_con_eq {p : x = z} {q : y = z} {r : x = y} :
    r ⬝ q = p → q = r⁻¹ ⬝ p :=
  by induction r; intro h; exact !idp_con⁻¹ ⬝ h ⬝ !idp_con⁻¹

  @[hott] def eq_con_inv_of_con_eq  {p : z = x} {q : y = z} {r : y = x} :
    q ⬝ p = r → q = r ⬝ p⁻¹ :=
  by induction p; exact id

  @[hott] def eq_of_con_inv_eq_idp  {p q : x = y} : p ⬝ q⁻¹ = idp → p = q :=
  by induction q; exact id

  @[hott] def eq_of_inv_con_eq_idp {p q : x = y} : q⁻¹ ⬝ p = idp → p = q :=
  by induction q; intro h; exact !idp_con⁻¹ ⬝ h

  @[hott] def eq_inv_of_con_eq_idp'  {p : x = y} {q : y = x} : p ⬝ q = idp → p = q⁻¹ :=
  by induction q; exact id

  @[hott] def eq_inv_of_con_eq_idp {p : x = y} {q : y = x} : q ⬝ p = idp → p = q⁻¹ :=
  by induction q; intro h; exact !idp_con⁻¹ ⬝ h

  @[hott] def eq_of_idp_eq_inv_con {p q : x = y} : idp = p⁻¹ ⬝ q → p = q :=
  by induction p; intro h; exact h ⬝ !idp_con

  @[hott] def eq_of_idp_eq_con_inv  {p q : x = y} : idp = q ⬝ p⁻¹ → p = q :=
  by induction p; exact id

  @[hott] def inv_eq_of_idp_eq_con  {p : x = y} {q : y = x} : idp = q ⬝ p → p⁻¹ = q :=
  by induction p; exact id

  @[hott] def inv_eq_of_idp_eq_con' {p : x = y} {q : y = x} : idp = p ⬝ q → p⁻¹ = q :=
  by induction p; intro h; exact h ⬝ !idp_con

  @[hott] def con_inv_eq_idp  {p q : x = y} (r : p = q) : p ⬝ q⁻¹ = idp :=
  by induction r; apply con.right_inv

  @[hott] def inv_con_eq_idp  {p q : x = y} (r : p = q) : q⁻¹ ⬝ p = idp :=
  by induction r; apply con.left_inv

  @[hott] def con_eq_idp {p : x = y} {q : y = x} (r : p = q⁻¹) : p ⬝ q = idp :=
  by induction q; exact r

  @[hott] def idp_eq_inv_con {p q : x = y} (r : p = q) : idp = p⁻¹ ⬝ q :=
  by induction r; exact (con.left_inv _)⁻¹

  @[hott] def idp_eq_con_inv {p q : x = y} (r : p = q) : idp = q ⬝ p⁻¹ :=
  by induction r; exact (con.right_inv _)⁻¹

  @[hott] def idp_eq_con {p : x = y} {q : y = x} (r : p⁻¹ = q) : idp = q ⬝ p :=
  by induction p; exact r

  @[hott] def eq_idp_of_con_right {p : x = x} {q : x = y} (r : p ⬝ q = q) : p = idp :=
  by induction q; exact r

  @[hott] def eq_idp_of_con_left {p : x = x} {q : y = x} (r : q ⬝ p = q) : p = idp :=
  by induction q; exact (idp_con p)⁻¹ ⬝ r

  @[hott] def idp_eq_of_con_right {p : x = x} {q : x = y} (r : q = p ⬝ q) : idp = p :=
  by induction q; exact r

  @[hott] def idp_eq_of_con_left {p : x = x} {q : y = x} (r : q = q ⬝ p) : idp = p :=
  by induction q; exact r ⬝ idp_con p

  /- Transport -/

  @[subst, reducible, hott]
  def transport (P : A → Type v) {x y : A} (p : x = y)
    (u : P x) : P y :=
  by induction p; exact u

  -- This idiom makes the operation right associative.
  hott_theory_cmd "local infixr ` ▸ ` := hott.eq.transport _"

  @[reducible, hott]
  def cast {A B : Type u} (p : A = B) (a : A) : B :=
  p ▸ a

  @[reducible, hott]
  def cast_def {A B : Type u} (p : A = B) (a : A)
    : cast p a = p ▸ a :=
  idp

  @[reducible, hott]
  def tr_rev (P : A → Type u) {x y : A} (p : x = y) (u : P y) : P x :=
  p⁻¹ ▸ u

  @[hott] def ap {{A : Type u}} {{B : Type v}} (f : A → B) {x y:A} (p : x = y) : f x = f y :=
  by induction p; reflexivity

  @[hott, hsimp] def eq_rec_ap {A B} (f : A → B) {x y : A} (p : x = y) :
    (eq.rec idp p : f x = f y) = ap f p := idp

  notation `ap01` [parsing_only] := ap

  @[reducible, hott]
  def homotopy (f g : Πx, P x) : Type _ :=
  Π x : A, f x = g x

  infix ~ := homotopy

  @[refl, reducible, hott]
  protected def homotopy.refl (f : Πx, P x) : f ~ f :=
  λ x, idp

  @[hott] protected def homotopy.rfl {f : Πx, P x} : f ~ f :=
  by refl

  @[symm, reducible, hott]
  protected def homotopy.symm  {f g : Πx, P x} (H : f ~ g)
    : g ~ f :=
  λ x, (H x)⁻¹

  @[trans, reducible, hott]
  protected def homotopy.trans {f g h : Πx, P x}
    (H1 : f ~ g) (H2 : g ~ h) : f ~ h :=
  λ x, H1 x ⬝ H2 x

  infix ` ⬝hty `:75 := homotopy.trans
  postfix `⁻¹ʰᵗʸ`:(max+1) := homotopy.symm

  @[hott] def homotopy.refl_symm {f : Π x, P x} : (homotopy.refl f).symm = homotopy.refl f :=
  idp

  @[hott] def hwhisker_left  (g : B → C) {f f' : A → B} (H : f ~ f') :
    g ∘ f ~ g ∘ f' :=
  λa, ap g (H a)

  @[hott] def hwhisker_right  (f : A → B) {g g' : B → C} (H : g ~ g') :
    g ∘ f ~ g' ∘ f :=
  λa, H (f a)

  @[hott, hsimp] def compose_id (f : A → B) : f ∘ id ~ f :=
  by reflexivity

  @[hott, hsimp] def id_compose (f : A → B) : id ∘ f ~ f :=
  by reflexivity

  @[hott] def compose2 {A B C : Type _} {g g' : B → C} {f f' : A → B}
    (p : g ~ g') (q : f ~ f') : g ∘ f ~ g' ∘ f' :=
  hwhisker_right f p ⬝hty hwhisker_left g' q

  @[hott] def hassoc {A B C D : Type _} (h : C → D) (g : B → C) (f : A → B) : (h ∘ g) ∘ f ~ h ∘ (g ∘ f) :=
  λa, idp

  @[hott] def homotopy_of_eq {f g : Πx, P x} (H1 : f = g) : f ~ g :=
  H1 ▸ homotopy.refl f

  @[hott] def apd10  {f g : Πx, P x} (H : f = g) : f ~ g :=
  λx, by induction H; reflexivity

  --the next theorem is useful if you want to write "apply (apd10' a)"
  @[hott] def apd10'  {f g : Πx, P x} (a : A) (H : f = g) : f a = g a :=
  by induction H; reflexivity

  --apd10 is also ap evaluation
  @[hott] def apd10_eq_ap_eval {f g : Πx, P x} (H : f = g) (a : A)
    : apd10 H a = ap (λs : Πx, P x, s a) H :=
  by induction H; reflexivity

  @[reducible,hott]
  def ap10 {f g : A → B} (H : f = g) : f ~ g := apd10 H

  @[hott] def ap11 {f g : A → B} (H : f = g) {x y : A} (p : x = y) : f x = g y :=
  by induction H; exact ap f p

  -- [apd] is defined in init.pathover using pathover instead of an equality with transport.
  @[hott] def apdt  (f : Πa, P a) {x y : A} (p : x = y) : p ▸ f x = f y :=
  by induction p; reflexivity

  @[hott] def ap011  (f : A → B → C) (Ha : a = a') (Hb : b = b') : f a b = f a' b' :=
  by induction Ha; exact ap (f a) Hb

  /- More theorems for moving things around in equations -/

  @[hott] def tr_eq_of_eq_inv_tr {P : A → Type v} {x y : A} {p : x = y} {u : P x} {v : P y} :
    u = p⁻¹ ▸ v → p ▸ u = v :=
  by induction p; exact id

  @[hott] def inv_tr_eq_of_eq_tr {P : A → Type v} {x y : A} {p : y = x} {u : P x} {v : P y} :
    u = p ▸ v → p⁻¹ ▸ u = v :=
  by induction p; exact id

  @[hott] def eq_inv_tr_of_tr_eq {P : A → Type v} {x y : A} {p : x = y} {u : P x} {v : P y} :
    p ▸ u = v → u = p⁻¹ ▸ v :=
  by induction p; exact id

  @[hott] def eq_tr_of_inv_tr_eq {P : A → Type v} {x y : A} {p : y = x} {u : P x} {v : P y} :
    p⁻¹ ▸ u = v → u = p ▸ v :=
  by induction p; exact id

  /- Transporting along the diagonal of a type family -/
  @[hott] def tr_diag_eq_tr_tr {A : Type u} (P : A → A → Type v) {x y : A} (p : x = y) (a : P x x) :
    transport (λ x, P x x) p a = transport (λ z, P y z) p (@transport _ (λ z, P z x) _ _ p a) :=
  by induction p; reflexivity

  /- Functoriality of functions -/

  -- Here we prove that functions behave like functors between groupoids, and that [ap] itself is
  -- functorial.

  -- Functions take identity paths to identity paths
  @[hott, hsimp] def ap_idp  (x : A) (f : A → B) : ap f idp = idp :> (f x = f x) := idp

  -- Functions commute with concatenation.
  @[hott] def ap_con  (f : A → B) {x y z : A} (p : x = y) (q : y = z) :
    ap f (p ⬝ q) = ap f p ⬝ ap f q :=
  by induction q; reflexivity

  @[hott] def con_ap_con_eq_con_ap_con_ap (f : A → B) {w x y z : A} (r : f w = f x)
    (p : x = y) (q : y = z) : r ⬝ ap f (p ⬝ q) = (r ⬝ ap f p) ⬝ ap f q :=
  by induction q; induction p; reflexivity

  @[hott] def ap_con_con_eq_ap_con_ap_con (f : A → B) {w x y z : A} (p : x = y) (q : y = z)
    (r : f z = f w) : ap f (p ⬝ q) ⬝ r = ap f p ⬝ (ap f q ⬝ r) :=
  by induction q; induction p; induction r; refl

  -- Functions commute with path inverses.
  @[hott] def ap_inv'  (f : A → B) {x y : A} (p : x = y) : (ap f p)⁻¹ = ap f p⁻¹ :=
  by induction p; reflexivity

  @[hott] def ap_inv  (f : A → B) {x y : A} (p : x = y) : ap f p⁻¹ = (ap f p)⁻¹ :=
  by induction p; reflexivity

  -- [ap] itself is functorial in the first argument.

  @[hott, hsimp] def ap_id  (p : x = y) : ap id p = p :=
  by induction p; reflexivity

  @[hott] def ap_compose  (g : B → C) (f : A → B) {x y : A} (p : x = y) :
    ap (g ∘ f) p = (ap g (ap f p) : g (f x) = g (f y)) :=
  by induction p; reflexivity

  -- Sometimes we don't have the actual function [compose].
  @[hott] def ap_compose'  (g : B → C) (f : A → B) {x y : A} (p : x = y) :
    ap (λa, g (f a)) p = ap g (ap f p) :=
  by induction p; reflexivity

  -- The action of constant maps.
  @[hott] def ap_constant  (p : x = y) (z : B) : ap (λu, z) p = idp :=
  by induction p; reflexivity

  -- Naturality of [ap].
  -- see also natural_square in cubical.square
  @[hott] def ap_con_eq_con_ap {f g : A → B} (p : f ~ g) {x y : A} (q : x = y) :
    ap f q ⬝ p y = p x ⬝ ap g q :=
  by induction q; apply idp_con

  -- Naturality of [ap] at identity.
  @[hott] def ap_con_eq_con {f : A → A} (p : Πx, f x = x) {x y : A} (q : x = y) :
    ap f q ⬝ p y = p x ⬝ q :=
  by induction q; apply idp_con

  @[hott] def con_ap_eq_con {f : A → A} (p : Πx, x = f x) {x y : A} (q : x = y) :
    p x ⬝ ap f q =  q ⬝ p y :=
  by induction q; exact !idp_con⁻¹

  -- Naturality of [ap] with constant function
  @[hott] def ap_con_eq {f : A → B} {b : B} (p : Πx, f x = b) {x y : A} (q : x = y) :
    ap f q ⬝ p y = p x :=
  by induction q; apply idp_con

  -- Naturality with other paths hanging around.

  @[hott] def con_ap_con_con_eq_con_con_ap_con {f g : A → B} (p : f ~ g) {x y : A} (q : x = y)
      {w z : B} (r : w = f x) (s : g y = z) :
    (r ⬝ ap f q) ⬝ (p y ⬝ s) = (r ⬝ p x) ⬝ (ap g q ⬝ s) :=
  by induction s; induction q; reflexivity

  @[hott] def con_ap_con_eq_con_con_ap {f g : A → B} (p : f ~ g) {x y : A} (q : x = y)
      {w : B} (r : w = f x) :
    (r ⬝ ap f q) ⬝ p y = (r ⬝ p x) ⬝ ap g q :=
  by induction q; reflexivity

  -- TODO: try this using the simplifier, and compare proofs
  @[hott] def ap_con_con_eq_con_ap_con {f g : A → B} (p : f ~ g) {x y : A} (q : x = y)
      {z : B} (s : g y = z) :
    ap f q ⬝ (p y ⬝ s) = p x ⬝ (ap g q ⬝ s) :=
  begin
    induction s,
    induction q,
    apply idp_con
  end

  @[hott] def con_ap_con_con_eq_con_con_con {f : A → A} (p : f ~ id) {x y : A} (q : x = y)
      {w z : A} (r : w = f x) (s : y = z) :
    (r ⬝ ap f q) ⬝ (p y ⬝ s) = (r ⬝ p x) ⬝ (q ⬝ s) :=
  by induction s; induction q; reflexivity

  @[hott] def con_con_ap_con_eq_con_con_con {g : A → A} (p : @id A ~ g) {x y : A} (q : x = y)
      {w z : A} (r : w = x) (s : g y = z) :
    (r ⬝ p x) ⬝ (ap g q ⬝ s) = (r ⬝ q) ⬝ (p y ⬝ s) :=
  by induction s; induction q; reflexivity

  @[hott] def con_ap_con_eq_con_con {f : A → A} (p : f ~ id) {x y : A} (q : x = y)
      {w : A} (r : w = f x) :
    (r ⬝ ap f q) ⬝ p y = (r ⬝ p x) ⬝ q :=
  by induction q; reflexivity

  @[hott] def ap_con_con_eq_con_con {f : A → A} (p : f ~ id) {x y : A} (q : x = y)
      {z : A} (s : y = z) :
    ap f q ⬝ (p y ⬝ s) = p x ⬝ (q ⬝ s) :=
  by induction s; induction q; apply idp_con

  @[hott] def con_con_ap_eq_con_con {g : A → A} (p : @id A ~ g) {x y : A} (q : x = y)
      {w : A} (r : w = x) :
    (r ⬝ p x) ⬝ ap g q = (r ⬝ q) ⬝ p y :=
  begin induction q, exact idp end

  @[hott] def con_ap_con_eq_con_con' {g : A → A} (p : @id A ~ g) {x y : A} (q : x = y)
      {z : A} (s : g y = z) :
    p x ⬝ (ap g q ⬝ s) = q ⬝ (p y ⬝ s) :=
  by induction s; induction q; exact !idp_con⁻¹

  /- Action of [apd10] and [ap10] on paths -/

  -- Application of paths between functions preserves the groupoid structure

  @[hott, hsimp] def apd10_idp (f : Πx, P x) (x : A) : apd10 (refl f) x = idp := idp

  @[hott] def apd10_con {f f' f'' : Πx, P x} (h : f = f') (h' : f' = f'') (x : A) :
    apd10 (h ⬝ h') x = apd10 h x ⬝ apd10 h' x :=
  by induction h; induction h'; reflexivity

  @[hott] def apd10_inv {f g : Πx : A, P x} (h : f = g) (x : A) :
    apd10 h⁻¹ x = (apd10 h x)⁻¹ :=
  by induction h; reflexivity

  @[hott, hsimp] def ap10_idp {f : A → B} (x : A) : ap10 (refl f) x = idp := idp

  @[hott] def ap10_con {f f' f'' : A → B} (h : f = f') (h' : f' = f'') (x : A) :
  ap10 (h ⬝ h') x = ap10 h x ⬝ ap10 h' x := apd10_con h h' x

  @[hott] def ap10_inv {f g : A → B} (h : f = g) (x : A) : ap10 h⁻¹ x = (ap10 h x)⁻¹ :=
  apd10_inv h x

  -- [ap10] also behaves nicely on paths produced by [ap]
  @[hott] def ap_ap10 (f g : A → B) (h : B → C) (p : f = g) (a : A) :
    ap h (ap10 p a) = ap10 (ap (λ f', h ∘ f') p) a:=
  by induction p; reflexivity

  /- some lemma's about ap011 -/

  @[hott] def ap_eq_ap011_left (f : A → B → C) (Ha : a = a') (b : B) :
    ap (λa, f a b) Ha = ap011 f Ha idp :=
  by induction Ha; reflexivity

  @[hott] def ap_eq_ap011_right (f : A → B → C) (a : A) (Hb : b = b') :
    ap (f a) Hb = ap011 f idp Hb :=
  by reflexivity

  @[hott] def ap_ap011 {A B C D : Type _} (g : C → D) (f : A → B → C) {a a' : A} {b b' : B}
    (p : a = a') (q : b = b') : ap g (ap011 f p q) = ap011 (λa b, g (f a b)) p q :=
  begin
    induction p, exact (ap_compose g (f a) q)⁻¹
  end


  /- Transport and the groupoid structure of paths -/

  @[hott, hsimp] def idp_tr {P : A → Type u} {x : A} (u : P x) : idp ▸ u = u := idp

  @[hott, hsimp] def idp_tr' {P : A → Type u} {x : A} : transport P (@idp _ x) = id := idp
  @[hott, hsimp] def idp_tr'' {P : A → Type u} {x : A} : transport P (@refl _ x) = id := idp

  @[hott] def con_tr  {P : A → Type w} {x y z : A} (p : x = y) (q : y = z) (u : P x) :
    p ⬝ q ▸ u = q ▸ p ▸ u :=
  by induction q; reflexivity

  @[hott, hsimp] def tr_inv_tr {P : A → Type v} {x y : A} (p : x = y) (z : P y) :
    p ▸ p⁻¹ ▸ z = z :=
  (con_tr p⁻¹ p z)⁻¹ ⬝ ap (λr, transport P r z) (con.left_inv p)

  @[hott, hsimp] def inv_tr_tr {P : A → Type v} {x y : A} (p : x = y) (z : P x) :
    p⁻¹ ▸ p ▸ z = z :=
  (con_tr p p⁻¹ z)⁻¹ ⬝ ap (λr, transport P r z) (con.right_inv p)

  @[hott] def cast_cast_inv {A : Type u} {P : A → Type u} {x y : A} (p : x = y) (z : P y) :
    cast (ap P p) (cast (ap P p⁻¹) z) = z :=
  by induction p; reflexivity

  @[hott] def cast_inv_cast {A : Type u} {P : A → Type u} {x y : A} (p : x = y) (z : P x) :
    cast (ap P p⁻¹) (cast (ap P p) z) = z :=
  by induction p; reflexivity

  @[hott] def fn_tr_eq_tr_fn {P Q : A → Type _} {x y : A} (p : x = y) (f : Πx, P x → Q x) (z : P x) :
    f y (p ▸ z) = p ▸ f x z :=
  by induction p; reflexivity

  @[hott] def fn_cast_eq_cast_fn {A : Type _} {P Q : A → Type _} {x y : A} (p : x = y)
    (f : Πx, P x → Q x) (z : P x) : f y (cast (ap P p) z) = cast (ap Q p) (f x z) :=
  by induction p; reflexivity

  @[hott] def con_con_tr {P : A → Type u}
      {x y z w : A} (p : x = y) (q : y = z) (r : z = w) (u : P x) :
    (ap (λe, e ▸ u) (con.assoc' p q r): _) ⬝ (con_tr (p ⬝ q) r u) ⬝
        ap (transport P r) (con_tr p q u)
      = (con_tr p (q ⬝ r) u) ⬝ (con_tr q r (p ▸ u))
      :> ((p ⬝ (q ⬝ r)) ▸ u = r ▸ q ▸ p ▸ u) :=
  by induction r; induction q; induction p; reflexivity

  --  Here is another coherence lemma for transport.
  @[hott] def tr_inv_tr_lemma {P : A → Type v} {x y : A} (p : x = y) (z : P x) :
    tr_inv_tr p (transport P p z) = ap (transport P p) (inv_tr_tr p z) :=
  by induction p; reflexivity

  /- some properties for apdt -/

  @[hott, hsimp] def apdt_idp (x : A) (f : Πx, P x) : apdt f idp = idp :> (f x = f x) := idp

  @[hott] def apdt_con (f : Πx, P x) {x y z : A} (p : x = y) (q : y = z)
    : apdt f (p ⬝ q) = con_tr p q (f x) ⬝ ap (transport P q) (apdt f p) ⬝ apdt f q :=
  by induction p; induction q; apply idp

  @[hott] def apdt_inv (f : Πx, P x) {x y : A} (p : x = y)
    : apdt f p⁻¹ = (eq_inv_tr_of_tr_eq (apdt f p))⁻¹ :=
  by induction p; apply idp

  -- Dependent transport in a doubly dependent type.
  -- This is a special case of transporto in init.pathover
  @[hott] def transportD  {P : A → Type _} (Q : Πa, P a → Type _)
      {a a' : A} (p : a = a') (b : P a) (z : Q a b) : Q a' (p ▸ b) :=
  by induction p; exact z

  -- In Coq the variables P, Q and b are explicit, but in Lean we can probably have them implicit
  -- using the following notation
  notation p ` ▸D `:65 x:64 := transportD _ p _ x

  -- transporting over 2 one-dimensional paths
  -- This is a special case of transporto in init.pathover
  @[hott] def transport11 {A B : Type u} (P : A → B → Type v) {a a' : A} {b b' : B}
    (p : a = a') (q : b = b') (z : P a b) : P a' b' :=
  transport (P a') q (@transport _ (λ x : A, P x b) _ _ p z)

  -- Transporting along higher-dimensional paths
  @[hott] def transport2  (P : A → Type w) {x y : A} {p q : x = y} (r : p = q) (z : P x) :
    p ▸ z = q ▸ z :=
  ap (λp', p' ▸ z) r

  notation p ` ▸2 `:65 x:64 := transport2 _ p _ x

  -- An alternative definition.
  @[hott] def tr2_eq_ap10 (Q : A → Type w) {x y : A} {p q : x = y} (r : p = q) (z : Q x) :
    transport2 Q r z = ap10 (ap (transport Q) r) z :=
  by induction r; reflexivity

  @[hott] def tr2_con {P : A → Type w} {x y : A} {p1 p2 p3 : x = y}
      (r1 : p1 = p2) (r2 : p2 = p3) (z : P x) :
    transport2 P (r1 ⬝ r2) z = transport2 P r1 z ⬝ transport2 P r2 z :=
  by induction r1; induction r2; reflexivity

  @[hott] def tr2_inv (Q : A → Type w) {x y : A} {p q : x = y} (r : p = q) (z : Q x) :
    transport2 Q r⁻¹ z = (transport2 Q r z)⁻¹ :=
  by induction r; reflexivity

  @[hott] def transportD2  {B C : A → Type _} (D : Π(a:A), B a → C a → Type _)
    {x1 x2 : A} (p : x1 = x2) (y : B x1) (z : C x1) (w : D x1 y z) : D x2 (p ▸ y) (p ▸ z) :=
  by induction p; exact w

  notation p ` ▸D2 `:65 x:64 := transportD2 _ p _ _ x

  @[hott] def ap_tr_con_tr2 (P : A → Type _) {x y : A} {p q : x = y} {z w : P x} (r : p = q)
      (s : z = w) :
    ap (transport P p) s  ⬝  transport2 P r w = transport2 P r z  ⬝  ap (transport P q) s :=
  by induction r; exact !idp_con⁻¹

  /- Transporting in particular fibrations -/

  /-
  From the Coq HoTT library:

  One frequently needs lemmas showing that transport in a certain dependent type is equal to some
  more explicitly defined operation, defined according to the structure of that dependent type.
  For most dependent types, we prove these lemmas in the appropriate file in the types/
  subdirectory.  Here we consider only the most basic cases.
  -/

  -- Transporting in a constant fibration.
  @[hott] def tr_constant (p : x = y) (z : B) : transport (λx, B) p z = z :=
  by induction p; reflexivity

  @[hott] def tr2_constant {p q : x = y} (r : p = q) (z : B) :
    tr_constant p z = transport2 (λu, B) r z ⬝ tr_constant q z :=
  by induction r; exact !idp_con⁻¹

  -- Transporting in a pulled back fibration.
  @[hott] def tr_compose (P : B → Type _) (f : A → B) (p : x = y) (z : P (f x)) :
    transport (P ∘ f) p z  = (transport P (ap f p) z : _) :=
  by induction p; reflexivity

  @[hott] def tr_ap (P : B → Type _) (f : A → B) (p : x = y) (z : P (f x)) :
    transport P (ap f p) z = (transport (P ∘ f) p z: _) :=
  (tr_compose P f p z)⁻¹

  @[hott] def ap_precompose (f : A → B) (g g' : B → C) (p : g = g') :
    ap (λh : B → C, h ∘ f) p = (transport (λh : B → C, g ∘ f = h ∘ f) p idp: _) :=
  by induction p; reflexivity

  @[hott] def apd10_ap_precompose (f : A → B) (g g' : B → C) (p : g = g') :
    apd10 (ap (λh : B → C, h ∘ f) p) = λa, (apd10 p (f a): _) :=
  by induction p; reflexivity

  @[hott] def apd10_ap_precompose_dependent {C : B → Type _}
    (f : A → B) {g g' : Πb : B, C b} (p : g = g')
    : apd10 (ap (λ(h : (Πb : B, C b))(a : A), h (f a)) p) = λa, (apd10 p (f a): _) :=
  by induction p; reflexivity

  @[hott] def apd10_ap_postcompose (f : B → C) (g g' : A → B) (p : g = g') :
    apd10 (ap (λh : A → B, f ∘ h) p) = λa, ap f (apd10 p a) :=
  by induction p; reflexivity

  -- A special case of [tr_compose] which seems to come up a lot.
  @[hott] def tr_eq_cast_ap {P : A → Type _} {x y} (p : x = y) (u : P x) : p ▸ u = cast (ap P p) u :=
  by induction p; reflexivity

  @[hott] def tr_eq_cast_ap_fn {P : A → Type _} {x y} (p : x = y) : transport P p = cast (ap P p) :=
  by induction p; reflexivity

  /- The behavior of [ap] and [apdt] -/

  -- In a constant fibration, [apdt] reduces to [ap], modulo [transport_const].
  @[hott] def apdt_eq_tr_constant_con_ap (f : A → B) (p : x = y) :
    apdt f p = tr_constant p (f x) ⬝ ap f p :=
  by induction p; reflexivity


  /- The 2-dimensional groupoid structure -/

  -- Horizontal composition of 2-dimensional paths.
  @[hott] def concat2  {p p' : x = y} {q q' : y = z} (h : p = p') (h' : q = q')
    : p ⬝ q = p' ⬝ q' :=
  ap011 concat h h'

  -- 2-dimensional path inversion
  @[hott] def inverse2  {p q : x = y} (h : p = q) : p⁻¹ = q⁻¹ :=
  ap inverse h

  infixl ` ◾ `:80 := concat2
  postfix [parsing_only] `⁻²`:(max+10) := inverse2 --this notation is abusive, should we use it?

  /- Whiskering -/

  @[hott] def whisker_left  (p : x = y) {q r : y = z} (h : q = r) : p ⬝ q = p ⬝ r :=
  idp ◾ h

  @[hott] def whisker_right  {p q : x = y} (r : y = z) (h : p = q) : p ⬝ r = q ⬝ r :=
  h ◾ idp

  -- Unwhiskering, a.k.a. cancelling

  @[hott] def cancel_left {x y z : A} (p : x = y) {q r : y = z} : (p ⬝ q = p ⬝ r) → (q = r) :=
  λs, (inv_con_cancel_left _ _)⁻¹ ⬝ whisker_left p⁻¹ s ⬝ inv_con_cancel_left _ _

  @[hott] def cancel_right {x y z : A} {p q : x = y} (r : y = z) : (p ⬝ r = q ⬝ r) → (p = q) :=
  λs, (con_inv_cancel_right _ _)⁻¹ ⬝ whisker_right r⁻¹ s ⬝ con_inv_cancel_right _ _

  -- Whiskering and identity paths.

  @[hott, hsimp] def whisker_right_idp {p q : x = y} (h : p = q) :
    whisker_right idp h = h :=
  by induction h; induction p; reflexivity

  @[hott, hsimp] def whisker_right_idp_left  (p : x = y) (q : y = z) :
    whisker_right q idp = idp :> (p ⬝ q = p ⬝ q) :=
  idp

  @[hott, hsimp] def whisker_left_idp_right  (p : x = y) (q : y = z) :
    whisker_left p idp = idp :> (p ⬝ q = p ⬝ q) :=
  idp

  @[hott, hsimp] def whisker_left_idp {p q : x = y} (h : p = q) :
    (idp_con p)⁻¹ ⬝ whisker_left idp h ⬝ idp_con q = h :=
  by induction h; induction p; reflexivity

  @[hott, hsimp] def whisker_left_idp2 {A : Type u} {a : A} (p : idp = idp :> a = a) :
    whisker_left idp p = p :=
  begin
    refine _ ⬝ whisker_left_idp p,
    exact !idp_con⁻¹
  end

  @[hott] def con2_idp  {p q : x = y} (h : p = q) :
    h ◾ idp = whisker_right idp h :> (p ⬝ idp = q ⬝ idp) :=
  idp

  @[hott] def idp_con2  {p q : x = y} (h : p = q) :
    idp ◾ h = whisker_left idp h :> (idp ⬝ p = idp ⬝ q) :=
  idp

  @[hott] def inv2_con2 {p p' : x = y} (h : p = p')
    : h⁻² ◾ h = con.left_inv p ⬝ (con.left_inv p')⁻¹ :=
  by induction h; induction p; reflexivity

  -- The interchange law for concatenation.
  @[hott] def con2_con_con2 {p p' p'' : x = y} {q q' q'' : y = z}
      (a : p = p') (b : p' = p'') (c : q = q') (d : q' = q'') :
    a ◾ c ⬝ b ◾ d = (a ⬝ b) ◾ (c ⬝ d) :=
  by induction d; induction c; induction b;induction a; reflexivity

  @[hott] def con2_eq_rl {A : Type _} {x y z : A} {p p' : x = y} {q q' : y = z}
    (a : p = p') (b : q = q') : a ◾ b = whisker_right q a ⬝ whisker_left p' b :=
  by induction b; induction a; reflexivity

  @[hott] def con2_eq_lf {A : Type _} {x y z : A} {p p' : x = y} {q q' : y = z}
    (a : p = p') (b : q = q') : a ◾ b = whisker_left p b ⬝ whisker_right q' a :=
  by induction b; induction a; reflexivity

  @[hott] def whisker_right_con_whisker_left {x y z : A} {p p' : x = y} {q q' : y = z}
    (a : p = p') (b : q = q') :
    (whisker_right q a) ⬝ (whisker_left p' b) = (whisker_left p b) ⬝ (whisker_right q' a) :=
  by induction b; induction a; reflexivity

  -- Structure corresponding to the coherence equations of a bicategory.

  -- The "pentagonator": the 3-cell witnessing the associativity pentagon.
  @[hott] def pentagon {v w x y z : A} (p : v = w) (q : w = x) (r : x = y) (s : y = z) :
    whisker_left p (con.assoc' q r s)
      ⬝ con.assoc' p (q ⬝ r) s
      ⬝ whisker_right s (con.assoc' p q r)
    = con.assoc' p q (r ⬝ s) ⬝ con.assoc' (p ⬝ q) r s :=
  by induction s;induction r;induction q;induction p;reflexivity

  -- The 3-cell witnessing the left unit triangle.
  @[hott] def triangulator (p : x = y) (q : y = z) :
    con.assoc' p idp q ⬝ whisker_right q (con_idp p) = whisker_left p (idp_con q) :=
  by induction q; induction p; reflexivity

  @[hott] def eckmann_hilton (p q : idp = idp :> a = a) : p ⬝ q = q ⬝ p :=
  begin
    refine (whisker_right_idp p ◾ whisker_left_idp2 q)⁻¹ᵖ ⬝ _,
    refine whisker_right_con_whisker_left _ _ ⬝ _,
    refine whisker_left_idp2 _ ◾ whisker_right_idp _
  end

  @[hott] def con_eq_con2 (p q : idp = idp :> a = a) : p ⬝ q = p ◾ q :=
  begin
    refine (whisker_right_idp p ◾ whisker_left_idp2 q)⁻¹ᵖ ⬝ _,
    symmetry,
    exact con2_eq_rl _ _
  end

  @[hott] def inv_eq_inv2 (p : idp = idp :> a = a) : p⁻¹ = p⁻² :=
  begin
    apply eq.cancel_right p,
    refine con.left_inv _ ⬝ _,
    refine _ ⬝ (con_eq_con2 _ _)⁻¹,
    exact (inv2_con2 _)⁻¹ᵖ,
  end

  -- The action of functions on 2-dimensional paths
  @[hott] def ap02 (f : A → B) {x y : A} {p q : x = y} (r : p = q)
    : ap f p = ap f q :=
  ap (ap f) r

  @[hott] def ap02_con (f : A → B) {x y : A} {p p' p'' : x = y} (r : p = p') (r' : p' = p'') :
    ap02 f (r ⬝ r') = ap02 f r ⬝ ap02 f r' :=
  by induction r; induction r'; reflexivity

  @[hott] def ap02_con2 (f : A → B) {x y z : A} {p p' : x = y} {q q' :y = z} (r : p = p')
    (s : q = q') :
      ap02 f (r ◾ s) = ap_con f p q
                        ⬝ (ap02 f r ◾ ap02 f s)
                        ⬝ (ap_con f p' q')⁻¹ :=
  by induction r; induction s; induction q; induction p; reflexivity

  @[hott] def apdt02  {p q : x = y} (f : Π x, P x) (r : p = q) :
    apdt f p = transport2 P r (f x) ⬝ apdt f q :=
  by induction r; exact !idp_con⁻¹

end eq

/-
  an auxillary namespace for concatenation and inversion for homotopies. We put this is a separate
  namespace because ⁻¹ʰ is also used as the inverse of a homomorphism
-/

open eq
namespace homotopy
  infix ` ⬝h `:75 := hott.eq.homotopy.trans
  postfix `⁻¹ʰ`:(max+1) := hott.eq.homotopy.symm
end homotopy

end hott
