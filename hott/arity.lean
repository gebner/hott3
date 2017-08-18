/-
Copyright (c) 2014 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Floris van Doorn

Theorems about functions with multiple arguments
-/
import hott.init

universes u v w
hott_theory

namespace hott

variables {A : Type _} {U : Type _} {V : Type _} {W : Type _}
          {X : Type _} {Y : Type _} {Z : Type _}
          {B : A → Type _} {C : Πa, B a → Type _} {D : Πa b, C a b → Type _}
          {E : Πa b c, D a b c → Type _} {F : Πa b c d, E a b c d → Type _}
          {G : Πa b c d e, F a b c d e → Type _} {H : Πa b c d e f, G a b c d e f → Type _}
variables {a a' : A} {u u' : U} {v v' : V} {w w' : W} {x x' x'' : X} {y y' : Y} {z z' : Z}
          {b : B a} {b' : B a'}
          {c : C a b} {c' : C a' b'}
          {d : D a b c} {d' : D a' b' c'}
          {e : E a b c d} {e' : E a' b' c' d'}
         {ff : F a b c d e} {f' : F a' b' c' d' e'}
          {g : G a b c d e ff} {g' : G a' b' c' d' e' f'}
          {h : H a b c d e ff g} {h' : H a' b' c' d' e' f' g'}

namespace eq
  /-
    Naming convention:
      The theorem which states how to construct an path between two function applications is
        api₀i₁...iₙ.
      Here i₀, ... iₙ are digits, n is the arity of the function(s),
        and iⱼ specifies the dimension of the path between the jᵗʰ argument
        (i₀ specifies the dimension of the path between the functions).
      A value iⱼ ≡ 0 means that the jᵗʰ arguments are definitionaly equal
      The functions are non-dependent, except when the theorem name contains trailing zeroes
        (where the function is dependent only in the arguments where it doesn't result in any
         transports in the theorem statement).
      For the fully-dependent versions (except that the conclusion doesn't contain a transport)
      we write
        apdi₀i₁...iₙ.

      For versions where only some arguments depend on some other arguments,
      or for versions with transport in the conclusion (like apdt), we don't have a
      consistent naming scheme (yet).

      We don't prove each theorem systematically, but prove only the ones which we actually need.
  -/

  @[hott, reducible] def homotopy2 (f g : Πa b, C a b)         : Type _ :=
  Πa b, f a b = g a b
  @[hott, reducible] def homotopy3 (f g : Πa b c, D a b c)     : Type _ :=
  Πa b c, f a b c = g a b c
  @[hott, reducible] def homotopy4 (f g : Πa b c d, E a b c d) : Type _ :=
  Πa b c d, f a b c d = g a b c d

  infix ` ~2 `:50 := homotopy2
  infix ` ~3 `:50 := homotopy3
  infix ` ~4 `:50 := homotopy4

  @[refl] def homotopy2.refl (f : Π a b, C a b) : f ~2 f := by intros _ _; refl
  @[refl] def homotopy3.refl (f : Π a b c, D a b c) : f ~3 f := by intros _ _ _; refl
  @[refl] def homotopy4.refl (f : Π a b c d, E a b c d) : f ~4 f := by intros _ _ _ _; refl

  @[hott] def ap0111 (f : U → V → W → X) (Hu : u = u') (Hv : v = v') (Hw : w = w')
      : f u v w = f u' v' w' :=
  by induction Hu; hsimp *

  @[hott] def ap01111 (f : U → V → W → X → Y)
    (Hu : u = u') (Hv : v = v') (Hw : w = w') (Hx : x = x')
      : f u v w x = f u' v' w' x' :=
  by induction Hu; hsimp *

  @[hott] def ap011111 (f : U → V → W → X → Y → Z)
    (Hu : u = u') (Hv : v = v') (Hw : w = w') (Hx : x = x') (Hy : y = y')
      : f u v w x y = f u' v' w' x' y' :=
  by induction Hu; hsimp *

  @[hott] def ap0111111 (f : U → V → W → X → Y → Z → A)
    (Hu : u = u') (Hv : v = v') (Hw : w = w') (Hx : x = x') (Hy : y = y') (Hz : z = z')
      : f u v w x y z = f u' v' w' x' y' z' :=
  by induction Hu; hsimp *

  @[hott] def ap010 (f : X → Πa, B a) (Hx : x = x') : f x ~ f x' :=
  λ b, ap (λa, f a b) Hx

  @[hott] def ap0100 (f : X → Πa b, C a b) (Hx : x = x') : f x ~2 f x' :=
  by intros; induction Hx; reflexivity

  @[hott] def ap01000 (f : X → Πa b c, D a b c) (Hx : x = x') : f x ~3 f x' :=
  by intros; induction Hx; reflexivity

  @[hott] def apdt011 (f : Πa, B a → Z) (Ha : a = a') (Hb : transport B Ha b = b')
      : f a b = f a' b' :=
  by induction Ha; induction Hb; reflexivity

  @[hott] def apdt0111 (f : Πa b, C a b → Z) (Ha : a = a') (Hb : transport B Ha b = b')
    (Hc : cast (apdt011 C Ha Hb) c = c')
      : f a b c = f a' b' c' :=
  by induction Ha; induction Hb; induction Hc; reflexivity

  @[hott] def apdt01111 (f : Πa b c, D a b c → Z) (Ha : a = a') (Hb : transport B Ha b = b')
    (Hc : cast (apdt011 C Ha Hb) c = c') (Hd : cast (apdt0111 D Ha Hb Hc) d = d')
      : f a b c d = f a' b' c' d' :=
  by induction Ha; induction Hb; induction Hc; induction Hd; reflexivity

  @[hott] def apdt011111 (f : Πa b c d, E a b c d → Z) (Ha : a = a') (Hb : transport B Ha b = b')
    (Hc : cast (apdt011 C Ha Hb) c = c') (Hd : cast (apdt0111 D Ha Hb Hc) d = d')
    (He : cast (apdt01111 E Ha Hb Hc Hd) e = e')
    : f a b c d e = f a' b' c' d' e' :=
  by induction Ha; induction Hb; induction Hc; induction Hd; induction He; reflexivity

  @[hott] def apdt0111111 (f : Πa b c d e, F a b c d e → Z) (Ha : a = a') (Hb : transport B Ha b = b')
    (Hc : cast (apdt011 C Ha Hb) c = c') (Hd : cast (apdt0111 D Ha Hb Hc) d = d')
    (He : cast (apdt01111 E Ha Hb Hc Hd) e = e') (Hf : cast (apdt011111 F Ha Hb Hc Hd He) ff = f')
    : f a b c d e ff = f a' b' c' d' e' f' :=
  begin induction Ha, induction Hb, induction Hc, induction Hd, induction He, induction Hf, reflexivity end

  -- @[hott] def apd0111111 (f : Πa b c d e ff, G a b c d e ff → Z) (Ha : a = a') (Hb : transport B Ha b = b')
  --   (Hc : cast (apd011 C Ha Hb) c = c') (Hd : cast (apd0111 D Ha Hb Hc) d = d')
  --   (He : cast (apd01111 E Ha Hb Hc Hd) e = e') (Hf : cast (apd011111 F Ha Hb Hc Hd He) ff = f')
  --   (Hg : cast (apd0111111 G Ha Hb Hc Hd He Hf) g = g')
  --   : f a b c d e ff g = f a' b' c' d' e' f' g' :=
  -- by induction Ha; induction Hb; induction Hc; induction Hd; induction He; induction Hf; induction Hg; reflexivity

  -- @[hott] def apd01111111 (f : Πa b c d e ff g, G a b c d e ff g → Z) (Ha : a = a') (Hb : transport B Ha b = b')
  --   (Hc : cast (apd011 C Ha Hb) c = c') (Hd : cast (apd0111 D Ha Hb Hc) d = d')
  --   (He : cast (apd01111 E Ha Hb Hc Hd) e = e') (Hf : cast (apd011111 F Ha Hb Hc Hd He) ff = f')
  --   (Hg : cast (apd0111111 G Ha Hb Hc Hd He Hf) g = g') (Hh : cast (apd01111111 H Ha Hb Hc Hd He Hf Hg) h = h')
  --   : f a b c d e ff g h = f a' b' c' d' e' f' g' h' :=
  -- by induction Ha; induction Hb; induction Hc; induction Hd; induction He; induction Hf; induction Hg; induction Hh; reflexivity

  @[hott] def apd100 {f g : Πa b, C a b} (p : f = g) : f ~2 g :=
  λa b, apd10 (apd10 p a) b

  @[hott] def apd1000 {f g : Πa b c, D a b c} (p : f = g) : f ~3 g :=
  λa b c, apd100 (apd10 p a) b c

  /- some properties of these variants of ap -/

  -- we only prove what we currently need

  @[hott] def ap010_con (f : X → Πa, B a) (p : x = x') (q : x' = x'') :
    ap010 f (p ⬝ q) a = ap010 f p a ⬝ ap010 f q a :=
  eq.rec_on q (eq.rec_on p idp)

  @[hott] def ap010_ap (f : X → Πa, B a) (g : Y → X) (p : y = y') :
    ap010 f (ap g p) a = (ap010 (f ∘ g) p: _) a :=
  eq.rec_on p idp

  @[hott] def ap_eq_ap010 {A B C : Type _} (f : A → B → C) {a a' : A} (p : a = a') (b : B) :
    ap (λa, f a b) p = ap010 f p b :=
  idp

  @[hott] def ap011_idp {A B C : Type _} (f : A → B → C) {a a' : A} (p : a = a') (b : B) :
    ap011 f p idp = ap010 f p b :=
  by reflexivity

  @[hott] def ap011_flip {A B C : Type _} (f : A → B → C) {a a' : A} {b b' : B} (p : a = a') (q : b = b') :
    ap011 f p q = (ap011 (λb a, f a b) q: _) p :=
  by induction q; induction p; reflexivity

  /- the following theorems are function extentionality for functions with multiple arguments -/

  @[hott] def eq_of_homotopy2 {f g : Πa b, C a b} (H : f ~2 g) : f = g :=
  eq_of_homotopy (λa, eq_of_homotopy (H a))

  @[hott] def eq_of_homotopy3 {f g : Πa b c, D a b c} (H : f ~3 g) : f = g :=
  eq_of_homotopy (λa, eq_of_homotopy2 (H a))

  @[hott] def eq_of_homotopy2_id (f : Πa b, C a b)
    : eq_of_homotopy2 (λa b, idpath (f a b)) = idpath f :=
  begin
    transitivity eq_of_homotopy (λ a, idpath (f a)),
      {apply (ap eq_of_homotopy), apply eq_of_homotopy, intro, apply eq_of_homotopy_idp},
      apply eq_of_homotopy_idp
  end

  @[hott] def eq_of_homotopy3_id (f : Πa b c, D a b c)
    : eq_of_homotopy3 (λa b c, idpath (f a b c)) = idpath f :=
  begin
    transitivity _,
      {apply (ap eq_of_homotopy), apply eq_of_homotopy, intro, apply eq_of_homotopy2_id},
      apply eq_of_homotopy_idp
  end

  @[hott] def eq_of_homotopy2_inv {f g : Πa b, C a b} (H : f ~2 g)
    : eq_of_homotopy2 (λa b, (H a b).inverse) = (eq_of_homotopy2 H)⁻¹ :=
  begin
    transitivity,
    {dsimp [eq_of_homotopy2], apply ap, apply eq_of_homotopy, intro, apply eq_of_homotopy_inv},
    {apply eq_of_homotopy_inv}
  end

  @[hott] def eq_of_homotopy3_inv {f g : Πa b c, D a b c} (H : f ~3 g)
    : eq_of_homotopy3 (λa b c, (H a b c).inverse) = (eq_of_homotopy3 H)⁻¹ :=
  begin
    transitivity,
    {dsimp [eq_of_homotopy3], apply ap, apply eq_of_homotopy, intro, apply eq_of_homotopy2_inv},
    {apply eq_of_homotopy_inv}
  end

  @[hott] def eq_of_homotopy2_con {f g h : Πa b, C a b} (H1 : f ~2 g) (H2 : g ~2 h)
    : eq_of_homotopy2 (λa b, H1 a b ⬝ H2 a b) = eq_of_homotopy2 H1 ⬝ eq_of_homotopy2 H2 :=
  begin
    transitivity,
    {dsimp [eq_of_homotopy2], apply ap, apply eq_of_homotopy, intro, apply eq_of_homotopy_con},
    {apply eq_of_homotopy_con}
  end

  @[hott] def eq_of_homotopy3_con {f g h : Πa b c, D a b c} (H1 : f ~3 g) (H2 : g ~3 h)
    : eq_of_homotopy3 (λa b c, H1 a b c ⬝ H2 a b c) = eq_of_homotopy3 H1 ⬝ eq_of_homotopy3 H2 :=
  begin
    transitivity,
    {dsimp [eq_of_homotopy3], apply ap, apply eq_of_homotopy, intro, apply eq_of_homotopy2_con},
    {apply eq_of_homotopy_con}
  end

end eq

open hott.eq equiv is_equiv
namespace funext
  @[hott, instance] def is_equiv_apd100 (f g : Πa b, C a b)
    : is_equiv (@apd100 A B C f g) :=
  adjointify _
             eq_of_homotopy2
             begin
               intro H, dsimp [apd100, eq_of_homotopy2],
               apply eq_of_homotopy, intro a,
               apply concat, apply (ap (λx : Π a, f a = g a, apd10 (x a))), apply (right_inv apd10),
               apply (right_inv apd10)
             end
             begin
               intro p, induction p, apply eq_of_homotopy2_id
             end

  @[hott, instance] def is_equiv_apd1000 (f g : Πa b c, D a b c)
    : is_equiv (@apd1000 A B C D f g) :=
  adjointify _
             eq_of_homotopy3
             begin
               intro H, dsimp,
               apply eq_of_homotopy, intro a,
               transitivity apd100 (eq_of_homotopy2 (H a)),
                 {apply ap (λ x : Π a, f a = g a, apd100 (x a)),
                  apply right_inv apd10},
                 apply right_inv apd100
             end
             begin
               intro p, induction p, apply eq_of_homotopy3_id
             end
end funext

namespace eq
  open funext
  local attribute [instance] funext.is_equiv_apd100
  @[hott] protected def homotopy2.rec_on {f g : Πa b, C a b} {P : (f ~2 g) → Type _}
    (p : f ~2 g) (H : Π(q : f = g), P (apd100 q)) : P p :=
  right_inv apd100 p ▸ H (eq_of_homotopy2 p)

  @[hott] protected def homotopy3.rec_on {f g : Πa b c, D a b c} {P : (f ~3 g) → Type _}
    (p : f ~3 g) (H : Π(q : f = g), P (apd1000 q)) : P p :=
  right_inv apd1000 p ▸ H (eq_of_homotopy3 p)

  @[hott] def eq_equiv_homotopy2 (f g : Πa b, C a b) : (f = g) ≃ (f ~2 g) :=
  equiv.mk apd100 (by apply_instance)

  @[hott] def eq_equiv_homotopy3 (f g : Πa b c, D a b c) : (f = g) ≃ (f ~3 g) :=
  equiv.mk apd1000 (by apply_instance)

  @[hott] def apd10_ap (f : X → Πa, B a) (p : x = x')
    : apd10 (ap f p) = ap010 f p :=
  eq.rec_on p idp

  @[hott] def eq_of_homotopy_ap010 (f : X → Πa, B a) (p : x = x')
    : eq_of_homotopy (ap010 f p) = ap f p :=
  inv_eq_of_eq (apd10_ap _ _)⁻¹

  @[hott] def ap_eq_ap_of_homotopy {f : X → Πa, B a} {p q : x = x'} (H : ap010 f p ~ ap010 f q)
    : ap f p = ap f q :=
  calc
    ap f p = eq_of_homotopy (ap010 f p) : by symmetry; apply eq_of_homotopy_ap010
       ... = eq_of_homotopy (ap010 f q) : by apply ap; apply eq_of_homotopy H
       ... = ap f q                     : by apply eq_of_homotopy_ap010

end eq

end hott