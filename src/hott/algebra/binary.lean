/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad

General properties of binary operations.
-/

import ..init
universes u v w
hott_theory

namespace hott
open function
namespace binary
section
variable {A : Type _}
variables (op₁ : A → A → A) (inv : A → A) (one : A)

local notation a * b := op₁ a b
local notation a ⁻¹  := inv a

@[hott] def commutative        := Πa b, a * b = b * a
@[hott] def associative        := Πa b c, (a * b) * c = a * (b * c)
@[hott] def left_identity      := Πa, one * a = a
@[hott] def right_identity     := Πa, a * one = a
@[hott] def left_inverse       := Πa, a⁻¹ * a = one
@[hott] def right_inverse      := Πa, a * a⁻¹ = one
@[hott] def left_cancelative   := Πa b c, a * b = a * c → b = c
@[hott] def right_cancelative  := Πa b c, a * b = c * b → a = c

@[hott] def inv_op_cancel_left  := Πa b, a⁻¹ * (a * b) = b
@[hott] def op_inv_cancel_left  := Πa b, a * (a⁻¹ * b) = b
@[hott] def inv_op_cancel_right  := Πa b, a * b⁻¹ * b =  a
@[hott] def op_inv_cancel_right  := Πa b, a * b * b⁻¹ = a

variable (op₂ : A → A → A)

local notation a + b := op₂ a b

@[hott] def left_distributive  := Πa b c, a * (b + c) = a * b + a * c
@[hott] def right_distributive  := Πa b c, (a + b) * c = a * c + b * c

@[hott] def right_commutative  {B : Type _} (f : B → A → B) :=
Π b a₁ a₂, f (f b a₁) a₂ = f (f b a₂) a₁
@[hott] def left_commutative  {B : Type _}  (f : A → B → B) :=
Π a₁ a₂ b, f a₁ (f a₂ b) = f a₂ (f a₁ b)
end

section
variable {A : Type _}
variable {f : A → A → A}
variable H_comm : commutative f
variable H_assoc : associative f
local infixl `*` := f
@[hott] theorem left_comm : left_commutative f :=
λ a b c, calc
  a*(b*c) = (a*b)*c  : (H_assoc _ _ _)⁻¹
    ...   = (b*a)*c  : ap (λ x, x*c) (H_comm _ _)
    ...   = b*(a*c)  : H_assoc _ _ _

@[hott] theorem right_comm : right_commutative f :=
λ a b c, calc
  (a*b)*c = a*(b*c) : H_assoc _ _ _
    ...   = a*(c*b) : ap (λ x, a*x) (H_comm _ _)
    ...   = (a*c)*b : (H_assoc _ _ _)⁻¹

@[hott] theorem comm4 (a b c d : A) : a*b*(c*d) = a*c*(b*d) :=
calc
  a*b*(c*d) = a*b*c*d   : (H_assoc _ _ _)⁻¹
    ...     = a*c*b*d   : ap (λx, x*d) (right_comm H_comm H_assoc _ _ _)
    ...     = a*c*(b*d) : H_assoc _ _ _
end

section
variable {A : Type _}
variable {f : A → A → A}
variable H_assoc : associative f
local infixl `*` := f
@[hott] theorem assoc4helper (a b c d) : (a*b)*(c*d) = a*((b*c)*d) :=
calc
  (a*b)*(c*d) = a*(b*(c*d)) : H_assoc _ _ _
          ... = a*((b*c)*d) : ap (λ x, a*x) (H_assoc _ _ _)⁻¹ᵖ
end

@[hott] def right_commutative_compose_right
  {A B : Type _} (f : A → A → A) (g : B → A) (rcomm : right_commutative f) : right_commutative (compose_right f g) :=
λ a b₁ b₂, (rcomm _ _ _)

@[hott] def left_commutative_compose_left
  {A B : Type _} (f : A → A → A) (g : B → A) (lcomm : left_commutative f) : left_commutative (compose_left f g) :=
λ a b₁ b₂, (lcomm _ _ _)
end binary

open eq
namespace is_equiv
@[hott] def inv_preserve_binary {A B : Type _} (f : A → B) [H : is_equiv f]
  (mA : A → A → A) (mB : B → B → B) (H : Π(a a' : A), f (mA a a') = mB (f a) (f a'))
  (b b' : B) : f⁻¹ᶠ (mB b b') = mA (f⁻¹ᶠ b) (f⁻¹ᶠ b') :=
begin
  have H2 : f⁻¹ᶠ (mB (f (f⁻¹ᶠ b)) (f (f⁻¹ᶠ b'))) = f⁻¹ᶠ (f (mA (f⁻¹ᶠ b) (f⁻¹ᶠ b'))), from
  ap f⁻¹ᶠ (H _ _)⁻¹ᵖ,
  rwr [right_inv f, right_inv f, left_inv f] at H2, rwr H2
end

@[hott] def preserve_binary_of_inv_preserve {A B : Type _} (f : A → B) [H : is_equiv f]
  (mA : A → A → A) (mB : B → B → B) (H : Π(b b' : B), f⁻¹ᶠ (mB b b') = mA (f⁻¹ᶠ b) (f⁻¹ᶠ b'))
  (a a' : A) : f (mA a a') = mB (f a) (f a') :=
begin
  have H2 : f (mA (f⁻¹ᶠ (f a)) (f⁻¹ᶠ (f a'))) = f (f⁻¹ᶠ (mB (f a) (f a'))), from ap f (H _ _)⁻¹ᵖ,
  rwr [right_inv f, left_inv f, left_inv f] at H2, rwr H2
end
end is_equiv
namespace equiv
open hott.is_equiv
@[hott] def inv_preserve_binary {A B : Type _} (f : A ≃ B)
  (mA : A → A → A) (mB : B → B → B) (H : Π(a a' : A), f (mA a a') = mB (f a) (f a'))
  (b b' : B) : f⁻¹ᶠ (mB b b') = mA (f⁻¹ᶠ b) (f⁻¹ᶠ b') :=
inv_preserve_binary f mA mB H b b'

@[hott] def preserve_binary_of_inv_preserve {A B : Type _} (f : A ≃ B)
  (mA : A → A → A) (mB : B → B → B) (H : Π(b b' : B), f⁻¹ᶠ (mB b b') = mA (f⁻¹ᶠ b) (f⁻¹ᶠ b'))
  (a a' : A) : f (mA a a') = mB (f a) (f a') :=
preserve_binary_of_inv_preserve f mA mB H a a'
end equiv
end hott
