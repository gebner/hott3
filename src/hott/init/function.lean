/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura

General operations on functions.
-/
import .meta.support .path0

universes u v w
hott_theory

namespace function

@[hott] def compose_right {A B} (f : B → B → B) (g : A → B) : B → A → B :=
λ b a, f b (g a)

@[hott] def compose_left {A B} (f : B → B → B) (g : A → B) : A → B → B :=
λ a b, f (g a) b

@[hott] def dcompose {A} {B : A → Type _} {C : Π {x : A}, B x → Type _}
  (f : Π {x : A} (y : B x), C y) (g : Πx, B x) : Πx, C (g x) :=
λx, f (g x)

@[hott, class] def is_weakly_constant {A B : Type _} (f : A → B) := Π(a a' : A), f a = f a'

infixr  ` ∘' `:60        := dcompose

end function

namespace hott
export function
attribute [reducible] id
end hott