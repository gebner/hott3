/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura

Hedberg's Theorem: every type with decidable equality is a set
-/
import .trunc .logic

universes u v w
hott_theory

namespace hott
open eq nat is_trunc sigma

-- TODO(Leo): move const coll and path_coll to a different file?
@[hott] private def const {A : Type u} {B : Type v} (f : A → B) := ∀ x y, f x = f y
@[hott] private def coll (A : Type u) := Σ f : A → A, const f
@[hott] private def path_coll (A : Type u) := ∀ x y : A, coll (x = y)

section
  variables {A : Type u} [h : decidable_eq A] {x y : A}
  include h

  -- TODO(gabriel): can't make private because otherwise dsimp fails
  @[hott, reducible] def pc : path_coll A | a b :=
  hott.dite (a = b)
    (λp, ⟨(λ _, p), λ q r, idp⟩)
    (λp, ⟨id,       λ q r, absurd q p⟩)

  @[hott, reducible] private def f : x = y → x = y :=
  (pc x y).fst

  @[hott] private def f_const (p q : x = y) : f p = f q :=
  begin
    dsimp [f],
    induction pc x y with f c,
    apply c,
  end

  @[hott] private def aux (p : x = y) : p = (f (refl x))⁻¹ ⬝ (f p) :=
  by induction p; rwr eq.con.left_inv

  @[hott, instance] def is_set_of_decidable_eq : is_set A :=
  begin
    apply is_set.mk A; intros x y p q,
    rwr [aux p, aux q, f_const p q],
  end
end

end hott