/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jeremy Avigad

General properties of relations, and classes for equivalence relations and congruences.
-/

import ..init
universes u v w
hott_theory
namespace hott
set_option old_structure_cmd true
namespace relation

/- properties of binary relations -/

section
  variables {T : Type _} (R : T → T → Type _)

  @[hott] def reflexive : Type _ := Πx, R x x
  @[hott] def symmetric : Type _ := Π⦃x y⦄, R x y → R y x
  @[hott] def transitive : Type _ := Π⦃x y z⦄, R x y → R y z → R x z
end


/- classes for equivalence relations -/

@[hott, class] structure is_reflexive {T : Type _} (R : T → T → Type _) := (refl : reflexive R)
@[hott, class] structure is_symmetric {T : Type _} (R : T → T → Type _) := (symm : symmetric R)
@[hott, class] structure is_transitive {T : Type _} (R : T → T → Type _) := (trans : transitive R)

@[hott, class] structure is_equivalence {T : Type _} (R : T → T → Type _)
extends is_reflexive R, is_symmetric R, is_transitive R

-- partial equivalence relation
@[hott, class] structure is_PER {T : Type _} (R : T → T → Type _) extends is_symmetric R, is_transitive R

-- Generic notation. For example, is_refl R is the reflexivity of R, if that can be
-- inferred by type class inference
section
  variables {T : Type _} (R : T → T → Type _)
  @[hott] def rel_refl [C : is_reflexive R] := is_reflexive.refl R
  @[hott] def rel_symm [C : is_symmetric R] := is_symmetric.symm R
  @[hott] def rel_trans [C : is_transitive R] := is_transitive.trans R
end


/- classes for unary and binary congruences with respect to arbitrary relations -/

@[hott, class] structure is_congruence
  {T1 : Type _} (R1 : T1 → T1 → Type _)
  {T2 : Type _} (R2 : T2 → T2 → Type _)
  (f : T1 → T2) :=
(congr : Π⦃x y⦄, R1 x y → R2 (f x) (f y))

@[hott, class] structure is_congruence2
  {T1 : Type _} (R1 : T1 → T1 → Type _)
  {T2 : Type _} (R2 : T2 → T2 → Type _)
  {T3 : Type _} (R3 : T3 → T3 → Type _)
  (f : T1 → T2 → T3) :=
(congr2 : Π{x1 y1 : T1} {x2 y2 : T2}, R1 x1 y1 → R2 x2 y2 → R3 (f x1 x2) (f y1 y2))

namespace is_congruence

  -- makes the type class explicit
  @[hott] def app {T1 : Type _} {R1 : T1 → T1 → Type _} {T2 : Type _} {R2 : T2 → T2 → Type _}
      {f : T1 → T2} (C : is_congruence R1 R2 f) : Π⦃x y : T1⦄, R1 x y → R2 (f x) (f y) :=
  C.congr

  @[hott] def app2 {T1 : Type _} {R1 : T1 → T1 → Type _} {T2 : Type _} {R2 : T2 → T2 → Type _}
      {T3 : Type _} {R3 : T3 → T3 → Type _}
      {f : T1 → T2 → T3} (C : is_congruence2 R1 R2 R3 f) : Π⦃x1 y1 : T1⦄ ⦃x2 y2 : T2⦄,
    R1 x1 y1 → R2 x2 y2 → R3 (f x1 x2) (f y1 y2) :=
  C.congr2

  /- tools to build instances -/

  @[hott] def compose
      {T2 : Type _} {R2 : T2 → T2 → Type _}
      {T3 : Type _} {R3 : T3 → T3 → Type _}
      {g : T2 → T3} (C2 : is_congruence R2 R3 g)
      ⦃T1 : Type _⦄ {R1 : T1 → T1 → Type _}
      {f : T1 → T2} [C1 : is_congruence R1 R2 f] :
    is_congruence R1 R3 (λx, g (f x)) :=
  is_congruence.mk (λx1 x2 H, app C2 (app C1 H))

  @[hott] def compose21
      {T2 : Type _} {R2 : T2 → T2 → Type _}
      {T3 : Type _} {R3 : T3 → T3 → Type _}
      {T4 : Type _} {R4 : T4 → T4 → Type _}
      {g : T2 → T3 → T4} (C3 : is_congruence2 R2 R3 R4 g)
      ⦃T1 : Type _⦄ {R1 : T1 → T1 → Type _}
      {f1 : T1 → T2} [C1 : is_congruence R1 R2 f1]
      {f2 : T1 → T3} [C2 : is_congruence R1 R3 f2] :
    is_congruence R1 R4 (λx, g (f1 x) (f2 x)) :=
  is_congruence.mk (λx1 x2 H, app2 C3 (app C1 H) (app C2 H))

  @[hott] def const {T2 : Type _} (R2 : T2 → T2 → Type _) (H : relation.reflexive R2)
      ⦃T1 : Type _⦄ (R1 : T1 → T1 → Type _) (c : T2) :
    is_congruence R1 R2 (λu : T1, c) :=
  is_congruence.mk (λx y H1, H c)

end is_congruence

@[hott, instance] def congruence_const {T2 : Type _} (R2 : T2 → T2 → Type _)
    [C : is_reflexive R2] ⦃T1 : Type _⦄ (R1 : T1 → T1 → Type _) (c : T2) :
  is_congruence R1 R2 (λu : T1, c) :=
is_congruence.const R2 (is_reflexive.refl R2) R1 c

@[hott, instance] def congruence_star {T : Type _} (R : T → T → Type _) :
  is_congruence R R (λu, u) :=
is_congruence.mk (λx y H, H)


/- relations that can be coerced to functions / implications-/

@[hott, class] structure mp_like (R : Type _ → Type _ → Type _) :=
(app : Π{a b : Type _}, R a b → (a → b))

@[hott] def rel_mp (R : Type _ → Type _ → Type _) [C : mp_like R] {a b : Type _} (H : R a b) :=
mp_like.app H


end relation
end hott
