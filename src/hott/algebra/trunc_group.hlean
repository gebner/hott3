/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn

truncating an ∞-group to a group
-/

import hit.trunc algebra.bundled

open eq is_trunc trunc

namespace algebra

  section
  parameters (n : trunc_index) {A : Type _} [inf_group A]

  local abbreviation G := trunc n A

  @[hott] def trunc_mul (g h : G) : G :=
  begin
    induction g with p,
    induction h with q,
    exact tr (p * q)
  end

  @[hott] def trunc_inv (g : G) : G :=
  begin
    induction g with p,
    exact tr p⁻¹
  end

  @[hott] def trunc_one : G :=
  tr 1

  local notation 1 := trunc_one
  local postfix ⁻¹ := trunc_inv
  local infix * := trunc_mul

  @[hott] theorem trunc_mul_assoc (g₁ g₂ g₃ : G) : g₁ * g₂ * g₃ = g₁ * (g₂ * g₃) :=
  begin
    induction g₁ with p₁,
    induction g₂ with p₂,
    induction g₃ with p₃,
    exact ap tr !mul.assoc,
  end

  @[hott] theorem trunc_one_mul (g : G) : 1 * g = g :=
  begin
    induction g with p,
    exact ap tr !one_mul
  end

  @[hott] theorem trunc_mul_one (g : G) : g * 1 = g :=
  begin
    induction g with p,
    exact ap tr !mul_one
  end

  @[hott] theorem trunc_mul_left_inv (g : G) : g⁻¹ * g = 1 :=
  begin
    induction g with p,
    exact ap tr !mul.left_inv
  end

  parameter (A)
  @[hott] def trunc_inf_group [instance] : inf_group (trunc n A) :=
  ⦃inf_group,
    mul          := algebra.trunc_mul          n,
    mul_assoc    := algebra.trunc_mul_assoc    n,
    one          := algebra.trunc_one          n,
    one_mul      := algebra.trunc_one_mul      n,
    mul_one      := algebra.trunc_mul_one      n,
    inv          := algebra.trunc_inv          n,
    mul_left_inv := algebra.trunc_mul_left_inv n⦄

  @[hott] def trunc_group : group (trunc 0 A) :=
  group_of_inf_group _

  end

  section
  variables (n : trunc_index) {A : Type _} [ab_inf_group A]

  @[hott] theorem trunc_mul_comm (g h : trunc n A) : trunc_mul n g h = trunc_mul n h g :=
  begin
    induction g with p,
    induction h with q,
    exact ap tr !mul.comm
  end

  variable (A)
  @[hott] def trunc_ab_inf_group [instance] : ab_inf_group (trunc n A) :=
  ⦃ab_inf_group, trunc_inf_group n A, mul_comm := algebra.trunc_mul_comm n⦄

  @[hott] def trunc_ab_group : ab_group (trunc 0 A) :=
  ab_group_of_ab_inf_group _

  end

end algebra
