/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad

Here an "ordered_ring" is partially ordered ring, which is ordered with respect to both a weak
order and an associated strict order. Our numeric structures (int, rat, and real) will be instances
of "linear_ordered_comm_ring". This development is modeled after Isabelle's library.
-/
import .ordered_group .ring
universes u v w
hott_theory
set_option old_structure_cmd true

namespace hott
open algebra
variable {A : Type _}
namespace algebra
@[hott] private def absurd_a_lt_a {B : Type _} {a : A} [s : strict_order A] (H : a < a) : B :=
absurd H (lt.irrefl a)

/- semiring structures -/

@[hott] structure ordered_semiring (A : Type _)
  extends semiring A, ordered_mul_cancel_comm_monoid A renaming
  mul→add mul_assoc→add_assoc one→zero one_mul→zero_add mul_one→add_zero mul_comm→add_comm
  mul_left_cancel→add_left_cancel mul_right_cancel→add_right_cancel mul_le_mul_left→add_le_add_left
  mul_lt_mul_left→add_lt_add_left le_of_mul_le_mul_left→le_of_add_le_add_left
  lt_of_mul_lt_mul_left→lt_of_add_lt_add_left :=
(mul_le_mul_of_nonneg_left: Πa b c, le a b → le zero c → le (mul c a) (mul c b))
(mul_le_mul_of_nonneg_right: Πa b c, le a b → le zero c → le (mul a c) (mul b c))
(mul_lt_mul_of_pos_left: Πa b c, lt a b → lt zero c → lt (mul c a) (mul c b))
(mul_lt_mul_of_pos_right: Πa b c, lt a b → lt zero c → lt (mul a c) (mul b c))

-- /- we make it a class now (and not as part of the structure) to avoid
--   ordered_semiring.to_ordered_mul_cancel_comm_monoid to be an instance -/
attribute [class] ordered_semiring

@[hott, instance, reducible] def add_ab_group_of_ordered_semiring (A : Type _)
  [H : ordered_semiring A] : semiring A :=
@ordered_semiring.to_semiring A H

@[hott, instance, reducible] def monoid_of_ordered_semiring (A : Type _)
  [H : ordered_semiring A] : ordered_cancel_comm_monoid A :=
@ordered_semiring.to_ordered_mul_cancel_comm_monoid A H

section
  variable [s : ordered_semiring A]
  variables (a b c d e : A)
  include s

  @[hott] def mul_le_mul_of_nonneg_left {a b c : A} (Hab : a ≤ b) (Hc : 0 ≤ c) :
    c * a ≤ c * b :=
  ordered_semiring.mul_le_mul_of_nonneg_left _ _ _ _ Hab Hc

  @[hott] def mul_le_mul_of_nonneg_right {a b c : A} (Hab : a ≤ b) (Hc : 0 ≤ c) :
    a * c ≤ b * c :=
  ordered_semiring.mul_le_mul_of_nonneg_right _ _ _ _ Hab Hc

  @[hott] theorem mul_le_mul {a b c d : A} (Hac : a ≤ c) (Hbd : b ≤ d) (nn_b : 0 ≤ b)
    (nn_c : 0 ≤ c) :
    a * b ≤ c * d :=
  calc
    a * b ≤ c * b : mul_le_mul_of_nonneg_right Hac nn_b
      ... ≤ c * d : mul_le_mul_of_nonneg_left Hbd nn_c

  @[hott] theorem mul_nonneg {a b : A} (Ha : a ≥ 0) (Hb : b ≥ 0) : a * b ≥ 0 :=
  begin
    have H : 0 * b ≤ a * b, from mul_le_mul_of_nonneg_right Ha Hb,
    rwr zero_mul at H,
    exact H
  end

  @[hott] theorem mul_nonpos_of_nonneg_of_nonpos {a b : A} (Ha : a ≥ 0) (Hb : b ≤ 0) : a * b ≤ 0 :=
  begin
    have H : a * b ≤ a * 0, from mul_le_mul_of_nonneg_left Hb Ha,
    rwr mul_zero at H,
    exact H
  end

  @[hott] theorem mul_nonpos_of_nonpos_of_nonneg {a b : A} (Ha : a ≤ 0) (Hb : b ≥ 0) : a * b ≤ 0 :=
  begin
    have H : a * b ≤ 0 * b, from mul_le_mul_of_nonneg_right Ha Hb,
    rwr zero_mul at H,
    exact H
  end

  @[hott] def mul_lt_mul_of_pos_left {a b c : A} (Hab : a < b) (Hc : 0 < c) :
    c * a < c * b :=
  ordered_semiring.mul_lt_mul_of_pos_left _ _ _ _ Hab Hc

  @[hott] def mul_lt_mul_of_pos_right {a b c : A} (Hab : a < b) (Hc : 0 < c) :
    a * c < b * c :=
  ordered_semiring.mul_lt_mul_of_pos_right _ _ _ _ Hab Hc

  -- TODO: once again, there are variations
  @[hott] theorem mul_lt_mul {a b c d : A} (Hac : a < c) (Hbd : b ≤ d) (pos_b : 0 < b)
    (nn_c : 0 ≤ c) : a * b < c * d :=
  calc
    a * b < c * b : mul_lt_mul_of_pos_right Hac pos_b
      ... ≤ c * d : mul_le_mul_of_nonneg_left Hbd nn_c

  @[hott] def mul_pos {a b : A} (Ha : a > 0) (Hb : b > 0) : a * b > 0 :=
  begin
    have H : 0 * b < a * b, from mul_lt_mul_of_pos_right Ha Hb,
    rwr zero_mul at H,
    exact H
  end

  @[hott] def mul_neg_of_pos_of_neg {a b : A} (Ha : a > 0) (Hb : b < 0) : a * b < 0 :=
  begin
    have H : a * b < a * 0, from mul_lt_mul_of_pos_left Hb Ha,
    rwr mul_zero at H,
    exact H
  end

  @[hott] def mul_neg_of_neg_of_pos {a b : A} (Ha : a < 0) (Hb : b > 0) : a * b < 0 :=
  begin
    have H : a * b < 0 * b, from mul_lt_mul_of_pos_right Ha Hb,
    rwr zero_mul at  H,
    exact H
  end
end

@[hott, class] structure linear_ordered_semiring (A : Type _)
  extends ordered_semiring A, linear_strong_order_pair A :=
(zero_lt_one : lt zero one)

section
  variable [s : linear_ordered_semiring A]
  variables {a b c : A}
  include s

  @[hott] theorem zero_lt_one : 0 < (1:A) := linear_ordered_semiring.zero_lt_one A

  @[hott] theorem lt_of_mul_lt_mul_left (H : c * a < c * b) (Hc : c ≥ 0) : a < b :=
  lt_of_not_ge
    (assume H1 : b ≤ a,
      have H2 : c * b ≤ c * a, from mul_le_mul_of_nonneg_left H1 Hc,
      not_lt_of_ge H2 H)

  @[hott] theorem lt_of_mul_lt_mul_right (H : a * c < b * c) (Hc : c ≥ 0) : a < b :=
  lt_of_not_ge
    (assume H1 : b ≤ a,
      have H2 : b * c ≤ a * c, from mul_le_mul_of_nonneg_right H1 Hc,
      not_lt_of_ge H2 H)

  @[hott] theorem le_of_mul_le_mul_left (H : c * a ≤ c * b) (Hc : c > 0) : a ≤ b :=
  le_of_not_gt
    (assume H1 : b < a,
      have H2 : c * b < c * a, from mul_lt_mul_of_pos_left H1 Hc,
      not_le_of_gt H2 H)

  @[hott] theorem le_of_mul_le_mul_right (H : a * c ≤ b * c) (Hc : c > 0) : a ≤ b :=
  le_of_not_gt
    (assume H1 : b < a,
      have H2 : b * c < a * c, from mul_lt_mul_of_pos_right H1 Hc,
      not_le_of_gt H2 H)

  @[hott] theorem le_iff_mul_le_mul_left (a b : A) {c : A} (H : c > 0) : a ≤ b ↔ c * a ≤ c * b :=
  iff.intro
    (assume H', mul_le_mul_of_nonneg_left H' (le_of_lt H))
    (assume H', le_of_mul_le_mul_left H' H)

  @[hott] theorem le_iff_mul_le_mul_right (a b : A) {c : A} (H : c > 0) : a ≤ b ↔ a * c ≤ b * c :=
  iff.intro
    (assume H', mul_le_mul_of_nonneg_right H' (le_of_lt H))
    (assume H', le_of_mul_le_mul_right H' H)

  @[hott] theorem pos_of_mul_pos_left (H : 0 < a * b) (H1 : 0 ≤ a) : 0 < b :=
  lt_of_not_ge
    (assume H2 : b ≤ 0,
      have H3 : a * b ≤ 0, from mul_nonpos_of_nonneg_of_nonpos H1 H2,
      not_lt_of_ge H3 H)

  @[hott] theorem pos_of_mul_pos_right (H : 0 < a * b) (H1 : 0 ≤ b) : 0 < a :=
  lt_of_not_ge
    (assume H2 : a ≤ 0,
      have H3 : a * b ≤ 0, from mul_nonpos_of_nonpos_of_nonneg H2 H1,
      not_lt_of_ge H3 H)

  @[hott] theorem nonneg_of_mul_nonneg_left (H : 0 ≤ a * b) (H1 : 0 < a) : 0 ≤ b :=
  le_of_not_gt
    (assume H2 : b < 0,
      not_le_of_gt (mul_neg_of_pos_of_neg H1 H2) H)

  @[hott] theorem nonneg_of_mul_nonneg_right (H : 0 ≤ a * b) (H1 : 0 < b) : 0 ≤ a :=
  le_of_not_gt
    (assume H2 : a < 0,
      not_le_of_gt (mul_neg_of_neg_of_pos H2 H1) H)

  @[hott] theorem neg_of_mul_neg_left (H : a * b < 0) (H1 : 0 ≤ a) : b < 0 :=
  lt_of_not_ge
    (assume H2 : b ≥ 0,
      not_lt_of_ge (mul_nonneg H1 H2) H)

  @[hott] theorem neg_of_mul_neg_right (H : a * b < 0) (H1 : 0 ≤ b) : a < 0 :=
  lt_of_not_ge
    (assume H2 : a ≥ 0,
      not_lt_of_ge (mul_nonneg H2 H1) H)

  @[hott] theorem nonpos_of_mul_nonpos_left (H : a * b ≤ 0) (H1 : 0 < a) : b ≤ 0 :=
  le_of_not_gt
    (assume H2 : b > 0,
      not_le_of_gt (mul_pos H1 H2) H)

  @[hott] theorem nonpos_of_mul_nonpos_right (H : a * b ≤ 0) (H1 : 0 < b) : a ≤ 0 :=
  le_of_not_gt
    (assume H2 : a > 0,
      not_le_of_gt (mul_pos H2 H1) H)
end

@[hott, class] structure decidable_linear_ordered_semiring (A : Type _)
  extends linear_ordered_semiring A, decidable_linear_order A

/- ring structures -/

@[hott] structure ordered_ring (A : Type _) extends ring A, ordered_mul_ab_group A renaming
  mul→add mul_assoc→add_assoc one→zero one_mul→zero_add mul_one→add_zero inv→neg
  mul_left_inv→add_left_inv mul_comm→add_comm mul_le_mul_left→add_le_add_left
  mul_lt_mul_left→add_lt_add_left,
  zero_ne_one_class A :=
(mul_nonneg : Πa b, le zero a → le zero b → le zero (mul a b))
(mul_pos : Πa b, lt zero a → lt zero b → lt zero (mul a b))

-- /- we make it a class now (and not as part of the structure) to avoid
--   ordered_ring.to_ordered_mul_ab_group to be an instance -/
attribute [class] ordered_ring

@[hott, instance, reducible] def add_ab_group_of_ordered_ring (A : Type _)
  [H : ordered_ring A] : ring A :=
@ordered_ring.to_ring A H

@[hott, instance, reducible] def monoid_of_ordered_ring (A : Type _)
  [H : ordered_ring A] : ordered_ab_group A :=
@ordered_ring.to_ordered_mul_ab_group A H

@[hott, instance, reducible] def zero_ne_one_class_of_ordered_ring (A : Type _)
  [H : ordered_ring A] : zero_ne_one_class A :=
@ordered_ring.to_zero_ne_one_class A H


@[hott] def ordered_ring.mul_le_mul_of_nonneg_left [s : ordered_ring A] {a b c : A}
        (Hab : a ≤ b) (Hc : 0 ≤ c) : c * a ≤ c * b :=
have H1 : 0 ≤ b - a, from sub_nonneg_of_le Hab,
have H2 : 0 ≤ c * (b - a), from ordered_ring.mul_nonneg _ _ _ Hc H1,
begin
  rwr mul_sub_left_distrib at H2,
  exact (iff.mp (sub_nonneg_iff_le _ _) H2)
end

@[hott] def ordered_ring.mul_le_mul_of_nonneg_right [s : ordered_ring A] {a b c : A}
        (Hab : a ≤ b) (Hc : 0 ≤ c) : a * c ≤ b * c  :=
have H1 : 0 ≤ b - a, from iff.elim_right (sub_nonneg_iff_le _ _) Hab,
have H2 : 0 ≤ (b - a) * c, from ordered_ring.mul_nonneg _ _ _ H1 Hc,
begin
  rwr mul_sub_right_distrib at H2,
  exact le_of_sub_nonneg H2
end

@[hott] def ordered_ring.mul_lt_mul_of_pos_left [s : ordered_ring A] {a b c : A}
       (Hab : a < b) (Hc : 0 < c) : c * a < c * b :=
have H1 : 0 < b - a, from iff.elim_right (sub_pos_iff_lt _ _) Hab,
have H2 : 0 < c * (b - a), from ordered_ring.mul_pos _ _ _ Hc H1,
begin
  rwr mul_sub_left_distrib at H2,
  exact (iff.mp (sub_pos_iff_lt _ _) H2)
end

@[hott] def ordered_ring.mul_lt_mul_of_pos_right [s : ordered_ring A] {a b c : A}
       (Hab : a < b) (Hc : 0 < c) : a * c < b * c :=
have H1 : 0 < b - a, from iff.elim_right (sub_pos_iff_lt _ _) Hab,
have H2 : 0 < (b - a) * c, from ordered_ring.mul_pos _ _ _ H1 Hc,
begin
  rwr mul_sub_right_distrib at H2,
  exact (lt_of_sub_pos H2)
end

@[hott, instance, reducible] def ordered_ring.to_ordered_semiring [s : ordered_ring A] :
  ordered_semiring A :=
{ mul_zero                   := mul_zero,
  zero_mul                   := zero_mul,
  add_left_cancel            := @add.left_cancel A _,
  add_right_cancel           := @add.right_cancel A _,
  le_of_add_le_add_left      := @le_of_add_le_add_left A _,
  mul_le_mul_of_nonneg_left  := @ordered_ring.mul_le_mul_of_nonneg_left A _,
  mul_le_mul_of_nonneg_right := @ordered_ring.mul_le_mul_of_nonneg_right A _,
  mul_lt_mul_of_pos_left     := @ordered_ring.mul_lt_mul_of_pos_left A _,
  mul_lt_mul_of_pos_right    := @ordered_ring.mul_lt_mul_of_pos_right A _,
  lt_of_add_lt_add_left      := @lt_of_add_lt_add_left A _, ..s }

section
  variable [s : ordered_ring A]
  variables {a b c : A}
  include s

  @[hott] theorem mul_le_mul_of_nonpos_left (H : b ≤ a) (Hc : c ≤ 0) : c * a ≤ c * b :=
  have Hc' : -c ≥ 0, from iff.mpr (neg_nonneg_iff_nonpos _) Hc,
  have H1 : -c * b ≤ -c * a, from mul_le_mul_of_nonneg_left H Hc',
  have H2 : -(c * b) ≤ -(c * a),
    begin
      rwr [←neg_mul_eq_neg_mul, ←neg_mul_eq_neg_mul] at H1,
      exact H1
    end,
  le_of_neg_le_neg H2

  @[hott] theorem mul_le_mul_of_nonpos_right (H : b ≤ a) (Hc : c ≤ 0) : a * c ≤ b * c :=
  have Hc' : -c ≥ 0, from iff.mpr (neg_nonneg_iff_nonpos _) Hc,
  have H1 : b * -c ≤ a * -c, from mul_le_mul_of_nonneg_right H Hc',
  have H2 : -(b * c) ≤ -(a * c),
    begin
      rwr [←neg_mul_eq_mul_neg, ←neg_mul_eq_mul_neg] at H1,
      exact H1
    end,
  le_of_neg_le_neg H2

  @[hott] theorem mul_nonneg_of_nonpos_of_nonpos (Ha : a ≤ 0) (Hb : b ≤ 0) : 0 ≤ a * b :=
  begin
    have H : 0 * b ≤ a * b, from mul_le_mul_of_nonpos_right Ha Hb,
    rwr zero_mul at H,
    exact H
  end

  @[hott] def mul_lt_mul_of_neg_left (H : b < a) (Hc : c < 0) : c * a < c * b :=
  have Hc' : -c > 0, from iff.mpr (neg_pos_iff_neg _) Hc,
  have H1 : -c * b < -c * a, from mul_lt_mul_of_pos_left H Hc',
  have H2 : -(c * b) < -(c * a),
    begin
      rwr [←neg_mul_eq_neg_mul, ←neg_mul_eq_neg_mul] at H1,
      exact H1
    end,
  lt_of_neg_lt_neg H2

  @[hott] def mul_lt_mul_of_neg_right (H : b < a) (Hc : c < 0) : a * c < b * c :=
  have Hc' : -c > 0, from iff.mpr (neg_pos_iff_neg _) Hc,
  have H1 : b * -c < a * -c, from mul_lt_mul_of_pos_right H Hc',
  have H2 : -(b * c) < -(a * c),
    begin
      rwr [←neg_mul_eq_mul_neg, ←neg_mul_eq_mul_neg] at H1,
      exact H1
    end,
  lt_of_neg_lt_neg H2

  @[hott] def mul_pos_of_neg_of_neg (Ha : a < 0) (Hb : b < 0) : 0 < a * b :=
  begin
    have H : 0 * b < a * b, from mul_lt_mul_of_neg_right Ha Hb,
    rwr zero_mul at H,
    exact H
  end

end

-- TODO: we can eliminate mul_pos_of_pos, but now it is not worth the effort to redeclare the
-- class instance
@[hott, class] structure linear_ordered_ring (A : Type _)
    extends ordered_ring A, linear_strong_order_pair A :=
  (zero_lt_one : lt zero one)

@[hott, instance, reducible] def linear_ordered_ring.to_linear_ordered_semiring
  [s : linear_ordered_ring A] : linear_ordered_semiring A :=
{ mul_zero                   := mul_zero,
  zero_mul                   := zero_mul,
  add_left_cancel            := @add.left_cancel A _,
  add_right_cancel           := @add.right_cancel A _,
  le_of_add_le_add_left      := @le_of_add_le_add_left A _,
  mul_le_mul_of_nonneg_left  := @mul_le_mul_of_nonneg_left A _,
  mul_le_mul_of_nonneg_right := @mul_le_mul_of_nonneg_right A _,
  mul_lt_mul_of_pos_left     := @mul_lt_mul_of_pos_left A _,
  mul_lt_mul_of_pos_right    := @mul_lt_mul_of_pos_right A _,
  le_total                   := linear_ordered_ring.le_total,
  lt_of_add_lt_add_left      := @lt_of_add_lt_add_left A _, ..s }

@[hott, class] structure linear_ordered_comm_ring (A : Type _) extends
  linear_ordered_ring A, comm_monoid A

@[hott] def linear_ordered_comm_ring.eq_zero_sum_eq_zero_of_mul_eq_zero
  [s : linear_ordered_comm_ring A] {a b : A} (H : a * b = 0) : a = 0 ⊎ b = 0 :=
lt.by_cases
  (assume Ha : 0 < a,
    lt.by_cases
      (assume Hb : 0 < b,
        begin
          have H1 : 0 < a * b, from mul_pos Ha Hb,
          rwr H at H1,
          apply absurd_a_lt_a H1
        end)
      (assume Hb : 0 = b, sum.inr (Hb⁻¹))
      (assume Hb : 0 > b,
        begin
          have H1 : 0 > a * b, from mul_neg_of_pos_of_neg Ha Hb,
          rwr H at H1,
          apply absurd_a_lt_a H1
        end))
  (assume Ha : 0 = a, sum.inl (Ha⁻¹))
  (assume Ha : 0 > a,
    lt.by_cases
      (assume Hb : 0 < b,
        begin
          have H1 : 0 > a * b, from mul_neg_of_neg_of_pos Ha Hb,
          rwr H at H1,
          apply absurd_a_lt_a H1
        end)
      (assume Hb : 0 = b, sum.inr (Hb⁻¹))
      (assume Hb : 0 > b,
        begin
          have H1 : 0 < a * b, from mul_pos_of_neg_of_neg Ha Hb,
          rwr H at H1,
          apply absurd_a_lt_a H1
        end))

-- Linearity implies no zero divisors. Doesn't need commutativity.
@[hott, instance, reducible] def linear_ordered_comm_ring.to_integral_domain
    [s : linear_ordered_comm_ring A] : integral_domain A :=
{ eq_zero_sum_eq_zero_of_mul_eq_zero :=
     @linear_ordered_comm_ring.eq_zero_sum_eq_zero_of_mul_eq_zero A s, ..s }

section
variable [s : linear_ordered_ring A]
variables (a b c : A)
include s

@[hott] theorem mul_self_nonneg : a * a ≥ 0 :=
sum.elim (le.total 0 a)
  (assume H : a ≥ 0, mul_nonneg H H)
  (assume H : a ≤ 0, mul_nonneg_of_nonpos_of_nonpos H H)

@[hott] theorem zero_le_one : 0 ≤ (1:A) := by rwr [←one_mul (1 : A)]; exact mul_self_nonneg 1

@[hott] theorem pos_prod_pos_sum_neg_prod_neg_of_mul_pos {a b : A} (Hab : a * b > 0) :
  (a > 0 × b > 0) ⊎ (a < 0 × b < 0) :=
lt.by_cases
  (assume Ha : 0 < a,
    lt.by_cases
      (assume Hb : 0 < b, sum.inl (pair Ha Hb))
      (assume Hb : 0 = b,
        begin
          rwr [←Hb, mul_zero] at Hab,
          apply absurd_a_lt_a Hab
        end)
      (assume Hb : b < 0,
        absurd Hab (lt.asymm (mul_neg_of_pos_of_neg Ha Hb))))
  (assume Ha : 0 = a,
    begin
      rwr [←Ha, zero_mul] at Hab,
      apply absurd_a_lt_a Hab
    end)
  (assume Ha : a < 0,
    lt.by_cases
      (assume Hb : 0 < b,
        absurd Hab (lt.asymm (mul_neg_of_neg_of_pos Ha Hb)))
      (assume Hb : 0 = b,
        begin
          rwr [←Hb, mul_zero] at Hab,
          apply absurd_a_lt_a Hab
        end)
      (assume Hb : b < 0, sum.inr (pair Ha Hb)))

@[hott] theorem gt_of_mul_lt_mul_neg_left {a b c : A} (H : c * a < c * b) (Hc : c ≤ 0) : a > b :=
have nhc : -c ≥ 0, from neg_nonneg_of_nonpos Hc,
have H2 : -(c * b) < -(c * a), from iff.mpr (neg_lt_neg_iff_lt _ _) H,
have H3 : (-c) * b < (-c) * a, from calc
  (-c) * b = - (c * b)    : by rwr neg_mul_eq_neg_mul
       ... < -(c * a)     : H2
       ... = (-c) * a     : by rwr neg_mul_eq_neg_mul,
lt_of_mul_lt_mul_left H3 nhc

@[hott] theorem zero_gt_neg_one : - 1 < (0:A) :=
by rwr ←neg_zero; exact neg_lt_neg zero_lt_one

@[hott] theorem le_of_mul_le_of_ge_one {a b c : A} (H : a * c ≤ b) (Hb : b ≥ 0) (Hc : c ≥ 1) :
a ≤ b :=
have H' : a * c ≤ b * c, from calc
  a * c ≤ b : H
    ... = b * 1 : by rwr mul_one
    ... ≤ b * c : mul_le_mul_of_nonneg_left Hc Hb,
le_of_mul_le_mul_right H' (lt_of_lt_of_le zero_lt_one Hc)

@[hott] theorem nonneg_le_nonneg_of_squares_le {a b : A} (Ha : a ≥ 0) (Hb : b ≥ 0)
  (H : a * a ≤ b * b) : a ≤ b :=
begin
  apply le_of_not_gt,
  intro Hab,
  let Hposa := lt_of_le_of_lt Hb Hab,
  let H' := calc
    b * b ≤ a * b : mul_le_mul_of_nonneg_right (le_of_lt Hab) Hb
    ... < a * a : mul_lt_mul_of_pos_left Hab Hposa,
  apply (not_le_of_gt H') H
end
end

/- TODO: Isabelle's library has all kinds of cancelation rules for the simplifier.
   Search on mult_le_cancel_right1 in Rings.thy. -/

@[hott] structure decidable_linear_ordered_comm_ring (A : Type _) extends linear_ordered_comm_ring A,
    decidable_linear_ordered_mul_ab_group A renaming
  mul→add mul_assoc→add_assoc one→zero one_mul→zero_add mul_one→add_zero inv→neg
  mul_left_inv→add_left_inv mul_comm→add_comm mul_le_mul_left→add_le_add_left
  mul_lt_mul_left→add_lt_add_left

/- we make it a class now (and not as part of the structure) to avoid
  ordered_semiring.to_ordered_mul_cancel_comm_monoid to be an instance -/
attribute [class] decidable_linear_ordered_comm_ring

@[hott, instance, reducible] def linear_ordered_comm_ring_of_decidable_linear_ordered_comm_ring
  (A : Type _) [H : decidable_linear_ordered_comm_ring A] : linear_ordered_comm_ring A :=
@decidable_linear_ordered_comm_ring.to_linear_ordered_comm_ring A H

@[hott, instance, reducible]
def decidable_linear_ordered_ab_group_of_decidable_linear_ordered_comm_ring
  (A : Type _) [H : decidable_linear_ordered_comm_ring A] : decidable_linear_ordered_ab_group A :=
@decidable_linear_ordered_comm_ring.to_decidable_linear_ordered_mul_ab_group A H

section
variable [s : decidable_linear_ordered_comm_ring A]
variables {a b c : A}
include s

@[hott] def sign (a : A) : A := lt.cases a 0 (- 1) 0 1

@[hott] theorem sign_of_neg (H : a < 0) : sign a = - 1 := lt.cases_of_lt H

@[hott] theorem sign_zero : sign 0 = (0:A) := lt.cases_of_eq rfl

@[hott] theorem sign_of_pos (H : a > 0) : sign a = 1 := lt.cases_of_gt H

@[hott] theorem sign_one : sign 1 = (1:A) := sign_of_pos zero_lt_one

@[hott] theorem sign_neg_one : sign (- 1) = -(1:A) := sign_of_neg (neg_neg_of_pos zero_lt_one)

@[hott] theorem sign_sign (a : A) : sign (sign a) = sign a :=
lt.by_cases
  (assume H : a > 0,
    calc
      sign (sign a) = sign 1 : by rwr (sign_of_pos H)
                ... = 1      : by rwr sign_one
                ... = sign a : by rwr (sign_of_pos H))
  (assume H : 0 = a,
    calc
      sign (sign a) = sign (sign 0) : by rwr H
                ... = sign 0        : by rwr ap sign sign_zero
                ... = sign a        : by rwr ←H)
  (assume H : a < 0,
    calc
      sign (sign a) = sign (- 1) : by rwr (sign_of_neg H)
                ... = - 1        : by rwr sign_neg_one
                ... = sign a     : by rwr (sign_of_neg H))

@[hott] theorem pos_of_sign_eq_one (H : sign a = 1) : a > 0 :=
lt.by_cases
  (assume H1 : 0 < a, H1)
  (assume H1 : 0 = a,
    begin
      rwr [←H1, sign_zero] at H,
      apply absurd H zero_ne_one
    end)
  (assume H1 : 0 > a,
    have H2 : - 1 = 1 :> A, from (sign_of_neg H1)⁻¹ ⬝ H,
    absurd ((eq_zero_of_neg_eq H2)⁻¹ᵖ) zero_ne_one)

@[hott] theorem eq_zero_of_sign_eq_zero (H : sign a = 0) : a = 0 :=
lt.by_cases
  (assume H1 : 0 < a,
    absurd (H⁻¹ ⬝ sign_of_pos H1) zero_ne_one)
  (assume H1 : 0 = a, H1⁻¹)
  (assume H1 : 0 > a,
    have H2 : 0 = - 1 :> A, from H⁻¹ ⬝ sign_of_neg H1,
    have H3 : 1 = 0 :> A, from eq_neg_of_eq_neg H2 ⬝ neg_zero,
    absurd (H3⁻¹) zero_ne_one)

@[hott] theorem neg_of_sign_eq_neg_one (H : sign a = - 1) : a < 0 :=
lt.by_cases
  (assume H1 : 0 < a,
    have H2 : - 1 = 1 :> A, from H⁻¹ ⬝ (sign_of_pos H1),
    absurd ((eq_zero_of_neg_eq H2)⁻¹) zero_ne_one)
  (assume H1 : 0 = a,
    have H2 : 0 = - 1 :> A,
      begin
        rwr [←H1, sign_zero] at H,
        exact H
      end,
    have H3 : 1 = 0 :> A, from eq_neg_of_eq_neg H2 ⬝ neg_zero,
    absurd (H3⁻¹) zero_ne_one)
  (assume H1 : 0 > a, H1)

@[hott] theorem sign_neg (a : A) : sign (-a) = -(sign a) :=
lt.by_cases
  (assume H1 : 0 < a,
    calc
      sign (-a) = - 1        : sign_of_neg (neg_neg_of_pos H1)
            ... = -(sign a) : by rwr (sign_of_pos H1))
  (assume H1 : 0 = a,
    calc
      sign (-a) = sign (-0) : by rwr ←H1
            ... = sign 0    : by rwr neg_zero
            ... = 0         : by rwr sign_zero
            ... = -0        : by rwr neg_zero
            ... = -(sign 0) : by rwr sign_zero
            ... = -(sign a) : by rwr ←H1)
  (assume H1 : 0 > a,
    calc
      sign (-a) = 1         : sign_of_pos (neg_pos_of_neg H1)
            ... = -(- 1)    : by rwr neg_neg
            ... = -(sign a) : by rwr sign_of_neg H1)

@[hott] theorem sign_mul (a b : A) : sign (a * b) = sign a * sign b :=
hott.algebra.lt.by_cases
  (assume z_lt_a : 0 < a,
    lt.by_cases
     (assume z_lt_b : 0 < b,
       by rwr [sign_of_pos z_lt_a, sign_of_pos z_lt_b,
                   sign_of_pos (mul_pos z_lt_a z_lt_b), one_mul])
     (assume z_eq_b : 0 = b, by rwr [←z_eq_b, mul_zero, sign_zero, mul_zero])
     (assume z_gt_b : 0 > b,
       by rwr [sign_of_pos z_lt_a, sign_of_neg z_gt_b,
                   sign_of_neg (mul_neg_of_pos_of_neg z_lt_a z_gt_b), one_mul]))
  (assume z_eq_a : 0 = a, by rwr [←z_eq_a, zero_mul, sign_zero, zero_mul])
  (assume z_gt_a : 0 > a,
    lt.by_cases
     (assume z_lt_b : 0 < b,
       by rwr [sign_of_neg z_gt_a, sign_of_pos z_lt_b,
                   sign_of_neg (mul_neg_of_neg_of_pos z_gt_a z_lt_b), mul_one])
     (assume z_eq_b : 0 = b, by rwr [←z_eq_b, mul_zero, sign_zero, mul_zero])
     (assume z_gt_b : 0 > b,
       by rwr [sign_of_neg z_gt_a, sign_of_neg z_gt_b,
                   sign_of_pos (mul_pos_of_neg_of_neg z_gt_a z_gt_b),
                   neg_mul_neg, one_mul]))

@[hott] theorem abs_eq_sign_mul (a : A) : abs a = sign a * a :=
lt.by_cases
  (assume H1 : 0 < a,
    calc
      abs a = a          : abs_of_pos H1
      ... = 1 * a        : by rwr one_mul
      ... = sign a * a   : by rwr (sign_of_pos H1))
  (assume H1 : 0 = a,
    calc
      abs a = abs 0    : by rwr ←H1
      ... = 0          : abs_zero
      ... = 0 * a      : by rwr zero_mul
      ... = sign 0 * a : by rwr sign_zero
      ... = sign a * a : by rwr ←H1)
  (assume H1 : a < 0,
    calc
      abs a = -a         : abs_of_neg H1
        ... = - 1 * a     : by rwr neg_eq_neg_one_mul
        ... = sign a * a : by rwr (sign_of_neg H1))

@[hott] theorem eq_sign_mul_abs (a : A) : a = sign a * abs a :=
lt.by_cases
  (assume H1 : 0 < a,
    calc
      a = abs a              : by rwr abs_of_pos H1
        ... = 1 * abs a      : by rwr one_mul
        ... = sign a * abs a : by rwr (sign_of_pos H1))
  (assume H1 : 0 = a,
    calc
      a = 0                  : H1⁻¹
        ... = 0 * abs a      : by rwr zero_mul
        ... = sign 0 * abs a : by rwr sign_zero
        ... = sign a * abs a : by rwr H1)
  (assume H1 : a < 0,
    calc
      a = -(-a)              : by rwr neg_neg
        ... = -abs a         : by rwr (abs_of_neg H1)
        ... = - 1 * abs a     : by rwr neg_eq_neg_one_mul
        ... = sign a * abs a : by rwr (sign_of_neg H1))

-- @[hott] theorem abs_dvd_iff (a b : A) : abs a ∣ b ↔ a ∣ b :=
-- abs.by_cases iff.rfl (neg_dvd_iff_dvd _ _)

-- @[hott] theorem abs_dvd_of_dvd {a b : A} : a ∣ b → abs a ∣ b :=
--   iff.mpr !abs_dvd_iff

-- @[hott] theorem dvd_abs_iff (a b : A) : a ∣ abs b ↔ a ∣ b :=
-- abs.by_cases iff.rfl !dvd_neg_iff_dvd

-- @[hott] theorem dvd_abs_of_dvd {a b : A} : a ∣ b → a ∣ abs b :=
--   iff.mpr !dvd_abs_iff

-- @[hott] theorem abs_mul (a b : A) : abs (a * b) = abs a * abs b :=
-- sum.elim (le.total 0 a)
--   (assume H1 : 0 ≤ a,
--     sum.elim (le.total 0 b)
--       (assume H2 : 0 ≤ b,
--         calc
--           abs (a * b) = a * b         : abs_of_nonneg (mul_nonneg H1 H2)
--                   ... = abs a * b     : by rwr (abs_of_nonneg H1)
--                   ... = abs a * abs b : by rwr (abs_of_nonneg H2))
--       (assume H2 : b ≤ 0,
--         calc
--           abs (a * b) = -(a * b)      : abs_of_nonpos (mul_nonpos_of_nonneg_of_nonpos H1 H2)
--                   ... = a * -b        : by rwr neg_mul_eq_mul_neg
--                   ... = abs a * -b    : by rwr (abs_of_nonneg H1)
--                   ... = abs a * abs b : by rwr (abs_of_nonpos H2)))
--   (assume H1 : a ≤ 0,
--     sum.elim (le.total 0 b)
--       (assume H2 : 0 ≤ b,
--         calc
--           abs (a * b) = -(a * b)      : abs_of_nonpos (mul_nonpos_of_nonpos_of_nonneg H1 H2)
--                   ... = -a * b        : by rwr neg_mul_eq_neg_mul
--                   ... = abs a * b     : by rwr (abs_of_nonpos H1)
--                   ... = abs a * abs b : by rwr (abs_of_nonneg H2))
--       (assume H2 : b ≤ 0,
--         calc
--           abs (a * b) = a * b         : abs_of_nonneg (mul_nonneg_of_nonpos_of_nonpos H1 H2)
--                   ... = -a * -b       : by rwr neg_mul_neg
--                   ... = abs a * -b    : by rwr (abs_of_nonpos H1)
--                   ... = abs a * abs b : by rwr (abs_of_nonpos H2)))

-- @[hott] theorem abs_mul_abs_self (a : A) : abs a * abs a = a * a :=
-- abs.by_cases rfl !neg_mul_neg

-- @[hott] theorem abs_mul_self (a : A) : abs (a * a) = a * a :=
-- by rwr [abs_mul, abs_mul_abs_self]

-- @[hott] theorem sub_le_of_abs_sub_le_left (H : abs (a - b) ≤ c) : b - c ≤ a :=
--   if Hz : 0 ≤ a - b then
--     (calc
--       a ≥ b : (iff.mp (sub_nonneg_iff_le _ _)) Hz
--     ... ≥ b - c : sub_le_of_nonneg _ (le.trans !abs_nonneg H))
--   else
--     (have Habs : b - a ≤ c, by rwr [abs_of_neg (lt_of_not_ge Hz), neg_sub] at H; apply H,
--      have Habs' : b ≤ c + a, from (iff.mpr !le_add_iff_sub_right_le) Habs,
--      (iff.mp !le_add_iff_sub_left_le) Habs')

-- @[hott] theorem sub_le_of_abs_sub_le_right (H : abs (a - b) ≤ c) : a - c ≤ b :=
--   sub_le_of_abs_sub_le_left (!abs_sub ▸ H)

-- @[hott] theorem sub_lt_of_abs_sub_lt_left (H : abs (a - b) < c) : b - c < a :=
--   if Hz : 0 ≤ a - b then
--     (calc
--       a ≥ b : (iff.mp (sub_nonneg_iff_le _ _)) Hz
--     ... > b - c : sub_lt_of_pos _ (lt_of_le_of_lt !abs_nonneg H))
--   else
--     (have Habs : b - a < c, by rwr [abs_of_neg (lt_of_not_ge Hz), neg_sub] at H; apply H,
--      have Habs' : b < c + a, from lt_add_of_sub_lt_right Habs,
--      sub_lt_left_of_lt_add Habs')

-- @[hott] theorem sub_lt_of_abs_sub_lt_right (H : abs (a - b) < c) : a - c < b :=
--   sub_lt_of_abs_sub_lt_left (!abs_sub ▸ H)

-- @[hott] theorem abs_sub_square (a b : A) : abs (a - b) * abs (a - b) = a * a + b * b - (1 + 1) * a * b :=
--   begin
--     rwr [abs_mul_abs_self, *mul_sub_left_distrib, *mul_sub_right_distrib,
--              sub_eq_add_neg (a*b), sub_add_eq_sub_sub, sub_neg_eq_add, *right_distrib, sub_add_eq_sub_sub, *one_mul,
--              *add.assoc, {_ + b * b}add.comm, *sub_eq_add_neg],
--     rwr [{a*a + b*b}add.comm],
--     rwr [mul.comm b a, *add.assoc]
--   end

-- @[hott] theorem abs_abs_sub_abs_le_abs_sub (a b : A) : abs (abs a - abs b) ≤ abs (a - b) :=
-- begin
--   apply nonneg_le_nonneg_of_squares_le,
--   repeat apply abs_nonneg,
--   rwr [*abs_sub_square, *abs_abs, *abs_mul_abs_self],
--   apply sub_le_sub_left,
--   rwr *mul.assoc,
--   apply mul_le_mul_of_nonneg_left,
--   rwr ←abs_mul,
--   apply le_abs_self,
--   apply le_of_lt,
--   apply add_pos,
--   apply zero_lt_one,
--   apply zero_lt_one
-- end

end

/- TODO: Multiplication and one, starting with mult_right_le_one_le. -/

-- namespace norm_num

-- @[hott] theorem pos_bit0_helper [s : linear_ordered_semiring A] (a : A) (H : a > 0) : bit0 a > 0 :=
--   by rwr ↑bit0; apply add_pos H H

-- @[hott] theorem nonneg_bit0_helper [s : linear_ordered_semiring A] (a : A) (H : a ≥ 0) : bit0 a ≥ 0 :=
--   by rwr ↑bit0; apply add_nonneg H H

-- @[hott] theorem pos_bit1_helper [s : linear_ordered_semiring A] (a : A) (H : a ≥ 0) : bit1 a > 0 :=
--   begin
--     rwr ↑bit1,
--     apply add_pos_of_nonneg_of_pos,
--     apply nonneg_bit0_helper _ H,
--     apply zero_lt_one
--   end

-- @[hott] theorem nonneg_bit1_helper [s : linear_ordered_semiring A] (a : A) (H : a ≥ 0) : bit1 a ≥ 0 :=
--   by apply le_of_lt; apply pos_bit1_helper _ H

-- @[hott] theorem nonzero_of_pos_helper [s : linear_ordered_semiring A] (a : A) (H : a > 0) : a ≠ 0 :=
--   ne_of_gt H

-- @[hott] theorem nonzero_of_neg_helper [s : linear_ordered_ring A] (a : A) (H : a ≠ 0) : -a ≠ 0 :=
--   begin intro Ha, apply H, apply eq_of_neg_eq_neg, rwr neg_zero, exact Ha end

-- end norm_num
end algebra
end hott
