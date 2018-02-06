/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad

Partially ordered additive groups, modeled on Isabelle's library. These classes can be refined
if necessary.
-/
import .group .order
universes u v w
hott_theory
set_option old_structure_cmd true

namespace hott

open algebra

variable {A : Type _}

/- partially ordered monoids, such as the natural numbers -/

namespace algebra
@[hott, class] structure ordered_mul_cancel_comm_monoid (A : Type _) extends comm_monoid A,
 left_cancel_semigroup A, right_cancel_semigroup A, order_pair A :=
(mul_le_mul_left : Πa b, le a b → Πc, le (mul c a) (mul c b))
(le_of_mul_le_mul_left : Πa b c, le (mul a b) (mul a c) → le b c)
(mul_lt_mul_left : Πa b, lt a b → Πc, lt (mul c a) (mul c b))
(lt_of_mul_lt_mul_left : Πa b c, lt (mul a b) (mul a c) → lt b c)

@[hott, class] def ordered_cancel_comm_monoid : Type _ → Type _ := ordered_mul_cancel_comm_monoid

@[hott, reducible, instance] def add_comm_monoid_of_ordered_cancel_comm_monoid
  (A : Type _) [H : ordered_cancel_comm_monoid A] : add_comm_monoid A :=
@ordered_mul_cancel_comm_monoid.to_comm_monoid A H

@[hott, reducible, instance] def add_left_cancel_semigroup_of_ordered_cancel_comm_monoid
  (A : Type _) [H : ordered_cancel_comm_monoid A] : add_left_cancel_semigroup A :=
@ordered_mul_cancel_comm_monoid.to_left_cancel_semigroup A H

@[hott, reducible, instance] def add_right_cancel_semigroup_of_ordered_cancel_comm_monoid
  (A : Type _) [H : ordered_cancel_comm_monoid A] : add_right_cancel_semigroup A :=
@ordered_mul_cancel_comm_monoid.to_right_cancel_semigroup A H

@[hott, reducible, instance] def order_pair_of_ordered_cancel_comm_monoid
  (A : Type _) [H : ordered_cancel_comm_monoid A] : order_pair A :=
@ordered_mul_cancel_comm_monoid.to_order_pair A H

section
variables [s : ordered_cancel_comm_monoid A]
variables {a b c d e : A}
include s

@[hott] def add_lt_add_left (H : a < b) (c : A) : c + a < c + b :=
@ordered_mul_cancel_comm_monoid.mul_lt_mul_left A s a b H c

@[hott] def add_lt_add_right (H : a < b) (c : A) : a + c < b + c :=
begin
  rwr [add.comm, add.comm b],
  exact (add_lt_add_left H c)
end

@[hott] def add_le_add_left (H : a ≤ b) (c : A) : c + a ≤ c + b :=
@ordered_mul_cancel_comm_monoid.mul_le_mul_left A s a b H c

@[hott] def add_le_add_right (H : a ≤ b) (c : A) : a + c ≤ b + c :=
by rwr [add.comm a c, add.comm b c]; exact add_le_add_left H c

@[hott] theorem add_le_add (Hab : a ≤ b) (Hcd : c ≤ d) : a + c ≤ b + d :=
le.trans (add_le_add_right Hab c) (add_le_add_left Hcd b)

@[hott] theorem le_add_of_nonneg_right (H : b ≥ 0) : a ≤ a + b :=
begin
  have H1 : a + b ≥ a + 0, from add_le_add_left H a,
  rwr add_zero at H1,
  exact H1
end

@[hott] theorem le_add_of_nonneg_left (H : b ≥ 0) : a ≤ b + a :=
begin
  have H1 : 0 + a ≤ b + a, from add_le_add_right H a,
  rwr zero_add at H1,
  exact H1
end

@[hott] theorem add_lt_add (Hab : a < b) (Hcd : c < d) : a + c < b + d :=
lt.trans (add_lt_add_right Hab c) (add_lt_add_left Hcd b)

@[hott] theorem add_lt_add_of_le_of_lt (Hab : a ≤ b) (Hcd : c < d) : a + c < b + d :=
lt_of_le_of_lt (add_le_add_right Hab c) (add_lt_add_left Hcd b)

@[hott] theorem add_lt_add_of_lt_of_le (Hab : a < b) (Hcd : c ≤ d) : a + c < b + d :=
lt_of_lt_of_le (add_lt_add_right Hab c) (add_le_add_left Hcd b)

@[hott] theorem lt_add_of_pos_right (H : b > 0) : a < a + b :=
by have := add_lt_add_left H a; rwra [add_zero a] at this

@[hott] theorem lt_add_of_pos_left (H : b > 0) : a < b + a :=
by have := add_lt_add_right H a; rwra [zero_add a] at this

-- here we start using le_of_add_le_add_left.
@[hott] def le_of_add_le_add_left (H : a + b ≤ a + c) : b ≤ c :=
@ordered_mul_cancel_comm_monoid.le_of_mul_le_mul_left A s a b c H

@[hott] def le_of_add_le_add_right (H : a + b ≤ c + b) : a ≤ c :=
le_of_add_le_add_left (show b + a ≤ b + c, begin rwr [add.comm, add.comm b], exact H end)

@[hott] def lt_of_add_lt_add_left (H : a + b < a + c) : b < c :=
@ordered_mul_cancel_comm_monoid.lt_of_mul_lt_mul_left A s a b c H

@[hott] def lt_of_add_lt_add_right (H : a + b < c + b) : a < c :=
by apply lt_of_add_lt_add_left; rwra [add.comm b a, add.comm b c]

@[hott] def add_le_add_left_iff (a b c : A) : a + b ≤ a + c ↔ b ≤ c :=
iff.intro le_of_add_le_add_left (assume H, add_le_add_left H _)

@[hott] def add_le_add_right_iff (a b c : A) : a + b ≤ c + b ↔ a ≤ c :=
iff.intro le_of_add_le_add_right (assume H, add_le_add_right H _)

@[hott] def add_lt_add_left_iff (a b c : A) : a + b < a + c ↔ b < c :=
iff.intro lt_of_add_lt_add_left (assume H, add_lt_add_left H _)

@[hott] def add_lt_add_right_iff (a b c : A) : a + b < c + b ↔ a < c :=
iff.intro lt_of_add_lt_add_right (assume H, add_lt_add_right H _)

-- here we start using properties of zero.
@[hott] theorem add_nonneg (Ha : 0 ≤ a) (Hb : 0 ≤ b) : 0 ≤ a + b :=
by rwr [←zero_add (0 : A)]; exact add_le_add Ha Hb

@[hott] theorem add_pos (Ha : 0 < a) (Hb : 0 < b) : 0 < a + b :=
by rwr [←zero_add (0 : A)]; exact add_lt_add Ha Hb

@[hott] theorem add_pos_of_pos_of_nonneg (Ha : 0 < a) (Hb : 0 ≤ b) : 0 < a + b :=
by rwr [←zero_add (0 : A)]; exact add_lt_add_of_lt_of_le Ha Hb

@[hott] theorem add_pos_of_nonneg_of_pos (Ha : 0 ≤ a) (Hb : 0 < b) : 0 < a + b :=
by rwr [←zero_add (0 : A)]; exact add_lt_add_of_le_of_lt Ha Hb

@[hott] theorem add_nonpos (Ha : a ≤ 0) (Hb : b ≤ 0) : a + b ≤ 0 :=
by rwr [←zero_add (0 : A)]; exact add_le_add Ha Hb


@[hott] theorem add_neg (Ha : a < 0) (Hb : b < 0) : a + b < 0 :=
by rwr [←zero_add (0 : A)]; exact add_lt_add Ha Hb

@[hott] theorem add_neg_of_neg_of_nonpos (Ha : a < 0) (Hb : b ≤ 0) : a + b < 0 :=
by rwr [←zero_add (0 : A)]; exact add_lt_add_of_lt_of_le Ha Hb

@[hott] theorem add_neg_of_nonpos_of_neg (Ha : a ≤ 0) (Hb : b < 0) : a + b < 0 :=
by rwr [←zero_add (0 : A)]; exact add_lt_add_of_le_of_lt Ha Hb

@[hott] theorem add_eq_zero_iff_eq_zero_prod_eq_zero_of_nonneg_of_nonneg
  (Ha : 0 ≤ a) (Hb : 0 ≤ b) : a + b = 0 ↔ a = 0 × b = 0 :=
iff.intro
  (assume Hab : a + b = 0,
    have Ha' : a ≤ 0, from
      calc
        a     = a + 0 : by rwr add_zero
          ... ≤ a + b : add_le_add_left Hb a
          ... = 0     : Hab,
    have Haz : a = 0, from le.antisymm Ha' Ha,
    have Hb' : b ≤ 0, from
      calc
        b     = 0 + b : by rwr zero_add
          ... ≤ a + b : add_le_add_right Ha b
          ... = 0     : Hab,
    have Hbz : b = 0, from le.antisymm Hb' Hb,
    pair Haz Hbz)
  (assume Hab : a = 0 × b = 0,
   by rwr [Hab.fst, Hab.snd, add_zero])

@[hott] theorem le_add_of_nonneg_of_le (Ha : 0 ≤ a) (Hbc : b ≤ c) : b ≤ a + c :=
by rwr [←zero_add b]; exact add_le_add Ha Hbc

@[hott] theorem le_add_of_le_of_nonneg (Hbc : b ≤ c) (Ha : 0 ≤ a) : b ≤ c + a :=
by rwr [←add_zero b]; exact add_le_add Hbc Ha

@[hott] theorem lt_add_of_pos_of_le (Ha : 0 < a) (Hbc : b ≤ c) : b < a + c :=
by rwr [←zero_add b]; exact add_lt_add_of_lt_of_le Ha Hbc

@[hott] theorem lt_add_of_le_of_pos (Hbc : b ≤ c) (Ha : 0 < a) : b < c + a :=
by rwr [←add_zero b]; exact add_lt_add_of_le_of_lt Hbc Ha

@[hott] theorem add_le_of_nonpos_of_le (Ha : a ≤ 0) (Hbc : b ≤ c) : a + b ≤ c :=
by rwr [←zero_add c]; exact add_le_add Ha Hbc

@[hott] theorem add_le_of_le_of_nonpos (Hbc : b ≤ c) (Ha : a ≤ 0) : b + a ≤ c :=
by rwr [←add_zero c]; exact add_le_add Hbc Ha

@[hott] theorem add_lt_of_neg_of_le (Ha : a < 0) (Hbc : b ≤ c) : a + b < c :=
by rwr [←zero_add c]; exact add_lt_add_of_lt_of_le Ha Hbc

@[hott] theorem add_lt_of_le_of_neg (Hbc : b ≤ c) (Ha : a < 0) : b + a < c :=
by rwr [←add_zero c]; exact add_lt_add_of_le_of_lt Hbc Ha

@[hott] theorem lt_add_of_nonneg_of_lt (Ha : 0 ≤ a) (Hbc : b < c) : b < a + c :=
by rwr [←zero_add b]; exact add_lt_add_of_le_of_lt Ha Hbc

@[hott] theorem lt_add_of_lt_of_nonneg (Hbc : b < c) (Ha : 0 ≤ a) : b < c + a :=
by rwr [←add_zero b]; exact add_lt_add_of_lt_of_le Hbc Ha

@[hott] theorem lt_add_of_pos_of_lt (Ha : 0 < a) (Hbc : b < c) : b < a + c :=
by rwr [←zero_add b]; exact add_lt_add Ha Hbc

@[hott] theorem lt_add_of_lt_of_pos (Hbc : b < c) (Ha : 0 < a) : b < c + a :=
by rwr [←add_zero b]; exact add_lt_add Hbc Ha

@[hott] theorem add_lt_of_nonpos_of_lt (Ha : a ≤ 0) (Hbc : b < c) : a + b < c :=
by rwr [←zero_add c]; exact add_lt_add_of_le_of_lt Ha Hbc

@[hott] theorem add_lt_of_lt_of_nonpos (Hbc : b < c) (Ha : a ≤ 0)  : b + a < c :=
by rwr [←add_zero c]; exact add_lt_add_of_lt_of_le Hbc Ha

@[hott] theorem add_lt_of_neg_of_lt (Ha : a < 0) (Hbc : b < c) : a + b < c :=
by rwr [←zero_add c]; exact add_lt_add Ha Hbc

@[hott] theorem add_lt_of_lt_of_neg (Hbc : b < c) (Ha : a < 0) : b + a < c :=
by rwr [←add_zero c]; exact add_lt_add Hbc Ha
end

/- partially ordered groups -/

@[hott, class] structure ordered_mul_ab_group (A : Type _) extends ab_group A, order_pair A :=
(mul_le_mul_left : Πa b, le a b → Πc, le (mul c a) (mul c b))
(mul_lt_mul_left : Πa b, lt a b → Π c, lt (mul c a) (mul c b))

@[hott, class] def ordered_ab_group : Type _ → Type _ := ordered_mul_ab_group

@[hott, reducible, instance] def add_ab_group_of_ordered_ab_group (A : Type _)
  [H : ordered_ab_group A] : add_ab_group A :=
@ordered_mul_ab_group.to_ab_group A H

@[hott] def ordered_mul_ab_group.le_of_mul_le_mul_left [s : ordered_mul_ab_group A] {a b c : A}
  (H : a * b ≤ a * c) : b ≤ c :=
have H' : a⁻¹ * (a * b) ≤ a⁻¹ * (a * c), from ordered_mul_ab_group.mul_le_mul_left _ _ H _,
by rwr [inv_mul_cancel_left, inv_mul_cancel_left] at H'; exact H'

@[hott] def ordered_mul_ab_group.lt_of_mul_lt_mul_left [s : ordered_mul_ab_group A] {a b c : A}
  (H : a * b < a * c) : b < c :=
have H' : a⁻¹ * (a * b) < a⁻¹ * (a * c), from ordered_mul_ab_group.mul_lt_mul_left _ _ H _,
by rwr [inv_mul_cancel_left, inv_mul_cancel_left] at H'; exact H'

@[hott, reducible, instance] def ordered_mul_ab_group.to_ordered_mul_cancel_comm_monoid
    [s : ordered_mul_ab_group A] : ordered_mul_cancel_comm_monoid A :=
{ mul_left_cancel       := @mul.left_cancel A _,
  mul_right_cancel      := @mul.right_cancel A _,
  le_of_mul_le_mul_left := @ordered_mul_ab_group.le_of_mul_le_mul_left A _,
  lt_of_mul_lt_mul_left := @ordered_mul_ab_group.lt_of_mul_lt_mul_left A _, ..s}

@[hott, reducible, instance] def ordered_ab_group.to_ordered_cancel_comm_monoid
    [s : ordered_ab_group A] : ordered_cancel_comm_monoid A :=
@ordered_mul_ab_group.to_ordered_mul_cancel_comm_monoid A s

section
variables [s : ordered_ab_group A] (a b c d e : A)
include s

@[hott] theorem neg_le_neg {a b : A} (H : a ≤ b) : -b ≤ -a :=
have H1 : 0 ≤ -a + b, by rwr [←add.left_inv a]; apply add_le_add_left H,
by rwr [←zero_add (-b), ←add_neg_cancel_right (-a) b]; exact add_le_add_right H1 (-b)

@[hott] theorem le_of_neg_le_neg {a b : A} (H : -b ≤ -a) : a ≤ b :=
by rwr [←neg_neg a, ←neg_neg b]; exact neg_le_neg H

@[hott] theorem neg_le_neg_iff_le : -a ≤ -b ↔ b ≤ a :=
iff.intro le_of_neg_le_neg neg_le_neg

@[hott] theorem nonneg_of_neg_nonpos {a : A} (H : -a ≤ 0) : 0 ≤ a :=
by apply le_of_neg_le_neg; rwra neg_zero

@[hott] theorem neg_nonpos_of_nonneg {a : A} (H : 0 ≤ a) : -a ≤ 0 :=
by rwr [←neg_zero]; exact neg_le_neg H

@[hott] theorem neg_nonpos_iff_nonneg : -a ≤ 0 ↔ 0 ≤ a :=
iff.intro nonneg_of_neg_nonpos neg_nonpos_of_nonneg

@[hott] theorem nonpos_of_neg_nonneg {a : A} (H : 0 ≤ -a) : a ≤ 0 :=
by apply le_of_neg_le_neg; rwra neg_zero

@[hott] theorem neg_nonneg_of_nonpos {a : A} (H : a ≤ 0) : 0 ≤ -a :=
by rwr [←neg_zero]; exact neg_le_neg H

@[hott] theorem neg_nonneg_iff_nonpos : 0 ≤ -a ↔ a ≤ 0 :=
iff.intro nonpos_of_neg_nonneg neg_nonneg_of_nonpos

@[hott] def neg_lt_neg {a b : A} (H : a < b) : -b < -a :=
have H1 : 0 < -a + b, by rwr [←add.left_inv a]; apply add_lt_add_left H,
by rwr [←zero_add (-b), ←add_neg_cancel_right (-a) b]; exact add_lt_add_right H1 (-b)

@[hott] def lt_of_neg_lt_neg {a b : A} (H : -b < -a) : a < b :=
by rwr [←neg_neg a, ←neg_neg b]; exact neg_lt_neg H

@[hott] theorem neg_lt_neg_iff_lt : -a < -b ↔ b < a :=
iff.intro lt_of_neg_lt_neg neg_lt_neg

@[hott] theorem pos_of_neg_neg {a : A} (H : -a < 0) : 0 < a :=
by apply lt_of_neg_lt_neg; rwra [neg_zero]

@[hott] theorem neg_neg_of_pos {a : A} (H : 0 < a) : -a < 0 :=
by rwr [←neg_zero]; exact neg_lt_neg H

@[hott] theorem neg_neg_iff_pos : -a < 0 ↔ 0 < a :=
iff.intro pos_of_neg_neg neg_neg_of_pos

@[hott] def neg_of_neg_pos {a : A} (H : 0 < -a) : a < 0 :=
by apply lt_of_neg_lt_neg; rwra neg_zero

@[hott] def neg_pos_of_neg {a : A} (H : a < 0) : 0 < -a :=
by rwr [←neg_zero]; exact neg_lt_neg H

@[hott] def neg_pos_iff_neg : 0 < -a ↔ a < 0 :=
iff.intro neg_of_neg_pos neg_pos_of_neg

@[hott] theorem le_neg_iff_le_neg : a ≤ -b ↔ b ≤ -a :=
by refine iff.trans _ (neg_le_neg_iff_le _ _); rwr neg_neg

@[hott] theorem le_neg_of_le_neg {a b : A} : a ≤ -b → b ≤ -a :=
(le_neg_iff_le_neg _ _).mp

@[hott] theorem neg_le_iff_neg_le : -a ≤ b ↔ -b ≤ a :=
by refine iff.trans _ (neg_le_neg_iff_le _ _); rwr neg_neg

@[hott] theorem neg_le_of_neg_le {a b : A} : -a ≤ b → -b ≤ a :=
(neg_le_iff_neg_le _ _).mp

@[hott] theorem lt_neg_iff_lt_neg : a < -b ↔ b < -a :=
by refine iff.trans _ (neg_lt_neg_iff_lt _ _); rwr neg_neg

@[hott] theorem lt_neg_of_lt_neg {a b : A} : a < -b → b < -a :=
(lt_neg_iff_lt_neg _ _).mp

@[hott] theorem neg_lt_iff_neg_lt : -a < b ↔ -b < a :=
by refine iff.trans _ (neg_lt_neg_iff_lt _ _); rwr neg_neg

@[hott] theorem neg_lt_of_neg_lt {a b : A} : -a < b → -b < a :=
(neg_lt_iff_neg_lt _ _).mp

@[hott] def sub_nonneg_iff_le : 0 ≤ a - b ↔ b ≤ a :=
by rwr [←sub_self b]; apply add_le_add_right_iff

@[hott] def sub_nonneg_of_le {a b : A} : b ≤ a → 0 ≤ a - b :=
(sub_nonneg_iff_le _ _).mpr

@[hott] def le_of_sub_nonneg {a b : A} : 0 ≤ a - b → b ≤ a :=
(sub_nonneg_iff_le _ _).mp

@[hott] theorem sub_nonpos_iff_le : a - b ≤ 0 ↔ a ≤ b :=
by rwr [←sub_self b]; apply add_le_add_right_iff

@[hott] theorem sub_nonpos_of_le {a b : A} : a ≤ b → a - b ≤ 0 :=
(sub_nonpos_iff_le _ _).mpr

@[hott] theorem le_of_sub_nonpos {a b : A} : a - b ≤ 0 → a ≤ b :=
(sub_nonpos_iff_le _ _).mp

@[hott] def sub_pos_iff_lt : 0 < a - b ↔ b < a :=
by rwr [←sub_self b]; apply add_lt_add_right_iff

@[hott] def sub_pos_of_lt {a b : A} : b < a → 0 < a - b :=
(sub_pos_iff_lt _ _).mpr

@[hott] def lt_of_sub_pos {a b : A} : 0 < a - b → b < a :=
(sub_pos_iff_lt _ _).mp

@[hott] theorem sub_neg_iff_lt : a - b < 0 ↔ a < b :=
by rwr [←sub_self b]; apply add_lt_add_right_iff

@[hott] theorem sub_neg_of_lt {a b : A} : a < b → a - b < 0 :=
(sub_neg_iff_lt _ _).mpr

@[hott] theorem lt_of_sub_neg {a b : A} : a - b < 0 → a < b :=
(sub_neg_iff_lt _ _).mp

@[hott] theorem add_le_iff_le_neg_add : a + b ≤ c ↔ b ≤ -a + c :=
have H: a + b ≤ c ↔ -a + (a + b) ≤ -a + c, from iff.symm (add_le_add_left_iff _ _ _),
by rwra neg_add_cancel_left at H

@[hott] theorem add_le_of_le_neg_add {a b c : A} : b ≤ -a + c → a + b ≤ c :=
(add_le_iff_le_neg_add _ _ _).mpr

@[hott] theorem le_neg_add_of_add_le {a b c : A} : a + b ≤ c → b ≤ -a + c :=
(add_le_iff_le_neg_add _ _ _).mp

@[hott] theorem add_le_iff_le_sub_left : a + b ≤ c ↔ b ≤ c - a :=
by rwr [sub_eq_add_neg, add.comm c]; apply add_le_iff_le_neg_add

@[hott] theorem add_le_of_le_sub_left {a b c : A} : b ≤ c - a → a + b ≤ c :=
iff.mpr (add_le_iff_le_sub_left _ _ _)

@[hott] theorem le_sub_left_of_add_le {a b c : A} : a + b ≤ c → b ≤ c - a :=
iff.mp (add_le_iff_le_sub_left _ _ _)

@[hott] theorem add_le_iff_le_sub_right : a + b ≤ c ↔ a ≤ c - b :=
have H: a + b ≤ c ↔ a + b - b ≤ c - b, from iff.symm (add_le_add_right_iff _ _ _),
by rwra add_sub_cancel at H

@[hott] theorem add_le_of_le_sub_right {a b c : A} : a ≤ c - b → a + b ≤ c :=
(add_le_iff_le_sub_right  _ _ _).mpr

@[hott] theorem le_sub_right_of_add_le {a b c : A} : a + b ≤ c → a ≤ c - b :=
(add_le_iff_le_sub_right _ _ _).mp

@[hott] theorem le_add_iff_neg_add_le : a ≤ b + c ↔ -b + a ≤ c :=
have H: a ≤ b + c ↔ -b + a ≤ -b + (b + c), from iff.symm (add_le_add_left_iff _ _ _),
by rwr neg_add_cancel_left at H; exact H

@[hott] theorem le_add_of_neg_add_le {a b c : A} : -b + a ≤ c → a ≤ b + c :=
(le_add_iff_neg_add_le _ _ _).mpr

@[hott] theorem neg_add_le_of_le_add {a b c : A} : a ≤ b + c → -b + a ≤ c :=
(le_add_iff_neg_add_le _ _ _).mp

@[hott] theorem le_add_iff_sub_left_le : a ≤ b + c ↔ a - b ≤ c :=
by rwr [sub_eq_add_neg, add.comm a]; apply le_add_iff_neg_add_le

@[hott] theorem le_add_of_sub_left_le {a b c : A} : a - b ≤ c → a ≤ b + c :=
(le_add_iff_sub_left_le _ _ _).mpr

@[hott] theorem sub_left_le_of_le_add {a b c : A} : a ≤ b + c → a - b ≤ c :=
(le_add_iff_sub_left_le _ _ _).mp

@[hott] theorem le_add_iff_sub_right_le : a ≤ b + c ↔ a - c ≤ b :=
have H: a ≤ b + c ↔ a - c ≤ b + c - c, from iff.symm (add_le_add_right_iff _ _ _),
by rwr [sub_eq_add_neg (b+c) c, add_neg_cancel_right] at H; exact H

@[hott] theorem le_add_of_sub_right_le {a b c : A} : a - c ≤ b → a ≤ b + c :=
(le_add_iff_sub_right_le _ _ _).mpr

@[hott] theorem sub_right_le_of_le_add {a b c : A} : a ≤ b + c → a - c ≤ b :=
(le_add_iff_sub_right_le _ _ _).mp

@[hott] theorem le_add_iff_neg_add_le_left : a ≤ b + c ↔ -b + a ≤ c :=
have H: a ≤ b + c ↔ -b + a ≤ -b + (b + c), from iff.symm (add_le_add_left_iff _ _ _),
by rwr neg_add_cancel_left at H; exact H

@[hott] theorem le_add_of_neg_add_le_left {a b c : A} : -b + a ≤ c → a ≤ b + c :=
(le_add_iff_neg_add_le_left _ _ _).mpr

@[hott] theorem neg_add_le_left_of_le_add {a b c : A} : a ≤ b + c → -b + a ≤ c :=
(le_add_iff_neg_add_le_left _ _ _).mp

@[hott] theorem le_add_iff_neg_add_le_right : a ≤ b + c ↔ -c + a ≤ b :=
by rwr add.comm; apply le_add_iff_neg_add_le_left

@[hott] theorem le_add_of_neg_add_le_right {a b c : A} : -c + a ≤ b → a ≤ b + c :=
(le_add_iff_neg_add_le_right _ _ _).mpr

@[hott] theorem neg_add_le_right_of_le_add {a b c : A} : a ≤ b + c → -c + a ≤ b :=
(le_add_iff_neg_add_le_right _ _ _).mp

@[hott] theorem le_add_iff_neg_le_sub_left : c ≤ a + b ↔ -a ≤ b - c :=
have H : c ≤ a + b ↔ -a + c ≤ b, from le_add_iff_neg_add_le _ _ _,
have H' : -a + c ≤ b ↔ -a ≤ b - c, from add_le_iff_le_sub_right _ _ _,
iff.trans H H'

@[hott] theorem le_add_of_neg_le_sub_left {a b c : A} : -a ≤ b - c → c ≤ a + b :=
(le_add_iff_neg_le_sub_left _ _ _).mpr

@[hott] theorem neg_le_sub_left_of_le_add {a b c : A} : c ≤ a + b → -a ≤ b - c :=
(le_add_iff_neg_le_sub_left _ _ _).mp

@[hott] theorem le_add_iff_neg_le_sub_right : c ≤ a + b ↔ -b ≤ a - c :=
by rwr add.comm; apply le_add_iff_neg_le_sub_left

@[hott] theorem le_add_of_neg_le_sub_right {a b c : A} : -b ≤ a - c → c ≤ a + b :=
(le_add_iff_neg_le_sub_right _ _ _).mpr

@[hott] theorem neg_le_sub_right_of_le_add {a b c : A} : c ≤ a + b → -b ≤ a - c :=
(le_add_iff_neg_le_sub_right _ _ _).mp

@[hott] theorem add_lt_iff_lt_neg_add_left : a + b < c ↔ b < -a + c :=
have H: a + b < c ↔ -a + (a + b) < -a + c, from iff.symm (add_lt_add_left_iff _ _ _),
begin rwr neg_add_cancel_left at H, exact H end

@[hott] theorem add_lt_of_lt_neg_add_left {a b c : A} : b < -a + c → a + b < c :=
(add_lt_iff_lt_neg_add_left _ _ _).mpr

@[hott] theorem lt_neg_add_left_of_add_lt {a b c : A} : a + b < c → b < -a + c :=
(add_lt_iff_lt_neg_add_left _ _ _).mp

@[hott] theorem add_lt_iff_lt_neg_add_right : a + b < c ↔ a < -b + c :=
by refine iff.trans _ (add_lt_iff_lt_neg_add_left _ _ _); rwr add.comm

@[hott] theorem add_lt_of_lt_neg_add_right {a b c : A} : a < -b + c → a + b < c :=
(add_lt_iff_lt_neg_add_right _ _ _).mpr

@[hott] theorem lt_neg_add_right_of_add_lt {a b c : A} : a + b < c → a < -b + c :=
(add_lt_iff_lt_neg_add_right _ _ _).mp

@[hott] theorem add_lt_iff_lt_sub_left : a + b < c ↔ b < c - a :=
begin
  rwr [sub_eq_add_neg, add.comm c],
  apply add_lt_iff_lt_neg_add_left
end

@[hott] theorem add_lt_of_lt_sub_left {a b c : A} : b < c - a → a + b < c :=
(add_lt_iff_lt_sub_left _ _ _).mpr

@[hott] theorem lt_sub_left_of_add_lt {a b c : A} : a + b < c → b < c - a :=
(add_lt_iff_lt_sub_left _ _ _).mp

@[hott] theorem add_lt_iff_lt_sub_right : a + b < c ↔ a < c - b :=
have H: a + b < c ↔ a + b - b < c - b, from iff.symm (add_lt_add_right_iff _ _ _),
by rwr [sub_eq_add_neg, add_neg_cancel_right] at H; exact H

@[hott] theorem add_lt_of_lt_sub_right {a b c : A} : a < c - b → a + b < c :=
(add_lt_iff_lt_sub_right _ _ _).mpr

@[hott] theorem lt_sub_right_of_add_lt {a b c : A} : a + b < c → a < c - b :=
(add_lt_iff_lt_sub_right _ _ _).mp

@[hott] theorem lt_add_iff_neg_add_lt_left : a < b + c ↔ -b + a < c :=
have H: a < b + c ↔ -b + a < -b + (b + c), from iff.symm (add_lt_add_left_iff _ _ _),
by rwr neg_add_cancel_left at H; exact H

@[hott] theorem lt_add_of_neg_add_lt_left {a b c : A} : -b + a < c → a < b + c :=
(lt_add_iff_neg_add_lt_left _ _ _).mpr

@[hott] theorem neg_add_lt_left_of_lt_add {a b c : A} : a < b + c → -b + a < c :=
(lt_add_iff_neg_add_lt_left _ _ _).mp

@[hott] theorem lt_add_iff_neg_add_lt_right : a < b + c ↔ -c + a < b :=
by rwr add.comm; apply lt_add_iff_neg_add_lt_left

@[hott] theorem lt_add_of_neg_add_lt_right {a b c : A} : -c + a < b → a < b + c :=
(lt_add_iff_neg_add_lt_right _ _ _).mpr

@[hott] theorem neg_add_lt_right_of_lt_add {a b c : A} : a < b + c → -c + a < b :=
(lt_add_iff_neg_add_lt_right _ _ _).mp

@[hott] theorem lt_add_iff_sub_lt_left : a < b + c ↔ a - b < c :=
by rwr [sub_eq_add_neg, add.comm a]; apply lt_add_iff_neg_add_lt_left

@[hott] theorem lt_add_of_sub_lt_left {a b c : A} : a - b < c → a < b + c :=
(lt_add_iff_sub_lt_left _ _ _).mpr

@[hott] theorem sub_lt_left_of_lt_add {a b c : A} : a < b + c → a - b < c :=
(lt_add_iff_sub_lt_left _ _ _).mp

@[hott] theorem lt_add_iff_sub_lt_right : a < b + c ↔ a - c < b :=
by refine iff.trans _ (lt_add_iff_sub_lt_left _ _ _); rwr add.comm

@[hott] theorem lt_add_of_sub_lt_right {a b c : A} : a - c < b → a < b + c :=
(lt_add_iff_sub_lt_right _ _ _).mpr

@[hott] theorem sub_lt_right_of_lt_add {a b c : A} : a < b + c → a - c < b :=
(lt_add_iff_sub_lt_right _ _ _).mp

@[hott] theorem sub_lt_of_sub_lt {a b c : A} : a - b < c → a - c < b :=
  begin
    intro H,
    apply sub_lt_left_of_lt_add,
    apply lt_add_of_sub_lt_right H
  end

@[hott] theorem sub_le_of_sub_le {a b c : A} : a - b ≤ c → a - c ≤ b :=
  begin
    intro H,
    apply sub_left_le_of_le_add,
    apply le_add_of_sub_right_le H
  end

-- TODO: the Isabelle library has varations on a + b ≤ b ↔ a ≤ 0
@[hott] theorem le_iff_le_of_sub_eq_sub {a b c d : A} (H : a - b = c - d) : a ≤ b ↔ c ≤ d :=
calc
  a ≤ b ↔ a - b ≤ 0   : iff.symm (sub_nonpos_iff_le a b)
    ... = (c - d ≤ 0) : by rwr H
    ... ↔ c ≤ d       : sub_nonpos_iff_le c d

@[hott] theorem lt_iff_lt_of_sub_eq_sub {a b c d : A} (H : a - b = c - d) : a < b ↔ c < d :=
calc
  a < b ↔ a - b < 0   : iff.symm (sub_neg_iff_lt a b)
    ... = (c - d < 0) : by rwr H
    ... ↔ c < d       : sub_neg_iff_lt c d

@[hott] theorem sub_le_sub_left {a b : A} (H : a ≤ b) (c : A) : c - b ≤ c - a :=
add_le_add_left (neg_le_neg H) c

@[hott] theorem sub_le_sub_right {a b : A} (H : a ≤ b) (c : A) : a - c ≤ b - c :=
add_le_add_right H (-c)

@[hott] theorem sub_le_sub {a b c d : A} (Hab : a ≤ b) (Hcd : c ≤ d) : a - d ≤ b - c :=
add_le_add Hab (neg_le_neg Hcd)

@[hott] theorem sub_lt_sub_left {a b : A} (H : a < b) (c : A) : c - b < c - a :=
add_lt_add_left (neg_lt_neg H) c

@[hott] theorem sub_lt_sub_right {a b : A} (H : a < b) (c : A) : a - c < b - c :=
add_lt_add_right H (-c)

@[hott] theorem sub_lt_sub {a b c d : A} (Hab : a < b) (Hcd : c < d) : a - d < b - c :=
add_lt_add Hab (neg_lt_neg Hcd)

@[hott] theorem sub_lt_sub_of_le_of_lt {a b c d : A} (Hab : a ≤ b) (Hcd : c < d) : a - d < b - c :=
add_lt_add_of_le_of_lt Hab (neg_lt_neg Hcd)

@[hott] theorem sub_lt_sub_of_lt_of_le {a b c d : A} (Hab : a < b) (Hcd : c ≤ d) : a - d < b - c :=
add_lt_add_of_lt_of_le Hab (neg_le_neg Hcd)

@[hott] theorem sub_le_self (a : A) {b : A} (H : b ≥ 0) : a - b ≤ a :=
calc
  a - b = a + -b : rfl
    ... ≤ a + 0  : add_le_add_left (neg_nonpos_of_nonneg H) a
    ... = a      : by rwr add_zero

@[hott] theorem sub_lt_self (a : A) {b : A} (H : b > 0) : a - b < a :=
calc
  a - b = a + -b : rfl
    ... < a + 0  : add_lt_add_left (neg_neg_of_pos H) a
    ... = a      : by rwr add_zero

@[hott] theorem add_le_add_three {a b c d e f : A} (H1 : a ≤ d) (H2 : b ≤ e) (H3 : c ≤ f) :
      a + b + c ≤ d + e + f :=
begin
  apply le.trans,
  apply add_le_add,
  apply add_le_add,
  repeat { assumption },
  apply le.refl
end

@[hott] theorem sub_le_of_nonneg {b : A} (H : b ≥ 0) : a - b ≤ a :=
 add_le_of_le_of_nonpos (le.refl a) (neg_nonpos_of_nonneg H)

@[hott] theorem sub_lt_of_pos {b : A} (H : b > 0) : a - b < a :=
 add_lt_of_le_of_neg (le.refl a) (neg_neg_of_pos H)

@[hott] theorem neg_add_neg_le_neg_of_pos {a : A} (H : a > 0) : -a + -a ≤ -a :=
by rwr [←neg_add]; exact neg_le_neg (le_add_of_nonneg_left (le_of_lt H))
end

/- linear ordered group with decidable order -/

@[hott, class] structure decidable_linear_ordered_mul_ab_group (A : Type _)
    extends ab_group A, decidable_linear_order A :=
    (mul_le_mul_left : Π a b, le a b → Π c, le (mul c a) (mul c b))
    (mul_lt_mul_left : Π a b, lt a b → Π c, lt (mul c a) (mul c b))

@[hott, class] def decidable_linear_ordered_ab_group : Type _ → Type _ :=
decidable_linear_ordered_mul_ab_group

@[hott, reducible, instance] def add_ab_group_of_decidable_linear_ordered_ab_group
  (A : Type _) [H : decidable_linear_ordered_ab_group A] : add_ab_group A :=
@decidable_linear_ordered_mul_ab_group.to_ab_group A H

@[hott, reducible, instance] def decidable_linear_order_of_decidable_linear_ordered_ab_group
  (A : Type _) [H : decidable_linear_ordered_ab_group A] :
  decidable_linear_order A :=
@decidable_linear_ordered_mul_ab_group.to_decidable_linear_order A H

@[hott, reducible, instance]
def decidable_linear_ordered_mul_ab_group.to_ordered_mul_ab_group
  (A : Type _) [s : decidable_linear_ordered_mul_ab_group A] : ordered_mul_ab_group A :=
{ le_of_lt := @le_of_lt A _,
  lt_of_le_of_lt := @lt_of_le_of_lt A _,
  lt_of_lt_of_le := @lt_of_lt_of_le A _, ..s }

@[hott, reducible, instance] def decidable_linear_ordered_ab_group.to_ordered_ab_group
   (A : Type _) [s : decidable_linear_ordered_ab_group A] : ordered_ab_group A :=
@decidable_linear_ordered_mul_ab_group.to_ordered_mul_ab_group A s

section
variables [s : decidable_linear_ordered_ab_group A]
variables {a b c d e : A}
include s

/- these can be generalized to a lattice ordered group -/

@[hott] theorem min_add_add_left : min (a + b) (a + c) = a + min b c :=
inverse (eq_min
  (show a + min b c ≤ a + b, from add_le_add_left (min_le_left _ _) _)
  (show a + min b c ≤ a + c, from add_le_add_left (min_le_right _ _) _)
  (λ d,
    assume H₁ : d ≤ a + b,
    assume H₂ : d ≤ a + c,
    have H : d - a ≤ min b c,
      from le_min (sub_left_le_of_le_add H₁) (sub_left_le_of_le_add H₂),
    show d ≤ a + min b c, from le_add_of_sub_left_le H))

@[hott] theorem min_add_add_right : min (a + c) (b + c) = min a b + c :=
by rwr [add.comm a c, add.comm b c, add.comm _ c]; apply min_add_add_left

@[hott] theorem max_add_add_left : max (a + b) (a + c) = a + max b c :=
inverse (eq_max
  (add_le_add_left (le_max_left _ _) _)
  (add_le_add_left (le_max_right _ _) _)
  (λ d H₁ H₂,
    have H : max b c ≤ d - a,
      from max_le (le_sub_left_of_add_le H₁) (le_sub_left_of_add_le H₂),
    show a + max b c ≤ d, from add_le_of_le_sub_left H))

@[hott] theorem max_add_add_right : max (a + c) (b + c) = max a b + c :=
by rwr [add.comm a c, add.comm b c, add.comm _ c]; apply max_add_add_left

@[hott] theorem max_neg_neg : max (-a) (-b) = - min a b  :=
inverse (eq_max
  (show -a ≤ -(min a b), from neg_le_neg (min_le_left _ _))
  (show -b ≤ -(min a b), from neg_le_neg (min_le_right _ _))
  (λ d,
    assume H₁ : -a ≤ d,
    assume H₂ : -b ≤ d,
    have H : -d ≤ min a b,
      from le_min (neg_le_of_neg_le H₁) (neg_le_of_neg_le H₂),
    show -(min a b) ≤ d, from neg_le_of_neg_le H))

@[hott] theorem min_eq_neg_max_neg_neg : min a b = - max (-a) (-b) :=
by rwr [max_neg_neg, neg_neg]

@[hott] theorem min_neg_neg : min (-a) (-b) = - max a b :=
by rwr [min_eq_neg_max_neg_neg, neg_neg, neg_neg]

@[hott] theorem max_eq_neg_min_neg_neg : max a b = - min (-a) (-b) :=
by rwr [min_neg_neg, neg_neg]

/- absolute value -/
variables {a b c}

@[hott] def abs (a : A) : A := max a (-a)

@[hott] theorem abs_of_nonneg (H : a ≥ 0) : abs a = a :=
have H' : -a ≤ a, from le.trans (neg_nonpos_of_nonneg H) H,
max_eq_left H'

@[hott] theorem abs_of_pos (H : a > 0) : abs a = a :=
abs_of_nonneg (le_of_lt H)

@[hott] theorem abs_of_nonpos (H : a ≤ 0) : abs a = -a :=
have H' : a ≤ -a, from le.trans H (neg_nonneg_of_nonpos H),
max_eq_right H'

@[hott] theorem abs_of_neg (H : a < 0) : abs a = -a := abs_of_nonpos (le_of_lt H)

@[hott] theorem abs_zero : abs 0 = (0:A) := abs_of_nonneg (le.refl _)

@[hott] theorem abs_neg (a : A) : abs (-a) = abs a :=
by delta hott.algebra.abs; rwr [max.comm, neg_neg]

@[hott] theorem abs_pos_of_pos (H : a > 0) : abs a > 0 :=
by rwr (abs_of_pos H); exact H

@[hott] theorem abs_pos_of_neg (H : a < 0) : abs a > 0 :=
by have := abs_pos_of_pos (neg_pos_of_neg H); rwra abs_neg at this

@[hott] theorem abs_sub (a b : A) : abs (a - b) = abs (b - a) :=
by rwr [←neg_sub, abs_neg]

@[hott] theorem ne_zero_of_abs_ne_zero {a : A} (H : abs a ≠ 0) : a ≠ 0 :=
begin intro Ha, apply H, rwr Ha, exact abs_zero end

/- these assume a linear order -/

@[hott] theorem eq_zero_of_neg_eq (H : -a = a) : a = 0 :=
lt.by_cases
  (assume H1 : a < 0,
    have H2: a > 0, by rwr ←H; exact neg_pos_of_neg H1,
    absurd H1 (lt.asymm H2))
  (assume H1 : a = 0, H1)
  (assume H1 : a > 0,
    have H2: a < 0, by rwr ←H; exact neg_neg_of_pos H1,
    absurd H1 (lt.asymm H2))

@[hott] theorem abs_nonneg (a : A) : abs a ≥ 0 :=
sum.elim (le.total 0 a)
  (assume H : 0 ≤ a, by rwr (abs_of_nonneg H); exact H)
  (assume H : a ≤ 0,
    calc
        0 ≤ -a    : neg_nonneg_of_nonpos H
      ... = abs a : (abs_of_nonpos H)⁻¹)

@[hott] theorem abs_abs (a : A) : abs (abs a) = abs a := abs_of_nonneg (abs_nonneg _)

@[hott] theorem le_abs_self (a : A) : a ≤ abs a :=
sum.elim (le.total 0 a)
  (assume H : 0 ≤ a, le_of_eq (abs_of_nonneg H)⁻¹)
  (assume H : a ≤ 0, le.trans H (abs_nonneg _))

@[hott] theorem neg_le_abs_self (a : A) : -a ≤ abs a :=
by refine le.trans (le_abs_self _) _; rwr [abs_neg]

@[hott] theorem eq_zero_of_abs_eq_zero (H : abs a = 0) : a = 0 :=
have H1 : a ≤ 0, from H ▸ le_abs_self a,
have H2 : -a ≤ 0, from H ▸ abs_neg a ▸ le_abs_self (-a),
le.antisymm H1 (nonneg_of_neg_nonpos H2)

@[hott] theorem abs_eq_zero_iff_eq_zero (a : A) : abs a = 0 ↔ a = 0 :=
iff.intro eq_zero_of_abs_eq_zero (assume H, ap abs H ⬝ abs_zero)

@[hott] theorem eq_of_abs_sub_eq_zero {a b : A} (H : abs (a - b) = 0) : a = b :=
have a - b = 0, from eq_zero_of_abs_eq_zero H,
show a = b, from eq_of_sub_eq_zero this

@[hott] theorem abs_pos_of_ne_zero (H : a ≠ 0) : abs a > 0 :=
sum.elim (lt_sum_gt_of_ne H) abs_pos_of_neg abs_pos_of_pos

@[hott] theorem abs.by_cases {P : A → Type _} {a : A} (H1 : P a) (H2 : P (-a)) : P (abs a) :=
sum.elim (le.total 0 a)
  (assume H : 0 ≤ a, (abs_of_nonneg H)⁻¹ ▸ H1)
  (assume H : a ≤ 0, (abs_of_nonpos H)⁻¹ ▸ H2)

-- @[hott] theorem abs_le_of_le_of_neg_le (H1 : a ≤ b) (H2 : -a ≤ b) : abs a ≤ b :=
-- abs.by_cases H1 H2

-- @[hott] theorem abs_lt_of_lt_of_neg_lt (H1 : a < b) (H2 : -a < b) : abs a < b :=
-- abs.by_cases H1 H2

-- the triangle inequality
section
-- @[hott] private lemma aux1 {a b : A} (H1 : a + b ≥ 0) (H2 : a ≥ 0) : abs (a + b) ≤ abs a + abs b :=
--   decidable.by_cases
--     (assume H3 : b ≥ 0,
--         calc
--           abs (a + b) ≤ abs (a + b)   : le.refl
--               ... = a + b             : by rwr (abs_of_nonneg H1)
--               ... = abs a + b         : by rwr (abs_of_nonneg H2)
--               ... = abs a + abs b     : by rwr (abs_of_nonneg H3))
--     (assume H3 : ¬ b ≥ 0,
--       have H4 : b ≤ 0, from le_of_lt (lt_of_not_ge H3),
--       calc
--         abs (a + b) = a + b     : by rwr (abs_of_nonneg H1)
--             ... = abs a + b     : by rwr (abs_of_nonneg H2)
--             ... ≤ abs a + 0     : add_le_add_left H4
--             ... ≤ abs a + -b    : add_le_add_left (neg_nonneg_of_nonpos H4)
--             ... = abs a + abs b : by rwr (abs_of_nonpos H4))

--   @[hott] private lemma aux2 {a b : A} (H1 : a + b ≥ 0) : abs (a + b) ≤ abs a + abs b :=
--   sum.elim (le.total b 0)
--     (assume H2 : b ≤ 0,
--       have H3 : ¬ a < 0, from
--         assume H4 : a < 0,
--         have H5 : a + b < 0, by rwr [←add_zero 0]; exact add_lt_add_of_lt_of_le H4 H2,
--         not_lt_of_ge H1 H5,
--       aux1 H1 (le_of_not_gt H3))
--     (assume H2 : 0 ≤ b,
--       begin
--         have H3 : abs (b + a) ≤ abs b + abs a,
--         begin
--           rwr add.comm at H1,
--           exact aux1 H1 H2
--         end,
--         rwr [add.comm, {abs a + _}add.comm],
--         exact H3
--       end)

--   @[hott] theorem abs_add_le_abs_add_abs (a b : A) : abs (a + b) ≤ abs a + abs b :=
--   sum.elim (le.total 0 (a + b))
--     (assume H2 : 0 ≤ a + b, aux2 H2)
--     (assume H2 : a + b ≤ 0,
--       have H3 : -a + -b = -(a + b), by rwr neg_add,
--       have H4 : -(a + b) ≥ 0, from iff.mpr (neg_nonneg_iff_nonpos (a+b)) H2,
--       have H5   : -a + -b ≥ 0, begin rwr -H3 at H4, exact H4 end,
--       calc
--         abs (a + b) = abs (-a + -b)   : by rwr [←abs_neg, neg_add]
--             ... ≤ abs (-a) + abs (-b) : aux2 H5
--             ... = abs a + abs b       : by rwr *abs_neg)

-- @[hott] theorem abs_sub_abs_le_abs_sub (a b : A) : abs a - abs b ≤ abs (a - b) :=
-- have H1 : abs a - abs b + abs b ≤ abs (a - b) + abs b, from
--   calc
--     abs a - abs b + abs b = abs a : by rwr sub_add_cancel
--       ... = abs (a - b + b)       : by rwr sub_add_cancel
--       ... ≤ abs (a - b) + abs b   : abs_add_le_abs_add_abs,
-- le_of_add_le_add_right H1

-- @[hott] theorem abs_sub_le (a b c : A) : abs (a - c) ≤ abs (a - b) + abs (b - c) :=
-- calc
--   abs (a - c) = abs (a - b + (b - c)) :  by rwr [*sub_eq_add_neg, add.assoc, neg_add_cancel_left]
--           ... ≤ abs (a - b) + abs (b - c) : abs_add_le_abs_add_abs

-- @[hott] theorem abs_add_three (a b c : A) : abs (a + b + c) ≤ abs a + abs b + abs c :=
--   begin
--     apply le.trans,
--     apply abs_add_le_abs_add_abs,
--     apply le.trans,
--     apply add_le_add_right,
--     apply abs_add_le_abs_add_abs,
--     apply le.refl
--   end

-- @[hott] theorem dist_bdd_within_interval {a b lb ub : A} (H : lb < ub) (Hal : lb ≤ a) (Hau : a ≤ ub)
--       (Hbl : lb ≤ b) (Hbu : b ≤ ub) : abs (a - b) ≤ ub - lb :=
-- begin
--   cases (decidable.em (b ≤ a)) with [Hba, Hba],
--   rwr (abs_of_nonneg (iff.mpr !sub_nonneg_iff_le Hba)),
--   apply sub_le_sub,
--   apply Hau,
--   apply Hbl,
--   rwr [abs_of_neg (iff.mpr !sub_neg_iff_lt (lt_of_not_ge Hba)), neg_sub],
--   apply sub_le_sub,
--   apply Hbu,
--   apply Hal
-- end

end
end

end algebra
end hott
