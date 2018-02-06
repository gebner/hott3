/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura

Structures with multiplicative and additive components, including semirings, rings, and fields.
The development is modeled after Isabelle's library.
-/

import .group
universes u v w
hott_theory
set_option old_structure_cmd true

namespace hott
open algebra

variable {A : Type _}
namespace algebra
/- auxiliary classes -/

@[hott, class] structure distrib (A : Type _) extends has_mul A, has_add A :=
(left_distrib : Πa b c, mul a (add b c) = add (mul a b) (mul a c))
(right_distrib : Πa b c, mul (add a b) c = add (mul a c) (mul b c))

@[hott] def left_distrib [s : distrib A] (a b c : A) : a * (b + c) = a * b + a * c :=
distrib.left_distrib _ _ _

@[hott] def right_distrib [s: distrib A] (a b c : A) : (a + b) * c = a * c + b * c :=
distrib.right_distrib _ _ _

@[hott, class] structure mul_zero_class (A : Type _) extends has_mul A, has_zero A :=
(zero_mul : Πa, mul zero a = zero)
(mul_zero : Πa, mul a zero = zero)

@[hott] def zero_mul [s : mul_zero_class A] (a : A) : 0 * a = 0 := mul_zero_class.zero_mul _
@[hott] def mul_zero [s : mul_zero_class A] (a : A) : a * 0 = 0 := mul_zero_class.mul_zero _

@[hott, class] structure zero_ne_one_class (A : Type _) extends has_zero A, has_one A :=
(zero_ne_one : zero ≠ one)

@[hott] theorem zero_ne_one [s: zero_ne_one_class A] : 0 ≠ (1:A) := @zero_ne_one_class.zero_ne_one A s

/- semiring -/
@[hott] structure semiring (A : Type _) extends comm_monoid A renaming
  mul→add mul_assoc→add_assoc one→zero one_mul→zero_add mul_one→add_zero mul_comm→add_comm,
  monoid A, distrib A, mul_zero_class A

/- we make it a class now (and not as part of the structure) to avoid
  semiring.to_comm_monoid to be an instance -/
attribute [class] semiring

@[hott, reducible, instance] def add_comm_monoid_of_semiring (A : Type _)
  [H : semiring A] : add_comm_monoid A :=
@semiring.to_comm_monoid A H

@[hott, reducible, instance] def monoid_of_semiring (A : Type _)
  [H : semiring A] : monoid A :=
@semiring.to_monoid A H

@[hott, reducible, instance] def distrib_of_semiring (A : Type _)
  [H : semiring A] : distrib A :=
@semiring.to_distrib A H

@[hott, reducible, instance] def mul_zero_class_of_semiring (A : Type _)
  [H : semiring A] : mul_zero_class A :=
@semiring.to_mul_zero_class A H

section semiring
  variables [s : semiring A] (a b c : A)
  include s

  @[hott] theorem As {a b c : A} : a + b + c = a + (b + c) :=
  add.assoc _ _ _

  @[hott] theorem one_add_one_eq_two : 1 + 1 = 2 :> A :=
  by unfold bit0

  @[hott] theorem ne_zero_of_mul_ne_zero_right {a b : A} (H : a * b ≠ 0) : a ≠ 0 :=
  λthis,
  have a * b = 0, by rwr [this, zero_mul],
  H this

  @[hott] theorem ne_zero_of_mul_ne_zero_left {a b : A} (H : a * b ≠ 0) : b ≠ 0 :=
  λthis,
  have a * b = 0, by rwr [this, mul_zero],
  H this

  @[hott] theorem distrib_three_right (a b c d : A) : (a + b + c) * d = a * d + b * d + c * d :=
  by rwr [right_distrib, right_distrib]

  @[hott] theorem mul_two : a * 2 = a + a :=
  by rwr [←one_add_one_eq_two, left_distrib, mul_one]

  @[hott] theorem two_mul : 2 * a = a + a :=
  by rwr [←one_add_one_eq_two, right_distrib, one_mul]

end semiring

/- comm semiring -/

@[hott, class] structure comm_semiring (A : Type _) extends semiring A, comm_monoid A
-- TODO: we could also define a cancelative comm_semiring, i.e. satisfying
-- c ≠ 0 → c * a = c * b → a = b.

-- section comm_semiring
--   variables [s : comm_semiring A] (a b c : A)
--   include s

--   @[hott] protected def algebra.dvd (a b : A) : Type _ := Σc, b = a * c

--   @[hott, instance, priority 500] def comm_semiring_has_dvd : has_dvd A :=
--   has_dvd.mk algebra.dvd

--   @[hott] theorem dvd.intro {a b c : A} (H : a * c = b) : a ∣ b :=
--   sigma.mk _ H⁻¹

--   @[hott] theorem dvd_of_mul_right_eq {a b c : A} (H : a * c = b) : a ∣ b := dvd.intro H

--   @[hott] theorem dvd.intro_left {a b c : A} (H : c * a = b) : a ∣ b :=
--   by rwr mul.comm at H; exact dvd.intro H

--   @[hott] theorem dvd_of_mul_left_eq {a b c : A} (H : c * a = b) : a ∣ b := dvd.intro_left H

--   @[hott] theorem exists_eq_mul_right_of_dvd {a b : A} (H : a ∣ b) : Σc, b = a * c := H

--   @[hott] theorem dvd.elim {P : Type _} {a b : A} (H₁ : a ∣ b) (H₂ : Πc, b = a * c → P) : P :=
--   sigma.rec_on H₁ H₂

--   @[hott] theorem exists_eq_mul_left_of_dvd {a b : A} (H : a ∣ b) : Σc, b = c * a :=
--   dvd.elim H (take c, assume H1 : b = a * c, sigma.mk c (H1 ⬝ mul.comm _ _))

--   @[hott] theorem dvd.elim_left {P : Type _} {a b : A} (H₁ : a ∣ b) (H₂ : Πc, b = c * a → P) : P :=
--   sigma.rec_on (exists_eq_mul_left_of_dvd H₁) (take c, assume H₃ : b = c * a, H₂ c H₃)

--   @[hott] theorem dvd.refl : a ∣ a := dvd.intro (mul_one _)

--   @[hott] theorem dvd.trans {a b c : A} (H₁ : a ∣ b) (H₂ : b ∣ c) : a ∣ c :=
--   dvd.elim H₁
--     (take d, assume H₃ : b = a * d,
--       dvd.elim H₂
--         (take e, assume H₄ : c = b * e,
--           dvd.intro
--             (show a * (d * e) = c, by rwr [←mul.assoc, -H₃, H₄])))

--   @[hott] theorem eq_zero_of_zero_dvd {a : A} (H : 0 ∣ a) : a = 0 :=
--     dvd.elim H (take c, assume H' : a = 0 * c, H' ⬝ (zero_mul _))

--   @[hott] theorem dvd_zero : a ∣ 0 := dvd.intro (mul_zero _)

--   @[hott] theorem one_dvd : 1 ∣ a := dvd.intro (one_mul _)

--   @[hott] theorem dvd_mul_right : a ∣ a * b := dvd.intro rfl

--   @[hott] theorem dvd_mul_left : a ∣ b * a :=
--   by rwr mul.comm; apply dvd_mul_right

--   @[hott] theorem dvd_mul_of_dvd_left {a b : A} (H : a ∣ b) (c : A) : a ∣ b * c :=
--   dvd.elim H
--     (take d,
--       suppose b = a * d,
--       dvd.intro
--         (show a * (d * c) = b * c, from by rwr [←mul.assoc]; substvars))

--   @[hott] theorem dvd_mul_of_dvd_right {a b : A} (H : a ∣ b) (c : A) : a ∣ c * b :=
--   by rwr mul.comm; exact dvd_mul_of_dvd_left H _

--   @[hott] theorem mul_dvd_mul {a b c d : A} (dvd_ab : a ∣ b) (dvd_cd : c ∣ d) : a * c ∣ b * d :=
--   dvd.elim dvd_ab
--     (take e, suppose b = a * e,
--       dvd.elim dvd_cd
--         (take f, suppose d = c * f,
--           dvd.intro
--             (show a * c * (e * f) = b * d,
--              by rwr [mul.assoc, {c*_}mul.left_comm, -mul.assoc]; substvars)))

--   @[hott] theorem dvd_of_mul_right_dvd {a b c : A} (H : a * b ∣ c) : a ∣ c :=
--   dvd.elim H (take d, assume Habdc : c = a * b * d, dvd.intro ((mul.assoc _ _ _)⁻¹ ⬝ (Habdc _ _ _ _)⁻¹))

--   @[hott] theorem dvd_of_mul_left_dvd {a b c : A} (H : a * b ∣ c) : b ∣ c :=
--   by apply dvd_of_mul_right_dvd; rwr mul.comm; exact H

--   @[hott] theorem dvd_add {a b c : A} (Hab : a ∣ b) (Hac : a ∣ c) : a ∣ b + c :=
--   dvd.elim Hab
--     (take d, suppose b = a * d,
--       dvd.elim Hac
--         (take e, suppose c = a * e,
--           dvd.intro (show a * (d + e) = b + c,
--                      by rwr [left_distrib]; substvars)))
-- end comm_semiring

/- ring -/

@[hott] structure ring (A : Type _) extends ab_group A renaming mul→add mul_assoc→add_assoc
  one→zero one_mul→zero_add mul_one→add_zero inv→neg mul_left_inv→add_left_inv mul_comm→add_comm,
  monoid A, distrib A

/- we make it a class now (and not as part of the structure) to avoid
  ring.to_ab_group to be an instance -/
attribute [class] ring

@[hott, reducible, instance] def add_ab_group_of_ring (A : Type _)
  [H : ring A] : add_ab_group A :=
@ring.to_ab_group A H

@[hott, reducible, instance] def monoid_of_ring (A : Type _)
  [H : ring A] : monoid A :=
@ring.to_monoid A H

@[hott, reducible, instance] def distrib_of_ring (A : Type _)
  [H : ring A] : distrib A :=
@ring.to_distrib A H

@[hott] def ring.mul_zero [s : ring A] (a : A) : a * 0 = 0 :=
have a * 0 + 0 = a * 0 + a * 0, from calc
  a * 0 + 0 = a * 0         : by rwr add_zero
        ... = a * (0 + 0)   : by rwr add_zero
        ... = a * 0 + a * 0 : left_distrib a 0 0,
show a * 0 = 0, from (add.left_cancel this)⁻¹

@[hott] def ring.zero_mul [s : ring A] (a : A) : 0 * a = 0 :=
have 0 * a + 0 = 0 * a + 0 * a, from calc
  0 * a + 0 = 0 * a         : by rwr add_zero
        ... = (0 + 0) * a   : by rwr add_zero
        ... = 0 * a + 0 * a : right_distrib 0 0 a,
show 0 * a = 0, from  (add.left_cancel this)⁻¹

@[hott, reducible, instance] def ring.to_semiring [s : ring A] : semiring A :=
{ mul_zero := ring.mul_zero,
  zero_mul := ring.zero_mul, ..s}

section
variables [s : ring A] (a b c d e : A)
include s

@[hott] def neg_mul_eq_neg_mul : -(a * b) = -a * b :=
neg_eq_of_add_eq_zero
  begin
    rwr [←right_distrib, add.right_inv, zero_mul]
  end

@[hott] def neg_mul_eq_mul_neg : -(a * b) = a * -b :=
 neg_eq_of_add_eq_zero
   begin
     rwr [←left_distrib, add.right_inv, mul_zero]
   end

@[hott] def neg_mul_eq_neg_mul_symm : - a * b = - (a * b) := (neg_mul_eq_neg_mul _ _)⁻¹ᵖ
@[hott] def mul_neg_eq_neg_mul_symm : a * - b = - (a * b) := (neg_mul_eq_mul_neg _ _)⁻¹ᵖ

@[hott] theorem neg_mul_neg : -a * -b = a * b :=
calc
   -a * -b = -(a * -b) : by rwr ←neg_mul_eq_neg_mul
     ... = - -(a * b)  : by rwr ←neg_mul_eq_mul_neg
     ... = a * b       : by rwr neg_neg

@[hott] theorem neg_mul_comm : -a * b = a * -b :=
(neg_mul_eq_neg_mul _ _)⁻¹ ⬝ (neg_mul_eq_mul_neg _ _)

@[hott] def neg_eq_neg_one_mul : -a = - 1 * a :=
calc
  -a = -(1 * a)  : by rwr one_mul
    ... = - 1 * a : by rwr neg_mul_eq_neg_mul

@[hott] def mul_sub_left_distrib : a * (b - c) = a * b - a * c :=
calc
  a * (b - c) = a * b + a * -c : left_distrib _ _ _
    ... = a * b + - (a * c)    : by rwr ←neg_mul_eq_mul_neg
    ... = a * b - a * c        : rfl

@[hott] def mul_sub_right_distrib : (a - b) * c = a * c - b * c :=
calc
  (a - b) * c = a * c  + -b * c : right_distrib _ _ _
    ... = a * c + - (b * c)     : by rwr neg_mul_eq_neg_mul
    ... = a * c - b * c         : rfl

@[hott] theorem mul_add_eq_mul_add_iff_sub_mul_add_eq :
  a * e + c = b * e + d ↔ (a - b) * e + c = d :=
calc
  a * e + c = b * e + d ↔ a * e + c = d + b * e : by rwr add.comm (b*e)
    ... ↔ a * e + c - b * e = d : iff.symm (sub_eq_iff_eq_add _ _ _)
    ... ↔ a * e - b * e + c = d : by rwr sub_add_eq_add_sub
    ... ↔ (a - b) * e + c = d   : by rwr mul_sub_right_distrib

@[hott] theorem mul_add_eq_mul_add_of_sub_mul_add_eq :
  (a - b) * e + c = d → a * e + c = b * e + d :=
iff.mpr (mul_add_eq_mul_add_iff_sub_mul_add_eq _ _ _ _ _)

@[hott] theorem sub_mul_add_eq_of_mul_add_eq_mul_add :
  a * e + c = b * e + d → (a - b) * e + c = d :=
iff.mp (mul_add_eq_mul_add_iff_sub_mul_add_eq _ _ _ _ _)

@[hott] theorem mul_neg_one_eq_neg : a * (- 1) = -a :=
  have a + a * - 1 = 0, from calc
    a + a * - 1 = a * 1 + a * - 1 : by rwr mul_one
           ... = a * (1 + - 1)   : by rwr left_distrib
           ... = a * 0          : by rwr add.right_inv
           ... = 0              : by rwr mul_zero,
  (neg_eq_of_add_eq_zero this)⁻¹

@[hott] theorem ne_zero_prod_ne_zero_of_mul_ne_zero {a b : A} (H : a * b ≠ 0) : a ≠ 0 × b ≠ 0 :=
  have H1 : a ≠ 0, from
    (λthis,
      have a * b = 0, by rwr [this, zero_mul],
      absurd this H),
  have b ≠ 0, from
    (λthis,
      have a * b = 0, by rwr [this, mul_zero],
      absurd this H),
  prod.mk H1 this
end

@[hott, class] structure comm_ring (A : Type _) extends ring A, comm_semigroup A

@[hott, reducible, instance] def comm_ring.to_comm_semiring [s : comm_ring A] :
  comm_semiring A :=
{ mul_zero := mul_zero,
  zero_mul := zero_mul, ..s }

section
  variables [s : comm_ring A] (a b c d e : A)
  include s

  @[hott] theorem mul_self_sub_mul_self_eq : a * a - b * b = (a + b) * (a - b) :=
  begin
    change a * a + - (b * b) = (a + b) * (a + - b),
    rwr [left_distrib, right_distrib, right_distrib, add.assoc],
    rwr [←add.assoc (b*a),
             ←neg_mul_eq_mul_neg, ←neg_mul_eq_mul_neg, mul.comm a b, add.right_inv, zero_add]
  end

  @[hott] theorem mul_self_sub_one_eq : a * a - 1 = (a + 1) * (a - 1) :=
  by rwr [←mul_self_sub_mul_self_eq, mul_one]

  -- @[hott] theorem dvd_neg_iff_dvd : (a ∣ -b) ↔ (a ∣ b) :=
  -- iff.intro
  --   (suppose a ∣ -b,
  --     dvd.elim this
  --       (take c, suppose -b = a * c,
  --         dvd.intro
  --           (show a * -c = b,
  --            by rwr [←neg_mul_eq_mul_neg, -this, neg_neg])))
  --   (suppose a ∣ b,
  --     dvd.elim this
  --       (take c, suppose b = a * c,
  --         dvd.intro
  --           (show a * -c = -b,
  --            by rwr [←neg_mul_eq_mul_neg, -this])))

  -- @[hott] theorem dvd_neg_of_dvd : (a ∣ b) → (a ∣ -b) :=
  --   iff.mpr (dvd_neg_iff_dvd _ _)

  -- @[hott] theorem dvd_of_dvd_neg : (a ∣ -b) → (a ∣ b) :=
  --   iff.mp (dvd_neg_iff_dvd _ _)

  -- @[hott] theorem neg_dvd_iff_dvd : (-a ∣ b) ↔ (a ∣ b) :=
  -- iff.intro
  --   (suppose -a ∣ b,
  --     dvd.elim this
  --       (take c, suppose b = -a * c,
  --         dvd.intro
  --           (show a * -c = b, by rwr [←neg_mul_comm, this])))
  --   (suppose a ∣ b,
  --     dvd.elim this
  --       (take c, suppose b = a * c,
  --         dvd.intro
  --           (show -a * -c = b, by rwr [neg_mul_neg, this])))

  -- @[hott] theorem neg_dvd_of_dvd : (a ∣ b) → (-a ∣ b) :=
  --   iff.mpr (neg_dvd_iff_dvd _ _)

  -- @[hott] theorem dvd_of_neg_dvd : (-a ∣ b) → (a ∣ b) :=
  --   iff.mp (neg_dvd_iff_dvd _ _)

  -- @[hott] theorem dvd_sub (H₁ : (a ∣ b)) (H₂ : (a ∣ c)) : (a ∣ b - c) :=
  -- dvd_add H₁ (dvd_neg_of_dvd H₂)
end

/- integral domains -/

@[hott, class] structure no_zero_divisors (A : Type _) extends has_mul A, has_zero A :=
(eq_zero_sum_eq_zero_of_mul_eq_zero : Πa b, mul a b = zero → a = zero ⊎ b = zero)

@[hott] def eq_zero_sum_eq_zero_of_mul_eq_zero {A : Type _} [s : no_zero_divisors A] {a b : A}
    (H : a * b = 0) : a = 0 ⊎ b = 0 :=
no_zero_divisors.eq_zero_sum_eq_zero_of_mul_eq_zero _ _ H

@[hott, class] structure integral_domain (A : Type _) extends comm_ring A, no_zero_divisors A,
    zero_ne_one_class A

section
  variables [s : integral_domain A] (a b c d e : A)
  include s

  @[hott] theorem mul_ne_zero {a b : A} (H1 : a ≠ 0) (H2 : b ≠ 0) : a * b ≠ 0 :=
  λthis,
    sum.elim (eq_zero_sum_eq_zero_of_mul_eq_zero this) (assume H3, H1 H3) (assume H4, H2 H4)

  -- @[hott] theorem eq_of_mul_eq_mul_right {a b c : A} (Ha : a ≠ 0) (H : b * a = c * a) : b = c :=
  -- have b * a - c * a = 0, from iff.mp (eq_iff_sub_eq_zero _ _) H,
  -- have (b - c) * a = 0, by rwr [mul_sub_right_distrib, this],
  -- have b - c = 0, from sum_resolve_left (eq_zero_sum_eq_zero_of_mul_eq_zero this) Ha,
  -- iff.elim_right (eq_iff_sub_eq_zero _ _) this

  -- @[hott] theorem eq_of_mul_eq_mul_left {a b c : A} (Ha : a ≠ 0) (H : a * b = a * c) : b = c :=
  -- have a * b - a * c = 0, from iff.mp (eq_iff_sub_eq_zero _ _) H,
  -- have a * (b - c) = 0, by rwr [mul_sub_left_distrib, this],
  -- have b - c = 0, from sum_resolve_right (eq_zero_sum_eq_zero_of_mul_eq_zero this) Ha,
  -- iff.elim_right (eq_iff_sub_eq_zero _ _) this

  -- -- TODO: do we want the iff versions?

  -- @[hott] theorem eq_zero_of_mul_eq_self_right {a b : A} (H₁ : b ≠ 1) (H₂ : a * b = a) : a = 0 :=
  -- have b - 1 ≠ 0, by intro this; apply H₁; rwr zero_add; apply eq_add_of_sub_eq; exact this,
  -- have a * b - a = 0, by rwr H₂; apply sub_self,
  -- have a * (b - 1) = 0, by rwr [mul_sub_left_distrib, mul_one]; apply this,
  --   show a = 0, from sum_resolve_left (eq_zero_sum_eq_zero_of_mul_eq_zero this) `b - 1 ≠ 0`

  -- @[hott] theorem eq_zero_of_mul_eq_self_left {a b : A} (H₁ : b ≠ 1) (H₂ : b * a = a) : a = 0 :=
  -- by apply eq_zero_of_mul_eq_self_right H₁; by rwr mul.comm; exact H₂

  -- @[hott] theorem mul_self_eq_mul_self_iff (a b : A) : a * a = b * b ↔ a = b ⊎ a = -b :=
  -- iff.intro
  --   (suppose a * a = b * b,
  --     have (a - b) * (a + b) = 0,
  --       by rwr [mul.comm, -mul_self_sub_mul_self_eq, this, sub_self],
  --     have a - b = 0 ⊎ a + b = 0, from eq_zero_sum_eq_zero_of_mul_eq_zero this,
  --     sum.elim this
  --       (suppose a - b = 0, sum.inl (eq_of_sub_eq_zero this))
  --       (suppose a + b = 0, sum.inr (eq_neg_of_add_eq_zero this)))
  --   (suppose a = b ⊎ a = -b, sum.elim this
  --     (suppose a = b,  by rwr this)
  --     (suppose a = -b, by rwr [this, neg_mul_neg]))

  -- @[hott] theorem mul_self_eq_one_iff (a : A) : a * a = 1 ↔ a = 1 ⊎ a = - 1 :=
  -- have a * a = 1 * 1 ↔ a = 1 ⊎ a = - 1, from mul_self_eq_mul_self_iff a 1,
  -- by rwr mul_one at this; exact this

  -- -- TODO: c - b * c → c = 0 ⊎ b = 1 and variants

  -- @[hott] theorem dvd_of_mul_dvd_mul_left {a b c : A} (Ha : a ≠ 0) (Hdvd : (a * b ∣ a * c)) : (b ∣ c) :=
  -- dvd.elim Hdvd
  --   (take d,
  --     suppose a * c = a * b * d,
  --     have b * d = c, by apply eq_of_mul_eq_mul_left Ha; rwr [mul.assoc, this],
  --     dvd.intro this)

  -- @[hott] theorem dvd_of_mul_dvd_mul_right {a b c : A} (Ha : a ≠ 0) (Hdvd : (b * a ∣ c * a)) : (b ∣ c) :=
  -- dvd.elim Hdvd
  --   (take d,
  --     suppose c * a = b * a * d,
  --     have b * d * a = c * a, from by rwr [mul.right_comm, -this],
  --     have b * d = c, from eq_of_mul_eq_mul_right Ha this,
  --     dvd.intro this)
end

namespace norm_num

-- @[hott] theorem mul_zero [s : mul_zero_class A] (a : A) : a * zero = zero :=
--   by rwr [↑zero, mul_zero]

-- @[hott] theorem zero_mul [s : mul_zero_class A] (a : A) : zero * a = zero :=
--   by rwr [↑zero, zero_mul]

-- @[hott] theorem mul_one [s : monoid A] (a : A) : a * one = a :=
--   by rwr [↑one, mul_one]

-- @[hott] theorem mul_bit0 [s : distrib A] (a b : A) : a * (bit0 b) = bit0 (a * b) :=
--   by rwr [↑bit0, left_distrib]

-- @[hott] theorem mul_bit0_helper [s : distrib A] (a b t : A) (H : a * b = t) : a * (bit0 b) = bit0 t :=
--   by rwr ←H; apply mul_bit0

-- @[hott] theorem mul_bit1 [s : semiring A] (a b : A) : a * (bit1 b) = bit0 (a * b) + a :=
--   by rwr [↑bit1, ↑bit0, +left_distrib, ↑one, mul_one]

-- @[hott] theorem mul_bit1_helper [s : semiring A] (a b s t : A) (Hs : a * b = s) (Ht : bit0 s + a  = t) :
--         a * (bit1 b) = t :=
--   begin rwr [←Ht, -Hs, mul_bit1] end

-- @[hott] theorem subst_into_prod [s : has_mul A] (l r tl tr t : A) (prl : l = tl) (prr : r = tr)
--         (prt : tl * tr = t) :
--         l * r = t :=
--    by rwr [prl, prr, prt]

-- @[hott] theorem mk_cong (op : A → A) (a b : A) (H : a = b) : op a = op b :=
--   by congruence; exact H

-- @[hott] theorem mk_eq (a : A) : a = a := rfl

-- @[hott] theorem neg_add_neg_eq_of_add_add_eq_zero [s : add_ab_group A] (a b c : A) (H : c + a + b = 0) :
--         -a + -b = c :=
--   begin
--     apply add_neg_eq_of_eq_add,
--     apply neg_eq_of_add_eq_zero,
--     rwr [add.comm, add.assoc, add.comm b, -add.assoc, H]
--   end

-- @[hott] theorem neg_add_neg_helper [s : add_ab_group A] (a b c : A) (H : a + b = c) : -a + -b = -c :=
--   begin apply iff.mp (neg_eq_neg_iff_eq _ _), rwr [neg_add, *neg_neg, H] end

-- @[hott] theorem neg_add_pos_eq_of_eq_add [s : add_ab_group A] (a b c : A) (H : b = c + a) : -a + b = c :=
--   begin apply neg_add_eq_of_eq_add, rwr add.comm, exact H end

-- @[hott] theorem neg_add_pos_helper1 [s : add_ab_group A] (a b c : A) (H : b + c = a) : -a + b = -c :=
--   begin apply neg_add_eq_of_eq_add, apply eq_add_neg_of_add_eq H end

-- @[hott] theorem neg_add_pos_helper2 [s : add_ab_group A] (a b c : A) (H : a + c = b) : -a + b = c :=
--   begin apply neg_add_eq_of_eq_add, rwr H end

-- @[hott] theorem pos_add_neg_helper [s : add_ab_group A] (a b c : A) (H : b + a = c) : a + b = c :=
--   by rwr [add.comm, H]

-- @[hott] theorem sub_eq_add_neg_helper [s : add_ab_group A] (t₁ t₂ e w₁ w₂: A) (H₁ : t₁ = w₁)
--         (H₂ : t₂ = w₂) (H : w₁ + -w₂ = e) : t₁ - t₂ = e :=
--   by rwr [sub_eq_add_neg, H₁, H₂, H]

-- @[hott] theorem pos_add_pos_helper [s : add_ab_group A] (a b c h₁ h₂ : A) (H₁ : a = h₁) (H₂ : b = h₂)
--         (H : h₁ + h₂ = c) : a + b = c :=
--   by rwr [H₁, H₂, H]

-- @[hott] theorem subst_into_subtr [s : add_group A] (l r t : A) (prt : l + -r = t) : l - r = t :=
--    by rwr [sub_eq_add_neg, prt]

-- @[hott] theorem neg_neg_helper [s : add_group A] (a b : A) (H : a = -b) : -a = b :=
--   by rwr [H, neg_neg]

-- @[hott] theorem neg_mul_neg_helper [s : ring A] (a b c : A) (H : a * b = c) : (-a) * (-b) = c :=
--   begin rwr [neg_mul_neg, H] end

-- @[hott] theorem neg_mul_pos_helper [s : ring A] (a b c : A) (H : a * b = c) : (-a) * b = -c :=
--   begin rwr [←neg_mul_eq_neg_mul, H] end

-- @[hott] theorem pos_mul_neg_helper [s : ring A] (a b c : A) (H : a * b = c) : a * (-b) = -c :=
--   begin rwr [←neg_mul_comm, -neg_mul_eq_neg_mul, H] end

end norm_num
end algebra
end hott
