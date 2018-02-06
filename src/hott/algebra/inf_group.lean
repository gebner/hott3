/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura

-/

import .binary

universes u v w
hott_theory
set_option old_structure_cmd true
namespace hott
open hott.binary is_trunc

variable {A : Type _}

/- inf_semigroup -/

namespace algebra

@[hott, class] structure inf_semigroup (A : Type _) extends has_mul A :=
(mul_assoc : Πa b c, mul (mul a b) c = mul a (mul b c))

@[hott] def mul.assoc [s : inf_semigroup A] (a b c : A) : a * b * c = a * (b * c) :=
inf_semigroup.mul_assoc _ _ _

@[hott, class] structure comm_inf_semigroup (A : Type _) extends inf_semigroup A :=
(mul_comm : Πa b, mul a b = mul b a)

@[hott] def mul.comm [s : comm_inf_semigroup A] (a b : A) : a * b = b * a :=
comm_inf_semigroup.mul_comm _ _

@[hott] theorem mul.left_comm [s : comm_inf_semigroup A] (a b c : A) : a * (b * c) = b * (a * c) :=
binary.left_comm (@mul.comm A _) (@mul.assoc A _) a b c

@[hott] theorem mul.right_comm [s : comm_inf_semigroup A] (a b c : A) : (a * b) * c = (a * c) * b :=
binary.right_comm (@mul.comm A _) (@mul.assoc A _) a b c

@[hott, class] structure left_cancel_inf_semigroup (A : Type _) extends inf_semigroup A :=
(mul_left_cancel : Πa b c, mul a b = mul a c → b = c)

@[hott] def mul.left_cancel [s : left_cancel_inf_semigroup A] {a b c : A} :
  a * b = a * c → b = c :=
left_cancel_inf_semigroup.mul_left_cancel _ _ _

@[hott, class] structure right_cancel_inf_semigroup (A : Type _) extends inf_semigroup A :=
(mul_right_cancel : Πa b c, mul a b = mul c b → a = c)

@[hott] def mul.right_cancel [s : right_cancel_inf_semigroup A] {a b c : A} :
  a * b = c * b → a = c :=
right_cancel_inf_semigroup.mul_right_cancel _ _ _

/- additive inf_semigroup -/

@[hott, class] def add_inf_semigroup : Type _ → Type _ := inf_semigroup

@[hott, reducible, instance] def has_add_of_add_inf_semigroup
  (A : Type _) [H : add_inf_semigroup A] : has_add A :=
has_add.mk (@inf_semigroup.mul A H)

@[hott] def add.assoc [s : add_inf_semigroup A] (a b c : A) : a + b + c = a + (b + c) :=
@mul.assoc A s a b c

@[hott, class] def add_comm_inf_semigroup : Type _ → Type _ := comm_inf_semigroup

@[hott, reducible, instance] def add_inf_semigroup_of_add_comm_inf_semigroup (A : Type _)
  [H : add_comm_inf_semigroup A] : add_inf_semigroup A :=
@comm_inf_semigroup.to_inf_semigroup A H

@[hott] def add.comm [s : add_comm_inf_semigroup A] (a b : A) : a + b = b + a :=
@mul.comm A s a b

@[hott] theorem add.left_comm [s : add_comm_inf_semigroup A] (a b c : A) :
  a + (b + c) = b + (a + c) :=
binary.left_comm (@add.comm A _) (@add.assoc A _) a b c

@[hott] theorem add.right_comm [s : add_comm_inf_semigroup A] (a b c : A) : (a + b) + c = (a + c) + b :=
binary.right_comm (@add.comm A _) (@add.assoc A _) a b c

@[hott, class] def add_left_cancel_inf_semigroup : Type _ → Type _ := left_cancel_inf_semigroup

@[hott, reducible, instance] def add_inf_semigroup_of_add_left_cancel_inf_semigroup (A : Type _)
  [H : add_left_cancel_inf_semigroup A] : add_inf_semigroup A :=
@left_cancel_inf_semigroup.to_inf_semigroup A H

@[hott] def add.left_cancel [s : add_left_cancel_inf_semigroup A] {a b c : A} :
  a + b = a + c → b = c :=
@mul.left_cancel A s a b c

@[hott, class] def add_right_cancel_inf_semigroup : Type _ → Type _ := right_cancel_inf_semigroup

@[hott, reducible, instance] def add_inf_semigroup_of_add_right_cancel_inf_semigroup (A : Type _)
  [H : add_right_cancel_inf_semigroup A] : add_inf_semigroup A :=
@right_cancel_inf_semigroup.to_inf_semigroup A H

@[hott] def add.right_cancel [s : add_right_cancel_inf_semigroup A] {a b c : A} :
  a + b = c + b → a = c :=
@mul.right_cancel A s a b c

/- inf_monoid -/

@[hott, class] structure inf_monoid (A : Type _) extends inf_semigroup A, has_one A :=
(one_mul : Πa, mul one a = a) (mul_one : Πa, mul a one = a)

@[hott] def one_mul [s : inf_monoid A] (a : A) : 1 * a = a := inf_monoid.one_mul _

@[hott] def mul_one [s : inf_monoid A] (a : A) : a * 1 = a := inf_monoid.mul_one _

@[hott, class] structure comm_inf_monoid (A : Type _) extends inf_monoid A, comm_inf_semigroup A

/- additive inf_monoid -/

@[hott, class] def add_inf_monoid : Type _ → Type _ := inf_monoid

@[hott, reducible, instance] def add_inf_semigroup_of_add_inf_monoid (A : Type _)
  [H : add_inf_monoid A] : add_inf_semigroup A :=
@inf_monoid.to_inf_semigroup A H

@[hott, reducible, instance] def has_zero_of_add_inf_monoid (A : Type _)
  [H : add_inf_monoid A] : has_zero A :=
has_zero.mk (@inf_monoid.one A H)

@[hott] def zero_add [s : add_inf_monoid A] (a : A) : 0 + a = a := @inf_monoid.one_mul A s a

@[hott] def add_zero [s : add_inf_monoid A] (a : A) : a + 0 = a := @inf_monoid.mul_one A s a

@[hott, class] def add_comm_inf_monoid : Type _ → Type _ := comm_inf_monoid

@[hott, reducible, instance] def add_inf_monoid_of_add_comm_inf_monoid (A : Type _)
  [H : add_comm_inf_monoid A] : add_inf_monoid A :=
@comm_inf_monoid.to_inf_monoid A H

@[hott, reducible, instance] def add_comm_inf_semigroup_of_add_comm_inf_monoid (A : Type _)
  [H : add_comm_inf_monoid A] : add_comm_inf_semigroup A :=
@comm_inf_monoid.to_comm_inf_semigroup A H

/- group -/

@[hott, class] structure inf_group (A : Type _) extends inf_monoid A, has_inv A :=
(mul_left_inv : Πa, mul (inv a) a = one)

-- Note: with more work, we could derive the axiom one_mul

section inf_group

variable [s : inf_group A]
include s

@[hott] def mul.left_inv (a : A) : a⁻¹ * a = 1 := inf_group.mul_left_inv _

@[hott] def inv_mul_cancel_left (a b : A) : a⁻¹ * (a * b) = b :=
by rwr [←mul.assoc, mul.left_inv, one_mul]

@[hott] def inv_mul_cancel_right (a b : A) : a * b⁻¹ * b = a :=
by rwr [mul.assoc, mul.left_inv, mul_one]

@[hott] def inv_eq_of_mul_eq_one {a b : A} (H : a * b = 1) : a⁻¹ = b :=
by rwr [←mul_one a⁻¹, ←H, inv_mul_cancel_left]

@[hott] theorem one_inv : (1 : A)⁻¹ = 1 := inv_eq_of_mul_eq_one (one_mul 1)

@[hott] def inv_inv (a : A) : (a⁻¹)⁻¹ = a := inv_eq_of_mul_eq_one (mul.left_inv a)

@[hott] theorem inv.inj {a b : A} (H : a⁻¹ = b⁻¹) : a = b :=
by rwr [←inv_inv a, H, inv_inv b]

@[hott] theorem inv_eq_inv_iff_eq (a b : A) : a⁻¹ = b⁻¹ ↔ a = b :=
iff.intro (assume H, inv.inj H) (assume H, ap _ H)

@[hott] theorem inv_eq_one_iff_eq_one (a : A) : a⁻¹ = 1 ↔ a = 1 :=
by refine iff.trans _ (inv_eq_inv_iff_eq a 1); rwr [one_inv]

@[hott] theorem inv_eq_one {a : A} (H : a = 1) : a⁻¹ = 1 :=
iff.mpr (inv_eq_one_iff_eq_one a) H

@[hott] theorem eq_one_of_inv_eq_one (a : A) : a⁻¹ = 1 → a = 1 :=
iff.mp (inv_eq_one_iff_eq_one _)

@[hott] theorem eq_inv_of_eq_inv {a b : A} (H : a = b⁻¹) : b = a⁻¹ :=
by rwr [H, inv_inv]

@[hott] theorem eq_inv_iff_eq_inv (a b : A) : a = b⁻¹ ↔ b = a⁻¹ :=
iff.intro eq_inv_of_eq_inv eq_inv_of_eq_inv

@[hott] theorem eq_inv_of_mul_eq_one {a b : A} (H : a * b = 1) : a = b⁻¹ :=
begin apply eq_inv_of_eq_inv, symmetry, exact inv_eq_of_mul_eq_one H end

@[hott] def mul.right_inv (a : A) : a * a⁻¹ = 1 :=
calc
  a * a⁻¹ = (a⁻¹)⁻¹ * a⁻¹ : by rwr inv_inv
      ... = 1             : mul.left_inv _

@[hott] theorem mul_inv_cancel_left (a b : A) : a * (a⁻¹ * b) = b :=
calc
  a * (a⁻¹ * b) = a * a⁻¹ * b : by rwr mul.assoc
    ... = 1 * b               : by rwr mul.right_inv
    ... = b                   : by rwr one_mul

@[hott] def mul_inv_cancel_right (a b : A) : a * b * b⁻¹ = a :=
calc
  a * b * b⁻¹ = a * (b * b⁻¹) : by rwr mul.assoc
    ... = a * 1 : by rwr mul.right_inv
    ... = a : by rwr mul_one

@[hott] theorem mul_inv (a b : A) : (a * b)⁻¹ = b⁻¹ * a⁻¹ :=
inv_eq_of_mul_eq_one
  (calc
    a * b * (b⁻¹ * a⁻¹) = a * (b * (b⁻¹ * a⁻¹)) : by rwr mul.assoc
      ... = a * a⁻¹                             : by rwr mul_inv_cancel_left
      ... = 1                                   : by rwr mul.right_inv)

@[hott] theorem eq_of_mul_inv_eq_one {a b : A} (H : a * b⁻¹ = 1) : a = b :=
calc
  a = a * b⁻¹ * b : by rwr inv_mul_cancel_right
    ... = 1 * b   : by rwr H
    ... = b       : by rwr one_mul

@[hott] theorem eq_mul_inv_of_mul_eq {a b c : A} (H : a * c = b) : a = b * c⁻¹ :=
by rwr [←H, mul_inv_cancel_right]

@[hott] theorem eq_inv_mul_of_mul_eq {a b c : A} (H : b * a = c) : a = b⁻¹ * c :=
by rwr [←H, inv_mul_cancel_left]

@[hott] theorem inv_mul_eq_of_eq_mul {a b c : A} (H : b = a * c) : a⁻¹ * b = c :=
by rwr [H, inv_mul_cancel_left]

@[hott] theorem mul_inv_eq_of_eq_mul {a b c : A} (H : a = c * b) : a * b⁻¹ = c :=
by rwr [H, mul_inv_cancel_right]

@[hott] theorem eq_mul_of_mul_inv_eq {a b c : A} (H : a * c⁻¹ = b) : a = b * c :=
by rwr [←inv_inv c]; exact eq_mul_inv_of_mul_eq H

@[hott] theorem eq_mul_of_inv_mul_eq {a b c : A} (H : b⁻¹ * a = c) : a = b * c :=
by rwr [←inv_inv b]; exact eq_inv_mul_of_mul_eq H

@[hott] theorem mul_eq_of_eq_inv_mul {a b c : A} (H : b = a⁻¹ * c) : a * b = c :=
by rwr [←inv_inv a]; exact inv_mul_eq_of_eq_mul H

@[hott] theorem mul_eq_of_eq_mul_inv {a b c : A} (H : a = c * b⁻¹) : a * b = c :=
by rwr [←inv_inv b]; exact mul_inv_eq_of_eq_mul H

@[hott] theorem mul_eq_iff_eq_inv_mul (a b c : A) : a * b = c ↔ b = a⁻¹ * c :=
iff.intro eq_inv_mul_of_mul_eq mul_eq_of_eq_inv_mul

@[hott] theorem mul_eq_iff_eq_mul_inv (a b c : A) : a * b = c ↔ a = c * b⁻¹ :=
iff.intro eq_mul_inv_of_mul_eq mul_eq_of_eq_mul_inv

@[hott] def mul_left_cancel {a b c : A} (H : a * b = a * c) : b = c :=
by rwr [←inv_mul_cancel_left a b, H, inv_mul_cancel_left]

@[hott] def mul_right_cancel {a b c : A} (H : a * b = c * b) : a = c :=
by rwr [←mul_inv_cancel_right a b, H, mul_inv_cancel_right]

@[hott] theorem mul_eq_one_of_mul_eq_one {a b : A} (H : b * a = 1) : a * b = 1 :=
by rwr [←inv_eq_of_mul_eq_one H, mul.left_inv]

@[hott] theorem mul_eq_one_iff_mul_eq_one (a b : A) : a * b = 1 ↔ b * a = 1 :=
iff.intro mul_eq_one_of_mul_eq_one mul_eq_one_of_mul_eq_one

-- @[hott] def conj_by (g a : A) := g * a * g⁻¹
-- @[hott] def is_conjugate (a b : A) := Σ x, conj_by x b = a

-- local infixl ` ~ ` := is_conjugate
-- local infixr ` ∘c `:55 := conj_by

-- @[hott] lemma conj_compose (f g a : A) : f ∘c g ∘c a = f*g ∘c a :=
--     calc f ∘c g ∘c a = f * (g * a * g⁻¹) * f⁻¹ : rfl
--     ... = f * (g * a) * g⁻¹ * f⁻¹ : by rwr [←mul.assoc]
--     ... = f * g * a * g⁻¹ * f⁻¹ : by rwr [←mul.assoc]
--     ... = f * g * a * (g⁻¹ * f⁻¹) : by rwr mul.assoc
--     ... = f * g * a * (f * g)⁻¹ : by rwr mul_inv

-- @[hott] lemma conj_id (a : A) : 1 ∘c a = a :=
--     calc 1 * a * 1⁻¹ = a * 1⁻¹ : by rwr one_mul
--     ... = a * 1 : by rwr one_inv
--     ... = a : by rwr mul_one

-- @[hott] lemma conj_one (g : A) : g ∘c 1 = 1 :=
--     calc g * 1 * g⁻¹ = g * g⁻¹ : by rwr mul_one
--     ... = 1 : by rwr mul.right_inv

-- @[hott] lemma conj_inv_cancel (g : A) : Π a, g⁻¹ ∘c g ∘c a = a :=
--     assume a, calc
--     g⁻¹ ∘c g ∘c a = g⁻¹*g ∘c a : by rwr conj_compose
--     ... = 1 ∘c a : by rwr mul.left_inv
--     ... = a : by rwr conj_id

-- @[hott] lemma conj_inv (g : A) : Π a, (g ∘c a)⁻¹ = g ∘c a⁻¹ :=
--   λa, calc
--   (g * a * g⁻¹)⁻¹ = g⁻¹⁻¹ * (g * a)⁻¹   : by rwr mul_inv
--               ... = g⁻¹⁻¹ * (a⁻¹ * g⁻¹) : by rwr mul_inv
--               ... = g⁻¹⁻¹ * a⁻¹ * g⁻¹   : by rwr mul.assoc
--               ... = g * a⁻¹ * g⁻¹       : by rwr inv_inv

-- @[hott] lemma is_conj.refl (a : A) : a ~ a := sigma.mk 1 (conj_id a)

-- @[hott] lemma is_conj.symm (a b : A) : a ~ b → b ~ a :=
--     assume Pab, obtain x (Pconj : x ∘c b = a), from Pab,
--     have Pxinv : x⁻¹ ∘c x ∘c b = x⁻¹ ∘c a,   begin congruence, assumption end,
--     sigma.mk x⁻¹ (inverse (conj_inv_cancel x b ▸ Pxinv))

-- @[hott] lemma is_conj.trans (a b c : A) : a ~ b → b ~ c → a ~ c :=
--     assume Pab, assume Pbc,
--     obtain x (Px : x ∘c b = a), from Pab,
--     obtain y (Py : y ∘c c = b), from Pbc,
--     sigma.mk (x*y) (calc
--     x*y ∘c c = x ∘c y ∘c c : conj_compose
--     ... = x ∘c b : Py
--     ... = a : Px)

@[hott, instance] def inf_group.to_left_cancel_inf_semigroup : left_cancel_inf_semigroup A :=
{ mul_left_cancel := @mul_left_cancel A s, ..s }

@[hott, instance] def inf_group.to_right_cancel_inf_semigroup : right_cancel_inf_semigroup A :=
{ mul_right_cancel := @mul_right_cancel A s, ..s }

@[hott] def one_unique {a : A} (H : Πb, a * b = b) : a = 1 :=
(mul_one _)⁻¹ ⬝ H 1

end inf_group

@[hott, class] structure ab_inf_group (A : Type _) extends inf_group A, comm_inf_monoid A

/- additive inf_group -/

@[hott, class] def add_inf_group : Type _ → Type _ := inf_group

@[hott, reducible, instance] def add_inf_semigroup_of_add_inf_group (A : Type _)
  [H : add_inf_group A] : add_inf_monoid A :=
@inf_group.to_inf_monoid A H

@[hott, reducible, instance] def has_neg_of_add_inf_group (A : Type _)
  [H : add_inf_group A] : has_neg A :=
has_neg.mk (@inf_group.inv A H)

section add_inf_group

variables [s : add_inf_group A]
include s

@[hott] def add.left_inv (a : A) : -a + a = 0 := @inf_group.mul_left_inv A s a

@[hott] def neg_add_cancel_left (a b : A) : -a + (a + b) = b :=
by rwr [←add.assoc, add.left_inv, zero_add]

@[hott] def neg_add_cancel_right (a b : A) : a + -b + b = a :=
by rwr [add.assoc, add.left_inv, add_zero]

@[hott] def neg_eq_of_add_eq_zero {a b : A} (H : a + b = 0) : -a = b :=
by rwr [←add_zero (-a), ←H, neg_add_cancel_left]

@[hott] def neg_zero : -0 = (0 : A) := neg_eq_of_add_eq_zero (zero_add 0)

@[hott] def neg_neg (a : A) : -(-a) = a := neg_eq_of_add_eq_zero (add.left_inv a)

@[hott] theorem eq_neg_of_add_eq_zero {a b : A} (H : a + b = 0) : a = -b :=
by rwr [←neg_eq_of_add_eq_zero H, neg_neg]

@[hott] theorem neg.inj {a b : A} (H : -a = -b) : a = b :=
calc
  a = -(-a) : by rwr neg_neg
... = -(-b) : by rwr H
... = b     : by rwr neg_neg

@[hott] theorem neg_eq_neg_iff_eq (a b : A) : -a = -b ↔ a = b :=
iff.intro (assume H, neg.inj H) (assume H, ap _ H)

@[hott] theorem eq_of_neg_eq_neg {a b : A} : -a = -b → a = b :=
  iff.mp (neg_eq_neg_iff_eq _ _)

@[hott] theorem neg_eq_zero_iff_eq_zero (a : A) : -a = 0 ↔ a = 0 :=
inv_eq_one_iff_eq_one a

@[hott] theorem eq_zero_of_neg_eq_zero {a : A} : -a = 0 → a = 0 :=
  iff.mp (neg_eq_zero_iff_eq_zero _)

@[hott] theorem eq_neg_of_eq_neg {a b : A} (H : a = -b) : b = -a :=
eq_inv_of_eq_inv H

@[hott] theorem eq_neg_iff_eq_neg (a b : A) : a = -b ↔ b = -a :=
iff.intro eq_neg_of_eq_neg eq_neg_of_eq_neg

@[hott] def add.right_inv (a : A) : a + -a = 0 :=
calc
  a + -a = -(-a) + -a : by rwr neg_neg
    ... = 0 : by rwr add.left_inv

@[hott] def add_neg_cancel_left (a b : A) : a + (-a + b) = b :=
by rwr [←add.assoc, add.right_inv, zero_add]

@[hott] def add_neg_cancel_right (a b : A) : a + b + -b = a :=
by rwr [add.assoc, add.right_inv, add_zero]

@[hott] theorem neg_add_rev (a b : A) : -(a + b) = -b + -a :=
neg_eq_of_add_eq_zero
  begin
    rwr [add.assoc, add_neg_cancel_left, add.right_inv]
  end

-- TODO: delete these in favor of sub rules?
@[hott] theorem eq_add_neg_of_add_eq {a b c : A} (H : a + c = b) : a = b + -c :=
eq_mul_inv_of_mul_eq H

@[hott] theorem eq_neg_add_of_add_eq {a b c : A} (H : b + a = c) : a = -b + c :=
eq_inv_mul_of_mul_eq H

@[hott] theorem neg_add_eq_of_eq_add {a b c : A} (H : b = a + c) : -a + b = c :=
inv_mul_eq_of_eq_mul H

@[hott] theorem add_neg_eq_of_eq_add {a b c : A} (H : a = c + b) : a + -b = c :=
mul_inv_eq_of_eq_mul H

@[hott] theorem eq_add_of_add_neg_eq {a b c : A} (H : a + -c = b) : a = b + c :=
eq_mul_of_mul_inv_eq H

@[hott] theorem eq_add_of_neg_add_eq {a b c : A} (H : -b + a = c) : a = b + c :=
eq_mul_of_inv_mul_eq H

@[hott] theorem add_eq_of_eq_neg_add {a b c : A} (H : b = -a + c) : a + b = c :=
mul_eq_of_eq_inv_mul H

@[hott] theorem add_eq_of_eq_add_neg {a b c : A} (H : a = c + -b) : a + b = c :=
mul_eq_of_eq_mul_inv H

@[hott] theorem add_eq_iff_eq_neg_add (a b c : A) : a + b = c ↔ b = -a + c :=
iff.intro eq_neg_add_of_add_eq add_eq_of_eq_neg_add

@[hott] theorem add_eq_iff_eq_add_neg (a b c : A) : a + b = c ↔ a = c + -b :=
iff.intro eq_add_neg_of_add_eq add_eq_of_eq_add_neg

@[hott] theorem add_left_cancel {a b c : A} (H : a + b = a + c) : b = c :=
calc b = -a + (a + b) : (neg_add_cancel_left _ _)⁻¹
   ... = -a + (a + c) : by rwr H
   ... = c : by rwr neg_add_cancel_left

@[hott] theorem add_right_cancel {a b c : A} (H : a + b = c + b) : a = c :=
calc a = (a + b) + -b : (add_neg_cancel_right _ _)⁻¹
   ... = (c + b) + -b : by rwr H
   ... = c : by rwr add_neg_cancel_right

@[hott, reducible, instance] def add_inf_group.to_add_left_cancel_inf_semigroup :
  add_left_cancel_inf_semigroup A :=
@inf_group.to_left_cancel_inf_semigroup A s

@[hott, reducible, instance] def add_inf_group.to_add_right_cancel_inf_semigroup :
  add_right_cancel_inf_semigroup A :=
@inf_group.to_right_cancel_inf_semigroup A s

@[hott] theorem add_neg_eq_neg_add_rev {a b : A} : a + -b = -(b + -a) :=
by rwr [neg_add_rev, neg_neg]

/- sub -/

-- TODO: derive corresponding facts for div in a field
@[hott, reducible] protected def algebra.sub (a b : A) : A := a + -b

@[hott, instance] def add_inf_group_has_sub : has_sub A :=
has_sub.mk algebra.sub

@[hott] def sub_eq_add_neg (a b : A) : a - b = a + -b := rfl

@[hott] def sub_self (a : A) : a - a = 0 := add.right_inv _

@[hott] theorem sub_add_cancel (a b : A) : a - b + b = a := neg_add_cancel_right _ _

@[hott] theorem add_sub_cancel (a b : A) : a + b - b = a := add_neg_cancel_right _ _

@[hott] theorem eq_of_sub_eq_zero {a b : A} (H : a - b = 0) : a = b :=
calc
  a = (a - b) + b : by rwr sub_add_cancel
    ... = 0 + b : by rwr H
    ... = b : by rwr zero_add

@[hott] theorem eq_iff_sub_eq_zero (a b : A) : a = b ↔ a - b = 0 :=
iff.intro (λH, by rwr [H, sub_self]) (assume H, eq_of_sub_eq_zero H)

@[hott] theorem zero_sub (a : A) : 0 - a = -a := zero_add _

@[hott] theorem sub_zero (a : A) : a - 0 = a :=
by rwr [sub_eq_add_neg, neg_zero, add_zero]

@[hott] theorem sub_neg_eq_add (a b : A) : a - (-b) = a + b :=
by change a + -(-b) = a + b; rwr neg_neg

@[hott] theorem neg_sub (a b : A) : -(a - b) = b - a :=
neg_eq_of_add_eq_zero
  (calc
    a - b + (b - a) = a - b + b - a : (add.assoc _ _ _)⁻¹
      ... = a - a                   : by rwr sub_add_cancel
      ... = 0                       : by rwr sub_self)

@[hott] theorem add_sub (a b c : A) : a + (b - c) = a + b - c := (add.assoc _ _ _)⁻¹

@[hott] theorem sub_add_eq_sub_sub_swap (a b c : A) : a - (b + c) = a - c - b :=
calc
  a - (b + c) = a + (-c - b) : by rwr [sub_eq_add_neg, neg_add_rev]
          ... = a - c - b    : (add.assoc _ _ _)⁻¹

@[hott] theorem sub_eq_iff_eq_add (a b c : A) : a - b = c ↔ a = c + b :=
iff.intro (assume H, eq_add_of_add_neg_eq H) (assume H, add_neg_eq_of_eq_add H)

@[hott] theorem eq_sub_iff_add_eq (a b c : A) : a = b - c ↔ a + c = b :=
iff.intro (assume H, add_eq_of_eq_add_neg H) (assume H, eq_add_neg_of_add_eq H)

@[hott] theorem eq_iff_eq_of_sub_eq_sub {a b c d : A} (H : a - b = c - d) : a = b ↔ c = d :=
calc
  a = b ↔ a - b = 0 : eq_iff_sub_eq_zero _ _
    ... ↔ c - d = 0 : by rwr H
    ... ↔ c = d     : iff.symm (eq_iff_sub_eq_zero c d)

@[hott] theorem eq_sub_of_add_eq {a b c : A} (H : a + c = b) : a = b - c :=
eq_add_neg_of_add_eq H

@[hott] theorem sub_eq_of_eq_add {a b c : A} (H : a = c + b) : a - b = c :=
add_neg_eq_of_eq_add H

@[hott] theorem eq_add_of_sub_eq {a b c : A} (H : a - c = b) : a = b + c :=
eq_add_of_add_neg_eq H

@[hott] theorem add_eq_of_eq_sub {a b c : A} (H : a = c - b) : a + b = c :=
add_eq_of_eq_add_neg H

@[hott] def zero_unique {a : A} (H : Πb, a + b = b) : a = 0 :=
(add_zero _)⁻¹ ⬝ H 0

end add_inf_group

@[hott, class] def add_ab_inf_group : Type _ → Type _ := ab_inf_group

@[hott, reducible, instance] def add_inf_group_of_add_ab_inf_group (A : Type _)
  [H : add_ab_inf_group A] : add_inf_group A :=
@ab_inf_group.to_inf_group A H

@[hott, reducible, instance] def add_comm_inf_monoid_of_add_ab_inf_group (A : Type _)
  [H : add_ab_inf_group A] : add_comm_inf_monoid A :=
@ab_inf_group.to_comm_inf_monoid A H

section add_ab_inf_group
variable [s : add_ab_inf_group A]
include s

@[hott] theorem sub_add_eq_sub_sub (a b c : A) : a - (b + c) = a - b - c :=
by rwr add.comm; apply sub_add_eq_sub_sub_swap

@[hott] theorem neg_add_eq_sub (a b : A) : -a + b = b - a := add.comm _ _

@[hott] theorem neg_add (a b : A) : -(a + b) = -a + -b := add.comm (-b) (-a) ▸ neg_add_rev a b

@[hott] theorem sub_add_eq_add_sub (a b c : A) : a - b + c = a + c - b := add.right_comm _ _ _

@[hott] theorem sub_sub (a b c : A) : a - b - c = a - (b + c) :=
by change a + -b + -c = _; rwr [add.assoc, ←neg_add]

@[hott] theorem add_sub_add_left_eq_sub (a b c : A) : (c + a) - (c + b) = a - b :=
by rwr [sub_add_eq_sub_sub, (add.comm c a), add_sub_cancel]

@[hott] theorem eq_sub_of_add_eq' {a b c : A} (H : c + a = b) : a = b - c :=
by apply eq_sub_of_add_eq; rwr add.comm; exact H

@[hott] theorem sub_eq_of_eq_add' {a b c : A} (H : a = b + c) : a - b = c :=
by apply sub_eq_of_eq_add; rwr add.comm; exact H

@[hott] theorem eq_add_of_sub_eq' {a b c : A} (H : a - b = c) : a = b + c :=
by rwr add.comm; apply eq_add_of_sub_eq; exact H

@[hott] theorem add_eq_of_eq_sub' {a b c : A} (H : b = c - a) : a + b = c :=
by rwr add.comm; apply add_eq_of_eq_sub; exact H

@[hott] theorem sub_sub_self (a b : A) : a - (a - b) = b :=
by rwr [sub_eq_add_neg, neg_sub, add.comm, sub_add_cancel]

@[hott] theorem add_sub_comm (a b c d : A) : a + b - (c + d) = (a - c) + (b - d) :=
by rwr [sub_add_eq_sub_sub, ←sub_add_eq_add_sub a c b, add_sub]

@[hott] theorem sub_eq_sub_add_sub (a b c : A) : a - b = c - b + (a - c) :=
by rwr [add_sub, sub_add_cancel] ⬝ add.comm _ _

@[hott] theorem neg_neg_sub_neg (a b : A) : - (-a - -b) = a - b :=
by rwr [neg_sub, sub_neg_eq_add, neg_add_eq_sub]
end add_ab_inf_group

@[hott] def inf_group_of_add_inf_group (A : Type _) [G : add_inf_group A] : inf_group A :=
{ mul             := has_add.add,
  mul_assoc       := add.assoc,
  one             := has_zero.zero _,
  one_mul         := zero_add,
  mul_one         := add_zero,
  inv             := has_neg.neg,
  mul_left_inv    := add.left_inv }

@[hott] theorem add.comm4 [s : add_comm_inf_semigroup A] :
  Π (n m k l : A), n + m + (k + l) = n + k + (m + l) :=
comm4 add.comm add.assoc

@[hott] def add1 [s : has_add A] [s' : has_one A] (a : A) : A := a + 1

@[hott] theorem add_comm_three [s : add_comm_inf_semigroup A] (a b c : A) : a + b + c = c + b + a :=
by rwr [add.comm a b, add.comm (b + a) c, add.assoc]

@[hott] theorem add_comm_four [s : add_comm_inf_semigroup A] (a b : A) :
  a + a + (b + b) = (a + b) + (a + b) :=
add.comm4 _ _ _ _

@[hott] theorem add_comm_middle [s : add_comm_inf_semigroup A] (a b c : A) :
  a + b + c = a + c + b :=
by rwr [add.assoc, add.comm b, ←add.assoc]

-- @[hott] theorem bit0_add_bit0 [s : add_comm_inf_semigroup A] (a b : A) : bit0 a + bit0 b = bit0 (a + b) :=
--   add_comm_four _ _

-- @[hott] theorem bit0_add_bit0_helper [s : add_comm_inf_semigroup A] (a b t : A) (H : a + b = t) :
--         bit0 a + bit0 b = bit0 t :=
--   by rwr -H; apply bit0_add_bit0

-- @[hott] theorem bit1_add_bit0 [s : add_comm_inf_semigroup A] [s' : has_one A] (a b : A) :
--         bit1 a + bit0 b = bit1 (a + b) :=
--   begin
--     rwr [↑bit0, ↑bit1, add_comm_middle], congruence, apply add_comm_four
--   end

-- @[hott] theorem bit1_add_bit0_helper [s : add_comm_inf_semigroup A] [s' : has_one A] (a b t : A)
--         (H : a + b = t) : bit1 a + bit0 b = bit1 t :=
--   by rwr -H; apply bit1_add_bit0

-- @[hott] theorem bit0_add_bit1 [s : add_comm_inf_semigroup A] [s' : has_one A] (a b : A) :
--         bit0 a + bit1 b = bit1 (a + b) :=
--   by rwr [{bit0 a + bit1 b}add.comm,{a + b}add.comm]; exact bit1_add_bit0 b a

-- @[hott] theorem bit0_add_bit1_helper [s : add_comm_inf_semigroup A] [s' : has_one A] (a b t : A)
--         (H : a + b = t) : bit0 a + bit1 b = bit1 t :=
--   by rwr -H; apply bit0_add_bit1

-- @[hott] theorem bit1_add_bit1 [s : add_comm_inf_semigroup A] [s' : has_one A] (a b : A) :
--         bit1 a + bit1 b = bit0 (add1 (a + b)) :=
--   begin
--     rwr ↑[bit0, bit1, add1, add.assoc],
--     rwr [*add.assoc, {_ + (b + 1)}add.comm, {_ + (b + 1 + _)}add.comm,
--       {_ + (b + 1 + _ + _)}add.comm, *add.assoc, {1 + a}add.comm, -{b + (a + 1)}add.assoc,
--       {b + a}add.comm, *add.assoc]
--   end

-- @[hott] theorem bit1_add_bit1_helper [s : add_comm_inf_semigroup A] [s' : has_one A] (a b t s: A)
--         (H : (a + b) = t) (H2 : add1 t = s) : bit1 a + bit1 b = bit0 s :=
--   begin rwr [←H2, ←H], apply bit1_add_bit1 end

-- @[hott] theorem bin_add_zero [s : add_inf_monoid A] (a : A) : a + zero = a := add_zero _

-- @[hott] theorem bin_zero_add [s : add_inf_monoid A] (a : A) : zero + a = a := zero_add _

-- @[hott] theorem one_add_bit0 [s : add_comm_inf_semigroup A] [s' : has_one A] (a : A) : one + bit0 a = bit1 a :=
--   begin rwr ↑[bit0, bit1], rwr add.comm end

-- @[hott] theorem bit0_add_one [s : has_add A] [s' : has_one A] (a : A) : bit0 a + one = bit1 a :=
--   rfl

-- @[hott] theorem bit1_add_one [s : has_add A] [s' : has_one A] (a : A) : bit1 a + one = add1 (bit1 a) :=
--   rfl

-- @[hott] theorem bit1_add_one_helper [s : has_add A] [s' : has_one A] (a t : A) (H : add1 (bit1 a) = t) :
--         bit1 a + one = t :=
--   by rwr -H

-- @[hott] theorem one_add_bit1 [s : add_comm_inf_semigroup A] [s' : has_one A] (a : A) :
--         one + bit1 a = add1 (bit1 a) := add.comm _ _

-- @[hott] theorem one_add_bit1_helper [s : add_comm_inf_semigroup A] [s' : has_one A] (a t : A)
--         (H : add1 (bit1 a) = t) : one + bit1 a = t :=
--   by rwr -H; apply one_add_bit1

-- @[hott] theorem add1_bit0 [s : has_add A] [s' : has_one A] (a : A) : add1 (bit0 a) = bit1 a :=
--   rfl

-- @[hott] theorem add1_bit1 [s : add_comm_inf_semigroup A] [s' : has_one A] (a : A) :
--         add1 (bit1 a) = bit0 (add1 a) :=
--   begin
--     rwr ↑[add1, bit1, bit0],
--     rwr [add.assoc, add_comm_four]
--   end

-- @[hott] theorem add1_bit1_helper [s : add_comm_inf_semigroup A] [s' : has_one A] (a t : A) (H : add1 a = t) :
--         add1 (bit1 a) = bit0 t :=
--   by rwr -H; apply add1_bit1

-- @[hott] theorem add1_one [s : has_add A] [s' : has_one A] : add1 (one : A) = bit0 one :=
--   rfl

-- @[hott] theorem add1_zero [s : add_inf_monoid A] [s' : has_one A] : add1 (zero : A) = one :=
--   begin
--     rwr [↑add1, zero_add]
--   end

-- @[hott] theorem one_add_one [s : has_add A] [s' : has_one A] : (one : A) + one = bit0 one :=
--   rfl

-- @[hott] theorem subst_into_sum [s : has_add A] (l r tl tr t : A) (prl : l = tl) (prr : r = tr)
--         (prt : tl + tr = t) : l + r = t :=
--    by rwr [prl, prr, prt]

-- @[hott] theorem neg_zero_helper [s : add_inf_group A] (a : A) (H : a = 0) : - a = 0 :=
--   by rwr [H, neg_zero]

end algebra
end hott
