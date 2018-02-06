/-
Copyright (c) 2014 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
(Ported from standard library)
Authors: Floris van Doorn, Leonardo de Moura, Jeremy Avigad

Basic operations on the natural numbers.
-/
import hott.algebra.ring
universes u v w
hott_theory
namespace hott
open eq hott.algebra is_trunc nat unit hott.decidable hott.binary

namespace nat

-- /- a variant of add, defined by recursion on the first argument -/

-- @[hott] def addl (x y : ℕ) : ℕ :=
-- nat.rec_on x y (λ n r, succ r)
-- infix ` ⊕ ` := addl

-- @[hott] theorem addl_succ_right (n m : ℕ) : n ⊕ succ m = succ (n ⊕ m) :=
-- nat.rec_on n
--   rfl
--   (λ n₁ ih, calc
--     succ n₁ ⊕ succ m = succ (n₁ ⊕ succ m)   : rfl
--              ...     = succ (succ (n₁ ⊕ m)) : ih
--              ...     = succ (succ n₁ ⊕ m)   : rfl)

-- @[hott] theorem add_eq_addl (x : ℕ) : Πy, x + y = x ⊕ y :=
-- nat.rec_on x
--   (λ y, nat.rec_on y
--     rfl
--     (λ y₁ ih, calc
--       0 + succ y₁ = succ (0 + y₁)  : rfl
--            ...    = succ (0 ⊕ y₁) : {ih}
--            ...    = 0 ⊕ (succ y₁) : rfl))
--   (λ x₁ ih₁ y, nat.rec_on y
--     (calc
--       succ x₁ + 0  = succ (x₁ + 0)  : rfl
--                ... = succ (x₁ ⊕ 0) : {ih₁ 0}
--                ... = succ x₁ ⊕ 0   : rfl)
--     (λ y₁ ih₂, calc
--       succ x₁ + succ y₁ = succ (succ x₁ + y₁) : rfl
--                    ...  = succ (succ x₁ ⊕ y₁) : {ih₂}
--                    ...  = succ x₁ ⊕ succ y₁   : addl_succ_right))

/- successor and predecessor -/

@[hott, reducible] protected def code : ℕ → ℕ → Type
| 0        0        := unit
| 0        (succ m) := empty
| (succ n) 0        := empty
| (succ n) (succ m) := code n m

@[hott] protected def refl : Πn, nat.code n n
| 0        := star
| (succ n) := refl n

@[hott] protected def encode {n m : ℕ} (p : n = m) : nat.code n m :=
p ▸ nat.refl n

@[hott] protected def decode : Π(n m : ℕ), nat.code n m → n = m
| 0        0        := λc, idp
| 0        (succ l) := λc, empty.elim c
| (succ k) 0        := λc, empty.elim c
| (succ k) (succ l) := λc, ap succ (decode k l c)


@[hott] def succ_ne_zero (n : ℕ) : succ n ≠ 0 :=
nat.encode

@[hott, hsimp] def pred_zero : pred 0 = 0 :=
rfl

@[hott, hsimp] def pred_succ (n : ℕ) : pred (succ n) = n :=
rfl

@[hott] theorem eq_zero_sum_eq_succ_pred (n : ℕ) : n = 0 ⊎ n = succ (pred n) :=
begin
  hinduction n with n IH,
  { exact sum.inl rfl },
  { exact sum.inr rfl }
end

@[hott] theorem exists_eq_succ_of_ne_zero {n : ℕ} (H : n ≠ 0) : Σk : ℕ, n = succ k :=
sigma.mk (pred n) (sum.resolve_left (eq_zero_sum_eq_succ_pred n) H)

@[hott] def succ.inj {n m : ℕ} (H : succ n = succ m) : n = m :=
nat.decode n m (@nat.encode (succ n) (succ m) H)

@[hott] theorem eq_of_succ_eq_succ {n m : ℕ} (H : succ n = succ m) : n = m := succ.inj H

@[hott] theorem succ_ne_self {n : ℕ} : succ n ≠ n :=
begin
  induction n with n IH,
  { apply succ_ne_zero },
  { intro H, apply IH, apply succ.inj, exact H }
end

@[hott, instance, priority nat.prio] protected def has_decidable_eq : Π x y : nat, decidable (x = y)
| 0        0        := inl rfl
| (succ x) 0        := inr (succ_ne_zero x)
| 0        (succ y) := inr (ne.symm (succ_ne_zero y))
| (succ x) (succ y) :=
    match has_decidable_eq x y with
    | inl xeqy := inl (ap succ xeqy)
    | inr xney := inr (λH, xney (succ.inj H))
    end

@[hott] theorem discriminate {B : Type _} {n : ℕ} (H1: n = 0 → B) (H2 : Πm, n = succ m → B) : B :=
have H : n = n → B, begin induction n with n IH, exact H1, apply H2 end,
H rfl

@[hott] theorem two_step_rec_on {P : ℕ → Type _} (a : ℕ) (H1 : P 0) (H2 : P 1)
    (H3 : Π (n : ℕ) (IH1 : P n) (IH2 : P (succ n)), P (succ (succ n))) : P a :=
have stronger : P a × P (succ a), from
  nat.rec_on a
    (pair H1 H2)
    (λk IH,
      have IH1 : P k, from IH.fst,
      have IH2 : P (succ k), from IH.snd,
        pair IH2 (H3 k IH1 IH2)),
  stronger.fst

@[hott] theorem sub_induction {P : ℕ → ℕ → Type _} (n m : ℕ) (H1 : Πm, P 0 m)
   (H2 : Πn, P (succ n) 0) (H3 : Πn m, P n m → P (succ n) (succ m)) : P n m :=
have general : Πm, P n m, from nat.rec_on n H1
  (λk : ℕ,
    assume IH : Πm, P k m,
    λm : ℕ,
    nat.cases_on m (H2 k) (λl, (H3 k l (IH l)))),
general m

/- addition -/

@[hott, hsimp] protected def add_zero (n : ℕ) : n + 0 = n :=
rfl

@[hott, hsimp] def add_succ (n m : ℕ) : n + succ m = succ (n + m) :=
rfl

@[hott, hsimp] protected def zero_add (n : ℕ) : 0 + n = n :=
begin
  induction n with n IH,
    reflexivity,
    exact ap succ IH
end

@[hott, hsimp] def succ_add (n m : ℕ) : (succ n) + m = succ (n + m) :=
begin
  induction m with m IH,
    reflexivity,
    exact ap succ IH
end

@[hott, hsimp] protected def add_comm (n m : ℕ) : n + m = m + n :=
begin
  induction n with n IH,
  { apply nat.zero_add},
  { exact succ_add n m ⬝ ap succ IH}
end

@[hott] protected def add_add (n l k : ℕ) : n + l + k = n + (k + l) :=
begin
  induction l with l IH,
    reflexivity,
    exact succ_add (n + l) k ⬝ ap succ IH
end

@[hott] def succ_add_eq_succ_add (n m : ℕ) : succ n + m = n + succ m :=
succ_add n m

@[hott, hsimp] protected def add_assoc (n m k : ℕ) : (n + m) + k = n + (m + k) :=
begin
  induction k with k IH,
    reflexivity,
    exact ap succ IH
end

@[hott] protected theorem add_left_comm : Π (n m k : ℕ), n + (m + k) = m + (n + k) :=
left_comm nat.add_comm nat.add_assoc

@[hott] protected theorem add_right_comm : Π (n m k : ℕ), n + m + k = n + k + m :=
right_comm nat.add_comm nat.add_assoc

@[hott] protected def add_left_cancel {n m k : ℕ} : n + m = n + k → m = k :=
nat.rec_on n
  (λH : 0 + m = 0 + k,
    (nat.zero_add _)⁻¹ ⬝ H ⬝ nat.zero_add _)
  (λ(n : ℕ) (IH : n + m = n + k → m = k) (H : succ n + m = succ n + k),
    have succ (n + m) = succ (n + k),
    from calc
      succ (n + m) = succ n + m   : by rwr succ_add
               ... = succ n + k   : H
               ... = succ (n + k) : by rwr succ_add,
    have n + m = n + k, from succ.inj this,
    IH this)

@[hott] protected def add_right_cancel {n m k : ℕ} (H : n + m = k + m) : n = k :=
have H2 : m + n = m + k, from nat.add_comm _ _ ⬝ H ⬝ nat.add_comm _ _,
  nat.add_left_cancel H2

@[hott] theorem eq_zero_of_add_eq_zero_right {n m : ℕ} : n + m = 0 → n = 0 :=
nat.rec_on n
  (λ(H : 0 + m = 0), rfl)
  (λk IH,
    assume H : succ k + m = 0,
    absurd
      (show succ (k + m) = 0, from calc
         succ (k + m) = succ k + m : by rwr succ_add
                  ... = 0          : H)
      (succ_ne_zero _))

@[hott] theorem eq_zero_of_add_eq_zero_left {n m : ℕ} (H : n + m = 0) : m = 0 :=
eq_zero_of_add_eq_zero_right (nat.add_comm _ _ ⬝ H)

@[hott] theorem eq_zero_prod_eq_zero_of_add_eq_zero {n m : ℕ} (H : n + m = 0) : n = 0 × m = 0 :=
pair (eq_zero_of_add_eq_zero_right H) (eq_zero_of_add_eq_zero_left H)

@[hott, hsimp] theorem add_one (n : ℕ) : n + 1 = succ n := rfl

@[hott] theorem one_add (n : ℕ) : 1 + n = succ n :=
succ_add 0 n ⬝ ap succ (nat.zero_add n)

/- multiplication -/

@[hott, hsimp] protected def mul_zero (n : ℕ) : n * 0 = 0 :=
rfl

@[hott, hsimp] def mul_succ (n m : ℕ) : n * succ m = n * m + n :=
rfl

-- commutativity, distributivity, associativity, identity

@[hott, hsimp] protected def zero_mul (n : ℕ) : 0 * n = 0 :=
begin induction n with n IH, refl, exact IH end

@[hott, hsimp] def succ_mul (n m : ℕ) : succ n * m = n * m + m :=
begin
  hinduction m with m IH,
  { refl },
  { rwr [mul_succ, IH, add_succ, nat.add_assoc, nat.add_comm m n, ←nat.add_assoc] }
end

@[hott, hsimp] protected def mul_comm (n m : ℕ) : n * m = m * n :=
begin
  hinduction m with m IH,
  { rwr [nat.zero_mul] },
  { rwr [mul_succ, succ_mul, IH] }
end

@[hott] protected def right_distrib (n m k : ℕ) : (n + m) * k = n * k + m * k :=
begin
  hinduction k with k IH,
  { refl },
  { rwr [mul_succ, IH, nat.add_assoc (n*k), ←nat.add_assoc (m*k), nat.add_comm (m*k),
         nat.add_assoc n, ←nat.add_assoc (n*k)] }
end

@[hott] protected def left_distrib (n m k : ℕ) : n * (m + k) = n * m + n * k :=
calc
  n * (m + k) = (m + k) * n    : by rwr nat.mul_comm
          ... = m * n + k * n  : by rwr nat.right_distrib
          ... = n * m + k * n  : by rwr nat.mul_comm
          ... = n * m + n * k  : by rwr nat.mul_comm k n

@[hott, hsimp] protected def mul_assoc (n m k : ℕ) : (n * m) * k = n * (m * k) :=
begin
  hinduction k with k IH,
  { refl },
  { rwr [mul_succ, IH, ←nat.left_distrib] }
end

@[hott, hsimp] protected def mul_one (n : ℕ) : n * 1 = n :=
calc
  n * 1 = n * 0 + n : by rwr mul_succ
    ... = 0 + n     : by rwr nat.mul_zero
    ... = n         : by rwr nat.zero_add

@[hott, hsimp] protected def one_mul (n : ℕ) : 1 * n = n :=
calc
  1 * n = n * 1 : by rwr nat.mul_comm
    ... = n     : by rwr nat.mul_one

@[hott] theorem eq_zero_sum_eq_zero_of_mul_eq_zero {n m : ℕ} : n * m = 0 → n = 0 ⊎ m = 0 :=
begin
  intro H, hinduction n with n IH, { exact sum.inl rfl },
  induction m with m IH, { exact sum.inr rfl },
  apply empty.elim, exact succ_ne_zero _ H
end

@[hott, instance] protected def comm_semiring : hott.algebra.comm_semiring nat :=
{ add            := nat.add,
  add_assoc      := nat.add_assoc,
  zero           := nat.zero,
  zero_add       := nat.zero_add,
  add_zero       := nat.add_zero,
  add_comm       := nat.add_comm,
  mul            := nat.mul,
  mul_assoc      := nat.mul_assoc,
  one            := nat.succ nat.zero,
  one_mul        := nat.one_mul,
  mul_one        := nat.mul_one,
  left_distrib   := nat.left_distrib,
  right_distrib  := nat.right_distrib,
  zero_mul       := nat.zero_mul,
  mul_zero       := nat.mul_zero,
  mul_comm       := nat.mul_comm,
  is_set_carrier := by apply_instance }
end nat

section
open nat
@[hott] def iterate {A : Type _} (op : A → A) : ℕ → A → A
 | 0 := λ a, a
 | (succ k) := λ a, op (iterate k a)

notation f `^[`:80 n:0 `]`:0 := iterate f n
end
end hott
