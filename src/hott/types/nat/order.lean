/-
Copyright (c) 2014 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Leonardo de Moura, Jeremy Avigad

The order relation on the natural numbers.
-/
import .basic ...algebra.ordered_ring
universes u v w
hott_theory
namespace hott
open hott.algebra nat sum

namespace nat

/- lt and le -/

inductive le (a : ℕ) : ℕ → Type
| nat_refl : le a
| step : Π {b}, le b → le (succ b)

@[hott, instance, priority nat.prio] def nat_has_le : has_le nat := has_le.mk nat.le

@[hott, refl] protected def le_refl : Π a : nat, a ≤ a :=
le.nat_refl

@[hott, reducible] protected def lt (n m : ℕ) := succ n ≤ m
@[hott, instance, priority nat.prio] def nat_has_lt : has_lt nat := has_lt.mk nat.lt

@[hott] protected def le_of_eq {n m : ℕ} (p : n = m) : n ≤ m :=
by rwr p; apply le_refl

@[hott] def le_succ (n : ℕ) : n ≤ succ n := le.step (nat.le_refl _)

@[hott] def pred_le (n : ℕ) : pred n ≤ n := by cases n; repeat { constructor }

@[hott, hsimp] def le_succ_iff_unit (n : ℕ) : n ≤ succ n ↔ unit :=
iff_unit_intro (le_succ n)

@[hott, hsimp] def pred_le_iff_unit (n : ℕ) : pred n ≤ n ↔ unit :=
iff_unit_intro (pred_le n)

@[hott] protected def le_trans {n m k : ℕ} (H1 : n ≤ m) (H2 : m ≤ k) : n ≤ k :=
begin hinduction H2 with k H2 IH, exact H1, exact le.step IH end

@[hott] def le_succ_of_le {n m : ℕ} (H : n ≤ m) : n ≤ succ m := nat.le_trans H (le_succ _)

@[hott] def le_of_succ_le {n m : ℕ} (H : succ n ≤ m) : n ≤ m := nat.le_trans (le_succ _) H

@[hott] protected def le_of_lt {n m : ℕ} (H : n < m) : n ≤ m := le_of_succ_le H

@[hott] def succ_le_succ {n m : ℕ} (H : n ≤ m) : succ n ≤ succ m :=
begin hinduction H with k H2 IH, reflexivity, exact le.step IH end

@[hott] def pred_le_pred {n m : ℕ} (H : n ≤ m) : pred n ≤ pred m :=
begin hinduction H with k H2 IH, reflexivity, exact nat.le_trans IH (pred_le k) end

@[hott] def le_of_succ_le_succ {n m : ℕ} : succ n ≤ succ m → n ≤ m :=
pred_le_pred

@[hott] theorem le_succ_of_pred_le {n m : ℕ} : pred n ≤ m → n ≤ succ m :=
nat.cases_on n le.step (λa, succ_le_succ)

@[hott] def not_succ_le_zero (n : ℕ) : ¬succ n ≤ 0 :=
by intro H; cases H

@[hott] theorem succ_le_zero_iff_empty (n : ℕ) : succ n ≤ 0 ↔ empty :=
iff_empty_intro (not_succ_le_zero _)

@[hott] def not_succ_le_self {n : ℕ} : ¬succ n ≤ n :=
begin
  hinduction n with n IH, apply not_succ_le_zero,
  intro H, apply IH, exact le_of_succ_le_succ H,
end

@[hott, hsimp] theorem succ_le_self_iff_empty (n : ℕ) : succ n ≤ n ↔ empty :=
iff_empty_intro not_succ_le_self

@[hott] def zero_le (n : ℕ) : 0 ≤ n :=
begin hinduction n with n IH, reflexivity, exact le.step IH end

@[hott, hsimp] theorem zero_le_iff_unit (n : ℕ) : 0 ≤ n ↔ unit :=
iff_unit_intro (zero_le n)

@[hott] theorem lt.step {n m : ℕ} : n < m → n < succ m := le.step

@[hott] def zero_lt_succ (n : ℕ) : 0 < succ n :=
succ_le_succ (zero_le _)

@[hott, hsimp] theorem zero_lt_succ_iff_unit (n : ℕ) : 0 < succ n ↔ unit :=
iff_unit_intro (zero_lt_succ n)

@[hott] protected theorem lt_trans {n m k : ℕ} (H1 : n < m) : m < k → n < k :=
nat.le_trans (le.step H1)

@[hott] protected def lt_of_le_of_lt {n m k : ℕ} (H1 : n ≤ m) : m < k → n < k :=
nat.le_trans (succ_le_succ H1)

@[hott] protected def lt_of_lt_of_le {n m k : ℕ} : n < m → m ≤ k → n < k := nat.le_trans

@[hott] protected def lt_irrefl (n : ℕ) : ¬n < n := not_succ_le_self

@[hott] theorem lt_self_iff_empty (n : ℕ) : n < n ↔ empty :=
iff_empty_intro (λ H, absurd H (nat.lt_irrefl n))

@[hott] theorem self_lt_succ (n : ℕ) : n < succ n := nat.le_refl _

@[hott, hsimp] theorem self_lt_succ_iff_unit (n : ℕ) : n < succ n ↔ unit :=
iff_unit_intro (self_lt_succ n)

@[hott] theorem lt.base (n : ℕ) : n < succ n := nat.le_refl _

@[hott] theorem le_lt_antisymm {n m : ℕ} (H1 : n ≤ m) (H2 : m < n) : empty :=
nat.lt_irrefl _ (nat.lt_of_le_of_lt H1 H2)

@[hott] protected def le_antisymm {n m : ℕ} (H1 : n ≤ m) (H2 : m ≤ n) : n = m :=
begin
  hinduction H1 with m H1 IH, reflexivity,
  exact absurd (nat.lt_of_le_of_lt H1 H2) (nat.lt_irrefl _)
end

@[hott] theorem lt_le_antisymm {n m : ℕ} (H1 : n < m) (H2 : m ≤ n) : empty :=
le_lt_antisymm H2 H1

@[hott] protected theorem nat.lt_asymm {n m : ℕ} (H1 : n < m) : ¬ m < n :=
le_lt_antisymm (nat.le_of_lt H1)

@[hott] theorem not_lt_zero (a : ℕ) : ¬ a < 0 := not_succ_le_zero _

@[hott, hsimp] theorem lt_zero_iff_empty (a : ℕ) : a < 0 ↔ empty :=
iff_empty_intro (not_lt_zero a)

@[hott] protected def eq_sum_lt_of_le {a b : ℕ} (H : a ≤ b) : a = b ⊎ a < b :=
le.cases_on H (inl rfl) (λn h, inr (succ_le_succ h))

@[hott] protected def le_of_eq_sum_lt {a b : ℕ} (H : a = b ⊎ a < b) : a ≤ b :=
begin hinduction H with H H, exact nat.le_of_eq H, exact nat.le_of_lt H end

@[hott] theorem succ_lt_succ {a b : ℕ} : a < b → succ a < succ b :=
succ_le_succ

@[hott] def lt_of_succ_lt {a b : ℕ} : succ a < b → a < b :=
le_of_succ_le

@[hott] theorem lt_of_succ_lt_succ {a b : ℕ} : succ a < succ b → a < b :=
le_of_succ_le_succ

@[hott, instance, priority nat.prio] def decidable_le : Π a b : nat, decidable (a ≤ b)  :=
λa, nat.rec (λm, (decidable.inl (zero_le _)))
    (λn IH m, nat.cases_on m (decidable.inr (not_succ_le_zero n))
      (λm, decidable.rec (λH, decidable.inl (succ_le_succ H))
        (λH, decidable.inr (λa, H (le_of_succ_le_succ a))) (IH m))) a

@[hott, instance, priority nat.prio] def decidable_lt : Π a b : nat, decidable (a < b) :=
λ a b, decidable_le (succ a) b

@[hott] protected def lt_sum_ge (a b : ℕ) : a < b ⊎ a ≥ b :=
nat.rec (inr (zero_le _)) (λn H, sum.rec
  (λh, inl (le_succ_of_le h))
  (λh, sum.rec_on (nat.eq_sum_lt_of_le h) (λe, inl (nat.le_of_eq (ap succ e⁻¹))) inr) H) b

@[hott] protected def lt_ge_by_cases {a b : ℕ} {P : Type _} (H1 : a < b → P) (H2 : a ≥ b → P) : P :=
hott.decidable.by_cases H1 (λh, H2 (sum.rec_on (nat.lt_sum_ge a b) (λa, absurd a h) (λa, a)))

@[hott] protected def lt_by_cases {a b : ℕ} {P : Type _} (H1 : a < b → P) (H2 : a = b → P)
  (H3 : b < a → P) : P :=
nat.lt_ge_by_cases H1 (λh₁,
  nat.lt_ge_by_cases H3 (λh₂, H2 (nat.le_antisymm h₂ h₁)))

@[hott] protected theorem lt_trichotomy (a b : ℕ) : a < b ⊎ a = b ⊎ b < a :=
nat.lt_by_cases (λH, inl H) (λH, inr (inl H)) (λH, inr (inr H))

@[hott] protected theorem eq_sum_lt_of_not_lt {a b : ℕ} (hnlt : ¬ a < b) : a = b ⊎ b < a :=
sum.rec_on (nat.lt_trichotomy a b)
  (λ hlt, absurd hlt hnlt)
  (λ h, h)

@[hott] def lt_succ_of_le {a b : ℕ} : a ≤ b → a < succ b :=
succ_le_succ

@[hott] def lt_of_succ_le {a b : ℕ} (h : succ a ≤ b) : a < b := h

@[hott] def succ_le_of_lt {a b : ℕ} (h : a < b) : succ a ≤ b := h

@[hott, hsimp] theorem succ_sub_succ_eq_sub (a b : ℕ) : succ a - succ b = a - b :=
nat.rec (by simp) (λ b, ap pred) b

@[hott] theorem sub_eq_succ_sub_succ (a b : ℕ) : a - b = succ a - succ b :=
(succ_sub_succ_eq_sub _ _)⁻¹

@[hott, hsimp] theorem zero_sub_eq_zero (a : ℕ) : 0 - a = 0 :=
nat.rec rfl (λ a, ap pred) a

@[hott] theorem zero_eq_zero_sub (a : ℕ) : 0 = 0 - a :=
(zero_sub_eq_zero _)⁻¹

@[hott] theorem sub_le (a b : ℕ) : a - b ≤ a :=
nat.rec_on b (nat.le_refl _) (λ b₁, nat.le_trans (pred_le _))

@[hott, hsimp] theorem sub_le_iff_unit (a b : ℕ) : a - b ≤ a ↔ unit :=
iff_unit_intro (sub_le a b)

@[hott] theorem sub_lt {a b : ℕ} (H1 : 0 < a) (H2 : 0 < b) : a - b < a :=
nat.cases_on a (λh, absurd h (nat.lt_irrefl _))
  (λa h, succ_le_succ (nat.cases_on b (λh, absurd h (nat.lt_irrefl _))
    (λb c, nat.le_trans (nat.le_of_eq (succ_sub_succ_eq_sub a b)) (sub_le a b)) H2)) H1

@[hott] theorem sub_lt_succ (a b : ℕ) : a - b < succ a :=
lt_succ_of_le (sub_le _ _)

@[hott, hsimp] theorem sub_lt_succ_iff_unit (a b : ℕ) : a - b < succ a ↔ unit :=
iff_unit_intro (sub_lt_succ _ _)

@[hott] protected def le_of_lt_sum_eq {m n : ℕ} (H : m < n ⊎ m = n) : m ≤ n :=
nat.le_of_eq_sum_lt (sum.swap H)

@[hott] protected def lt_sum_eq_of_le {m n : ℕ} (H : m ≤ n) : m < n ⊎ m = n :=
sum.swap (nat.eq_sum_lt_of_le H)

@[hott] protected def le_iff_lt_sum_eq (m n : ℕ) : m ≤ n ↔ m < n ⊎ m = n :=
iff.intro nat.lt_sum_eq_of_le nat.le_of_lt_sum_eq

@[hott] protected def lt_of_le_prod_ne {m n : ℕ} (H1 : m ≤ n) : m ≠ n → m < n :=
sum.resolve_left (nat.eq_sum_lt_of_le H1)

@[hott] protected theorem lt_iff_le_prod_ne (m n : ℕ) : m < n ↔ m ≤ n × m ≠ n :=
iff.intro
  (λH, ⟨nat.le_of_lt H, λH1, nat.lt_irrefl n (nat.le_trans (nat.le_of_eq (ap succ H1⁻¹)) H)⟩)
  (λv, prod.rec nat.lt_of_le_prod_ne v)

@[hott] def le_add_right (n k : ℕ) : n ≤ n + k :=
begin hinduction k with k IH, reflexivity, exact le_succ_of_le IH end

@[hott] theorem le_add_left (n m : ℕ): n ≤ m + n :=
by rwr add.comm; apply le_add_right

@[hott] def le.intro {n m k : ℕ} (h : n + k = m) : n ≤ m :=
by rwr ←h; apply le_add_right

@[hott] def le.elim {n m : ℕ} (H : n ≤ m) : Σ k, n + k = m :=
begin
  hinduction H with m H IH, exact ⟨0, idp⟩, hinduction IH with k H2, exact ⟨succ k, ap succ H2⟩
end

@[hott] protected def le_total {m n : ℕ} : m ≤ n ⊎ n ≤ m :=
sum.imp_left nat.le_of_lt (nat.lt_sum_ge _ _)

/- addition -/

@[hott] protected def add_le_add_left {n m : ℕ} (H : n ≤ m) (k : ℕ) : k + n ≤ k + m :=
begin
  hinduction le.elim H with p l Hl,
  fapply le.intro, exact l, rwr ←Hl, apply nat.add_assoc
end

@[hott] protected theorem add_le_add_right {n m : ℕ} (H : n ≤ m) (k : ℕ) : n + k ≤ m + k :=
by rwr [nat.add_comm n k, nat.add_comm m k]; apply nat.add_le_add_left H

@[hott] protected def le_of_add_le_add_left {k n m : ℕ} (H : k + n ≤ k + m) : n ≤ m :=
begin
  hinduction le.elim H with p l Hl,
  exact le.intro (nat.add_left_cancel ((nat.add_assoc _ _ _)⁻¹ᵖ ⬝ Hl))
end

@[hott] protected def lt_of_add_lt_add_left {k n m : ℕ} (H : k + n < k + m) : n < m :=
let H' := nat.le_of_lt H in
nat.lt_of_le_prod_ne (nat.le_of_add_le_add_left H') (assume Heq, nat.lt_irrefl _ (Heq ▸ H))

@[hott] protected def add_lt_add_left {n m : ℕ} (H : n < m) (k : ℕ) : k + n < k + m :=
by apply lt_of_succ_le; rwr [←add_succ]; exact nat.add_le_add_left (succ_le_of_lt H) k

@[hott] protected def add_lt_add_right {n m : ℕ} (H : n < m) (k : ℕ) : n + k < m + k :=
by rwr [nat.add_comm n k, nat.add_comm m k]; apply nat.add_lt_add_left H

@[hott] protected def lt_add_of_pos_right {n k : ℕ} (H : k > 0) : n < n + k :=
nat.add_lt_add_left H n

/- multiplication -/

@[hott] def mul_le_mul_left {n m : ℕ} (k : ℕ) (H : n ≤ m) : k * n ≤ k * m :=
begin
  hinduction le.elim H with p l Hl,
  have : k * n + k * l = k * m, by rwr [←nat.left_distrib, Hl],
  exact le.intro this
end

@[hott] def mul_le_mul_right {n m : ℕ} (k : ℕ) (H : n ≤ m) : n * k ≤ m * k :=
by rwr [mul.comm n k, mul.comm m k]; exact mul_le_mul_left _ H

@[hott] protected theorem mul_le_mul {n m k l : ℕ} (H1 : n ≤ k) (H2 : m ≤ l) : n * m ≤ k * l :=
nat.le_trans (nat.mul_le_mul_right _ H1) (nat.mul_le_mul_left _ H2)

@[hott] protected def mul_lt_mul_of_pos_left {n m k : ℕ} (H : n < m) (Hk : k > 0) :
  k * n < k * m :=
begin
  apply nat.lt_of_lt_of_le (nat.lt_add_of_pos_right Hk),
  rwr ←mul_succ, exact nat.mul_le_mul_left k (succ_le_of_lt H)
end

@[hott] protected def mul_lt_mul_of_pos_right {n m k : ℕ} (H : n < m) (Hk : k > 0) :
  n * k < m * k :=
by rwr [mul.comm n k, mul.comm m k]; exact nat.mul_lt_mul_of_pos_left H Hk

/- nat is an instance of a linearly ordered semiring and a lattice -/

@[hott, instance] protected def decidable_linear_ordered_semiring :
  hott.algebra.decidable_linear_ordered_semiring ℕ :=
{ add_left_cancel            := @nat.add_left_cancel,
  add_right_cancel           := @nat.add_right_cancel,
  lt                         := nat.lt,
  le                         := nat.le,
  le_refl                    := nat.le_refl,
  le_trans                   := @nat.le_trans,
  le_antisymm                := @nat.le_antisymm,
  le_total                   := @nat.le_total,
  le_iff_lt_sum_eq           := @nat.le_iff_lt_sum_eq,
  le_of_lt                   := @nat.le_of_lt,
  lt_irrefl                  := @nat.lt_irrefl,
  lt_of_lt_of_le             := @nat.lt_of_lt_of_le,
  lt_of_le_of_lt             := @nat.lt_of_le_of_lt,
  lt_of_add_lt_add_left      := @nat.lt_of_add_lt_add_left,
  add_lt_add_left            := @nat.add_lt_add_left,
  add_le_add_left            := @nat.add_le_add_left,
  le_of_add_le_add_left      := @nat.le_of_add_le_add_left,
  zero_lt_one                := zero_lt_succ 0,
  mul_le_mul_of_nonneg_left  := (λa b c H1 H2, nat.mul_le_mul_left c H1),
  mul_le_mul_of_nonneg_right := (λa b c H1 H2, nat.mul_le_mul_right c H1),
  mul_lt_mul_of_pos_left     := @nat.mul_lt_mul_of_pos_left,
  mul_lt_mul_of_pos_right    := @nat.mul_lt_mul_of_pos_right,
  decidable_lt               := nat.decidable_lt, ..nat.comm_semiring }

@[hott, instance, priority nat.prio] def nat_has_dvd : has_dvd nat :=
has_dvd.mk has_dvd.dvd

@[hott] theorem add_pos_left {a : ℕ} (H : 0 < a) (b : ℕ) : 0 < a + b :=
@hott.algebra.add_pos_of_pos_of_nonneg _ _ a b H (zero_le _)

@[hott] theorem add_pos_right {a : ℕ} (H : 0 < a) (b : ℕ) : 0 < b + a :=
by rwr add.comm; apply add_pos_left H b

@[hott] theorem add_eq_zero_iff_eq_zero_prod_eq_zero {a b : ℕ} :
a + b = 0 ↔ a = 0 × b = 0 :=
@add_eq_zero_iff_eq_zero_prod_eq_zero_of_nonneg_of_nonneg _ _ a b (zero_le _) (zero_le _)

@[hott] theorem le_add_of_le_left {a b c : ℕ} (H : b ≤ c) : b ≤ a + c :=
@hott.algebra.le_add_of_nonneg_of_le _ _ a b c (zero_le _) H

@[hott] theorem le_add_of_le_right {a b c : ℕ} (H : b ≤ c) : b ≤ c + a :=
@hott.algebra.le_add_of_le_of_nonneg _ _ a b c H (zero_le _)

@[hott] theorem lt_add_of_lt_left {b c : ℕ} (H : b < c) (a : ℕ) : b < a + c :=
@hott.algebra.lt_add_of_nonneg_of_lt _ _ a b c (zero_le _) H

@[hott] theorem lt_add_of_lt_right {b c : ℕ} (H : b < c) (a : ℕ) : b < c + a :=
@hott.algebra.lt_add_of_lt_of_nonneg _ _ a b c H (zero_le _)

@[hott] theorem lt_of_mul_lt_mul_left {a b c : ℕ} (H : c * a < c * b) : a < b :=
@hott.algebra.lt_of_mul_lt_mul_left _ _ a b c H (zero_le _)

@[hott] theorem lt_of_mul_lt_mul_right {a b c : ℕ} (H : a * c < b * c) : a < b :=
@hott.algebra.lt_of_mul_lt_mul_right _ _ a b c H (zero_le _)

@[hott] theorem pos_of_mul_pos_left {a b : ℕ} (H : 0 < a * b) : 0 < b :=
@hott.algebra.pos_of_mul_pos_left _ _ a b H (zero_le _)

@[hott] theorem pos_of_mul_pos_right {a b : ℕ} (H : 0 < a * b) : 0 < a :=
@hott.algebra.pos_of_mul_pos_right _ _ a b H (zero_le _)

@[hott] theorem zero_le_one : (0:nat) ≤ 1 :=
dec_star

/- properties specific to nat -/

@[hott] theorem lt_intro {n m k : ℕ} (H : succ n + k = m) : n < m :=
lt_of_succ_le (le.intro H)

@[hott] theorem lt_elim {n m : ℕ} (H : n < m) : Σk, succ n + k = m :=
le.elim (succ_le_of_lt H)

@[hott] theorem lt_add_succ (n m : ℕ) : n < n + succ m :=
lt_intro (succ_add_eq_succ_add _ _)

@[hott] theorem eq_zero_of_le_zero {n : ℕ} (H : n ≤ 0) : n = 0 :=
begin
  hinduction le.elim H with p k Hk,
  exact eq_zero_of_add_eq_zero_right Hk
end

/- succ and pred -/

@[hott] def le_of_lt_succ {m n : nat} : m < succ n → m ≤ n :=
le_of_succ_le_succ

@[hott] theorem lt_iff_succ_le (m n : nat) : m < n ↔ succ m ≤ n :=
iff.rfl

@[hott] theorem lt_succ_iff_le (m n : nat) : m < succ n ↔ m ≤ n :=
iff.intro le_of_lt_succ lt_succ_of_le

@[hott] theorem self_le_succ (n : ℕ) : n ≤ succ n :=
le.intro (add_one _)

@[hott] theorem succ_le_sum_eq_of_le {n m : ℕ} : n ≤ m → succ n ≤ m ⊎ n = m :=
lt_sum_eq_of_le

@[hott] theorem pred_le_of_le_succ {n m : ℕ} : n ≤ succ m → pred n ≤ m :=
pred_le_pred

@[hott] theorem succ_le_of_le_pred {n m : ℕ} : succ n ≤ m → n ≤ pred m :=
pred_le_pred

@[hott] theorem pred_le_pred_of_le {n m : ℕ} : n ≤ m → pred n ≤ pred m :=
pred_le_pred

@[hott] theorem pre_lt_of_lt {n m : ℕ} : n < m → pred n < m :=
lt_of_le_of_lt (pred_le _)

@[hott] theorem lt_of_pred_lt_pred {n m : ℕ} (H : pred n < pred m) : n < m :=
lt_of_not_ge (λthis, not_lt_of_ge (pred_le_pred_of_le this) H)

@[hott] theorem le_sum_eq_succ_of_le_succ {n m : ℕ} (H : n ≤ succ m) : n ≤ m ⊎ n = succ m :=
sum.imp_left le_of_succ_le_succ (succ_le_sum_eq_of_le H)

@[hott] theorem le_pred_self (n : ℕ) : pred n ≤ n :=
pred_le n

@[hott] theorem succ_pos (n : ℕ) : 0 < succ n :=
zero_lt_succ _

@[hott] theorem succ_pred_of_pos {n : ℕ} (H : n > 0) : succ (pred n) = n :=
(sum.resolve_left (eq_zero_sum_eq_succ_pred n) (ne.symm (ne_of_lt H)))⁻¹

@[hott] theorem exists_eq_succ_of_lt {n : ℕ} : Π {m : ℕ}, n < m → Σk, m = succ k
| 0        H := absurd H (not_lt_zero _)
| (succ k) H := sigma.mk k rfl

@[hott] theorem lt_succ_self (n : ℕ) : n < succ n :=
lt.base n

@[hott] lemma lt_succ_of_lt {i j : nat} : i < j → i < succ j :=
λPlt, hott.algebra.lt.trans Plt (self_lt_succ j)

@[hott] lemma one_le_succ (n : ℕ) : 1 ≤ succ n :=
nat.succ_le_succ (zero_le _)

@[hott] lemma two_le_succ_succ (n : ℕ) : 2 ≤ succ (succ n) :=
nat.succ_le_succ (one_le_succ _)

/- other forms of induction -/

@[hott] protected def strong_rec_on {P : nat → Type _} (n : ℕ) (H : Πn, (Πm, m < n → P m) → P n) :
  P n :=
begin
  have : Π⦃m⦄, m < n → P m,
  { hinduction n with n IH; intros m Hm, cases Hm,
    hinduction (lt_sum_eq_of_le (le_of_lt_succ Hm)) with p H' H', exact IH H',
    hinduction H', exact H m IH },
  exact H n this
end

@[hott] protected theorem case_strong_rec_on {P : nat → Type _} (a : nat) (H0 : P 0)
  (Hind : Π(n : nat), (Πm, m ≤ n → P m) → P (succ n)) : P a :=
nat.strong_rec_on a
  (λn,
   show (Π m, m < n → P m) → P n, from
     nat.cases_on n
       (λthis, show P 0, from H0)
       (λn this,
         show P (succ n), from
           Hind n (λm, assume H1 : m ≤ n, this _ (lt_succ_of_le H1))))

/- pos -/

@[hott] theorem by_cases_zero_pos {P : ℕ → Type _} (y : ℕ) (H0 : P 0)
  (H1 : Π {y : nat}, y > 0 → P y) : P y :=
nat.cases_on y H0 (λy, H1 (succ_pos _))

@[hott] theorem eq_zero_sum_pos (n : ℕ) : n = 0 ⊎ n > 0 :=
begin hinduction n with n IH, exact inl idp, exact inr (zero_lt_succ n) end

@[hott] theorem pos_of_ne_zero {n : ℕ} (H : n ≠ 0) : n > 0 :=
sum.elim (eq_zero_sum_pos _) (λH2 : n = 0, empty.elim (H H2)) (λH2 : n > 0, H2)

@[hott] theorem ne_zero_of_pos {n : ℕ} (H : n > 0) : n ≠ 0 :=
ne.symm (ne_of_lt H)

@[hott] theorem exists_eq_succ_of_pos {n : ℕ} (H : n > 0) : Σl, n = succ l :=
exists_eq_succ_of_lt H

-- @[hott] theorem pos_of_dvd_of_pos {m n : ℕ} (H1 : m ∣ n) (H2 : n > 0) : m > 0 :=
-- pos_of_ne_zero
--   (λthis,
--    have n = 0, by apply eq_zero_of_zero_dvd; rwra ←this,
--    ne_of_lt H2 (by subst n))

/- multiplication -/

@[hott] theorem mul_lt_mul_of_le_of_lt {n m k l : ℕ} (Hk : k > 0) (H1 : n ≤ k) (H2 : m < l) :
  n * m < k * l :=
lt_of_le_of_lt (mul_le_mul_right m H1) (mul_lt_mul_of_pos_left H2 Hk)

@[hott] theorem mul_lt_mul_of_lt_of_le {n m k l : ℕ} (Hl : l > 0) (H1 : n < k) (H2 : m ≤ l) :
  n * m < k * l :=
lt_of_le_of_lt (mul_le_mul_left n H2) (mul_lt_mul_of_pos_right H1 Hl)

@[hott] theorem mul_lt_mul_of_le_of_le {n m k l : ℕ} (H1 : n < k) (H2 : m < l) : n * m < k * l :=
have H3 : n * m ≤ k * m, from mul_le_mul_right m (le_of_lt H1),
have H4 : k * m < k * l, from mul_lt_mul_of_pos_left H2 (lt_of_le_of_lt (zero_le _) H1),
lt_of_le_of_lt H3 H4

@[hott] theorem eq_of_mul_eq_mul_left {m k n : ℕ} (Hn : n > 0) (H : n * m = n * k) : m = k :=
have n * m ≤ n * k, by rwr H,
have H2 : m ≤ k,         from le_of_mul_le_mul_left this Hn,
have n * k ≤ n * m, by rwr H,
have k ≤ m,         from le_of_mul_le_mul_left this Hn,
le.antisymm H2 this

@[hott] theorem eq_of_mul_eq_mul_right {n m k : ℕ} (Hm : m > 0) (H : n * m = k * m) : n = k :=
by apply eq_of_mul_eq_mul_left Hm; rwra [mul.comm m n, mul.comm m k]

@[hott] theorem eq_zero_sum_eq_of_mul_eq_mul_left {n m k : ℕ} (H : n * m = n * k) : n = 0 ⊎ m = k :=
(eq_zero_sum_pos _).functor_right _ (assume Hn : n > 0, eq_of_mul_eq_mul_left Hn H)

@[hott] theorem eq_zero_sum_eq_of_mul_eq_mul_right {n m k : ℕ} (H : n * m = k * m) :
  m = 0 ⊎ n = k :=
by apply eq_zero_sum_eq_of_mul_eq_mul_left; rwra [mul.comm m n, mul.comm m k]

@[hott] theorem eq_one_of_mul_eq_one_right {n m : ℕ} (H : n * m = 1) : n = 1 :=
have H2 : n * m > 0, by rwr H; apply succ_pos,
sum.elim (le_sum_gt n 1)
  (λH3,
    have n > 0, from pos_of_mul_pos_right H2,
    show n = 1, from le.antisymm H3 (succ_le_of_lt this))
  (λH3,
    have m > 0, from pos_of_mul_pos_left H2,
    have n * m ≥ 2 * 1, from nat.mul_le_mul (succ_le_of_lt H3) (succ_le_of_lt this),
    have 1 ≥ 2, by rwra [H, hott.algebra.mul_one] at this,
    absurd (lt_succ_self _) (not_lt_of_ge this))

@[hott] theorem eq_one_of_mul_eq_one_left {n m : ℕ} (H : n * m = 1) : m = 1 :=
by apply eq_one_of_mul_eq_one_right; rwra [mul.comm]

@[hott] theorem eq_one_of_mul_eq_self_left {n m : ℕ} (Hpos : n > 0) (H : m * n = n) : m = 1 :=
eq_of_mul_eq_mul_right Hpos (H ⬝ (one_mul _)⁻¹ᵖ)

@[hott] theorem eq_one_of_mul_eq_self_right {n m : ℕ} (Hpos : m > 0) (H : m * n = m) : n = 1 :=
by apply eq_one_of_mul_eq_self_left Hpos; rwra [mul.comm]

-- @[hott] theorem eq_one_of_dvd_one {n : ℕ} (H : n ∣ 1) : n = 1 :=
-- dvd.elim H
--   (λm, suppose 1 = n * m,
--    eq_one_of_mul_eq_one_right this⁻¹)

/- min and max -/
open decidable

local notation `min` := hott.algebra.min
local notation `max` := hott.algebra.max

@[hott, hsimp] theorem min_zero (a : ℕ) : min a 0 = 0 :=
by rwr [hott.algebra.min_eq_right (zero_le _)]

@[hott, hsimp] theorem zero_min (a : ℕ) : min 0 a = 0 :=
by rwr [min_eq_left (zero_le _)]

@[hott, hsimp] theorem max_zero (a : ℕ) : max a 0 = a :=
by rwr [max_eq_left (zero_le _)]

@[hott, hsimp] theorem zero_max (a : ℕ) : max 0 a = a :=
by rwr [max_eq_right (zero_le _)]

@[hott, hsimp] theorem min_succ_succ (a b : ℕ) : min (succ a) (succ b) = succ (min a b) :=
sum.elim (lt_sum_ge a b)
  (λthis, by rwr [min_eq_left_of_lt this, min_eq_left_of_lt (succ_lt_succ this)])
  (λthis, by rwr [min_eq_right this, min_eq_right (succ_le_succ this)])

@[hott, hsimp] theorem max_succ_succ (a b : ℕ) : max (succ a) (succ b) = succ (max a b) :=
sum.elim (lt_sum_ge a b)
  (λthis, by rwr [max_eq_right_of_lt this, max_eq_right_of_lt (succ_lt_succ this)])
  (λthis, by rwr [max_eq_left this, max_eq_left (succ_le_succ this)])

/- In algebra.ordered_group, these next four are only proved for additive groups, not additive
   semigroups. -/

@[hott] protected theorem min_add_add_left (a b c : ℕ) : min (a + b) (a + c) = a + min b c :=
sum.elim (le_sum_gt b c)
  (λH,
   have a + b ≤ a + c, from add_le_add_left H _,
   by rwr [min_eq_left H, min_eq_left this])
  (λthis,
   have H : c ≤ b,     from le_of_lt this,
   have a + c ≤ a + b, from add_le_add_left H _,
   by rwr [min_eq_right H, min_eq_right this])

@[hott] protected theorem min_add_add_right (a b c : ℕ) : min (a + c) (b + c) = min a b + c :=
by rwr [nat.add_comm a c, nat.add_comm b c, nat.add_comm (min _ _) c]; apply nat.min_add_add_left

@[hott] protected theorem max_add_add_left (a b c : ℕ) : max (a + b) (a + c) = a + max b c :=
sum.elim (le_sum_gt b c)
  (λH, /- b ≤ c -/
   have a + b ≤ a + c, from add_le_add_left H _,
   by rwr [max_eq_right H, max_eq_right this])
  (λthis,
   have H : c ≤ b,         from le_of_lt this,
   have a + c ≤ a + b, from add_le_add_left H _,
   by rwr [max_eq_left H, max_eq_left this])

@[hott] protected theorem max_add_add_right (a b c : ℕ) : max (a + c) (b + c) = max a b + c :=
by rwr [nat.add_comm a c, nat.add_comm b c, nat.add_comm (max _ _) c]; apply nat.max_add_add_left

/- least and greatest -/

section least_prod_greatest
  variable (P : ℕ → Type _)
  variable [decP : Π n, decidable (P n)]
  include decP

  -- returns the least i < n satisfying P, sum n if there is none
  @[hott] def least : ℕ → ℕ
    | 0        := 0
    | (succ n) := if' P (least n) then least n else succ n

  @[hott] theorem least_of_bound {n : ℕ} (H : P n) : P (least P n) :=
    begin
      induction n with m ih,
      dsimp [least],
      apply H,
      dsimp [least],
      cases decidable.em (P (least P m)) with Hlp Hlp,
      rwr [if_pos Hlp],
      apply Hlp,
      rwr [if_neg Hlp],
      apply H
    end

  @[hott] theorem least_le (n : ℕ) : least P n ≤ n:=
    begin
      induction n with m ih, reflexivity,
      dsimp [least],
      cases decidable.em (P (least P m)) with Psm Pnsm,
      rwr [if_pos Psm],
      apply le.trans ih (le_succ _),
      rwr [if_neg Pnsm]
    end

 @[hott] theorem least_of_lt {i n : ℕ} (ltin : i < n) (H : P i) : P (least P n) :=
   begin
     induction n with m ih,
     exact absurd ltin (not_lt_zero _),
     dsimp [least],
     cases decidable.em (P (least P m)) with Psm Pnsm,
     rwr [if_pos Psm],
     apply Psm,
     rwr [if_neg Pnsm],
     cases (lt_sum_eq_of_le (le_of_lt_succ ltin)) with Hlt Heq,
     exact absurd (ih Hlt) Pnsm,
     rwr Heq at H,
     exact absurd (least_of_bound P H) Pnsm
   end

  @[hott] theorem ge_least_of_lt {i n : ℕ} (ltin : i < n) (Hi : P i) : i ≥ least P n :=
    begin
      induction n with m ih,
      exact absurd ltin (not_lt_zero _),
      dsimp [least],
      cases decidable.em (P (least P m)) with Psm Pnsm,
      rwr [if_pos Psm],
      cases (lt_sum_eq_of_le (le_of_lt_succ ltin)) with Hlt Heq,
      apply ih Hlt,
      rwr Heq,
      apply least_le,
      rwr [if_neg Pnsm],
      cases (lt_sum_eq_of_le (le_of_lt_succ ltin)) with Hlt Heq,
      apply absurd (least_of_lt P Hlt Hi) Pnsm,
      rwr Heq at Hi,
      apply absurd (least_of_bound P Hi) Pnsm
    end

  @[hott] theorem least_lt {n i : ℕ} (ltin : i < n) (Hi : P i) : least P n < n :=
    lt_of_le_of_lt (ge_least_of_lt P ltin Hi) ltin

  -- returns the largest i < n satisfying P, sum n if there is none.
  @[hott] def greatest : ℕ → ℕ
  | 0        := 0
  | (succ n) := if' P n then n else greatest n

  @[hott] theorem greatest_of_lt {i n : ℕ} (ltin : i < n) (Hi : P i) : P (greatest P n) :=
  begin
    induction n with m ih,
      {exact absurd ltin (not_lt_zero _)},
      {cases (decidable.em (P m)) with Psm Pnsm,
        {dsimp [greatest], rwr [if_pos Psm]; exact Psm},
        {dsimp [greatest], rwr [if_neg Pnsm],
          have neim : i ≠ m, from assume H : i = m, absurd (H ▸ Hi) Pnsm,
          have ltim : i < m, from lt_of_le_of_ne (le_of_lt_succ ltin) neim,
          apply ih ltim}}
  end

  @[hott] theorem le_greatest_of_lt {i n : ℕ} (ltin : i < n) (Hi : P i) : i ≤ greatest P n :=
  begin
    induction n with m ih,
      {exact absurd ltin (not_lt_zero _)},
      {cases (decidable.em (P m)) with Psm Pnsm,
        {dsimp [greatest], rwr [if_pos Psm], apply le_of_lt_succ ltin},
        {dsimp [greatest], rwr [if_neg Pnsm],
          have neim : i ≠ m, from assume H : i = m, absurd (H ▸ Hi) Pnsm,
          have ltim : i < m, from lt_of_le_of_ne (le_of_lt_succ ltin) neim,
          apply ih ltim}}
  end

end least_prod_greatest

end nat
end hott
