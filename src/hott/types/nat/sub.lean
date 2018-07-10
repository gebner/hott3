/-
Copyright (c) 2014 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Floris van Doorn, Jeremy Avigad
Subtraction on the natural numbers, as well as min, max, and distance.
-/
import .order
universes u v w
hott_theory
namespace hott
open hott.algebra nat hott.nat

namespace nat

/- subtraction -/

@[hott] protected theorem sub_zero (n : ℕ) : n - 0 = n :=
rfl

@[hott] theorem sub_succ (n m : ℕ) : n - succ m = pred (n - m) :=
rfl

@[hott] protected theorem zero_sub (n : ℕ) : 0 - n = 0 :=
nat.rec_on n (nat.sub_zero _)
  (λk : nat,
    assume IH : 0 - k = 0,
    calc
      0 - succ k = pred (0 - k) : by rwr sub_succ
             ... = pred 0       : by rwr IH
             ... = 0            : pred_zero)

@[hott] theorem succ_sub_succ (n m : ℕ) : succ n - succ m = n - m :=
succ_sub_succ_eq_sub n m

@[hott] protected theorem sub_self (n : ℕ) : n - n = 0 :=
nat.rec_on n (nat.sub_zero _) (λk IH, succ_sub_succ _ _ ⬝ IH)

@[hott] protected theorem add_sub_add_right (n k m : ℕ) : (n + k) - (m + k) = n - m :=
nat.rec_on k
  (calc
    (n + 0) - (m + 0) = n - (m + 0) : by rwr [hott.algebra.add_zero]
                  ... = n - m       : by rwr [hott.algebra.add_zero])
  (λl : nat,
    assume IH : (n + l) - (m + l) = n - m,
    calc
      (n + succ l) - (m + succ l) = succ (n + l) - (m + succ l) : by rwr add_succ
                              ... = succ (n + l) - succ (m + l) : by rwr add_succ
                              ... = (n + l) - (m + l)           : by rwr succ_sub_succ
                              ... =  n - m                      : IH)
@[hott] protected theorem add_sub_add_left (k n m : ℕ) : (k + n) - (k + m) = n - m :=
by rwr [nat.add_comm k n, nat.add_comm k m]; exact nat.add_sub_add_right n k m

@[hott] protected theorem add_sub_cancel (n m : ℕ) : n + m - m = n :=
nat.rec_on m
  (begin rwr hott.algebra.add_zero end)
  (λk : ℕ,
    assume IH : n + k - k = n,
    calc
      n + succ k - succ k = succ (n + k) - succ k : by rwr add_succ
                      ... = n + k - k             : by rwr succ_sub_succ
                      ... = n                     : IH)

@[hott] protected theorem add_sub_cancel_left (n m : ℕ) : n + m - n = m :=
by rwr add.comm; apply nat.add_sub_cancel

@[hott] protected theorem sub_sub (n m k : ℕ) : n - m - k = n - (m + k) :=
nat.rec_on k
  (calc
    n - m - 0 = n - m        : by rwr nat.sub_zero
          ... = n - (m + 0)  : by rwr nat.add_zero)
  (λl : nat,
    assume IH : n - m - l = n - (m + l),
    calc
      n - m - succ l = pred (n - m - l)   : by rwr sub_succ
                 ... = pred (n - (m + l)) : by rwr IH
                 ... = n - succ (m + l)   : by rwr sub_succ
                 ... = n - (m + succ l)   : by rwr add_succ)

@[hott] theorem succ_sub_sub_succ (n m k : ℕ) : succ n - m - succ k = n - m - k :=
calc
  succ n - m - succ k = succ n - (m + succ k) : by rwr nat.sub_sub
                  ... = succ n - succ (m + k) : by rwr add_succ
                  ... = n - (m + k)           : by rwr succ_sub_succ
                  ... = n - m - k             : by rwr nat.sub_sub

@[hott] theorem sub_self_add (n m : ℕ) : n - (n + m) = 0 :=
calc
  n - (n + m) = n - n - m : by rwr nat.sub_sub
          ... = 0 - m     : by rwr nat.sub_self
          ... = 0         : by rwr nat.zero_sub

@[hott] protected theorem sub.right_comm (m n k : ℕ) : m - n - k = m - k - n :=
calc
  m - n - k = m - (n + k) : by rwr nat.sub_sub
        ... = m - (k + n) : by rwr add.comm
        ... = m - k - n   : by rwr nat.sub_sub

@[hott] theorem succ_sub_one (n : ℕ) : succ n - 1 = n :=
rfl

/- interaction with multiplication -/

@[hott] theorem mul_pred_left (n m : ℕ) : pred n * m = n * m - m :=
nat.rec_on n
  (calc
    pred 0 * m = 0 * m     : by rwr pred_zero
           ... = 0         : by rwr nat.zero_mul
           ... = 0 - m     : by rwr nat.zero_sub
           ... = 0 * m - m : by rwr nat.zero_mul)
  (λk : nat,
    assume IH : pred k * m = k * m - m,
    calc
      pred (succ k) * m = k * m          : by rwr pred_succ
                    ... = k * m + m - m  : by rwr nat.add_sub_cancel
                    ... = succ k * m - m : by rwr succ_mul)

@[hott] theorem mul_pred_right (n m : ℕ) : n * pred m = n * m - n :=
calc
  n * pred m = pred m * n : by rwr mul.comm
         ... = m * n - n  : by rwr mul_pred_left
         ... = n * m - n  : by rwr mul.comm

@[hott] protected theorem mul_sub_right_distrib (n m k : ℕ) : (n - m) * k = n * k - m * k :=
nat.rec_on m
  (calc
    (n - 0) * k = n * k         : by rwr nat.sub_zero
            ... = n * k - 0     : by rwr nat.sub_zero
            ... = n * k - 0 * k : by rwr nat.zero_mul)
  (λl : nat,
    assume IH : (n - l) * k = n * k - l * k,
    calc
      (n - succ l) * k = pred (n - l) * k     : by rwr sub_succ
                   ... = (n - l) * k - k      : by rwr mul_pred_left
                   ... = n * k - l * k - k    : by rwr IH
                   ... = n * k - (l * k + k)  : by rwr nat.sub_sub
                   ... = n * k - (succ l * k) : by rwr succ_mul)

@[hott] protected theorem mul_sub_left_distrib (n m k : ℕ) : n * (m - k) = n * m - n * k :=
calc
  n * (m - k) = (m - k) * n   : by rwr mul.comm
          ... = m * n - k * n : by rwr nat.mul_sub_right_distrib
          ... = n * m - k * n : by rwr mul.comm
          ... = n * m - n * k : by rwr mul.comm k n

@[hott] protected theorem mul_self_sub_mul_self_eq (a b : nat) : a * a - b * b = (a + b) * (a - b) :=
begin
  rwr [nat.mul_sub_left_distrib, nat.right_distrib, nat.right_distrib, mul.comm b a],
  rwr [nat.add_comm (a*a) (a*b)],
  rwr nat.add_sub_add_left
end

@[hott] theorem succ_mul_succ_eq (a : nat) : succ a * succ a = a*a + a + a + 1 :=
calc succ a * succ a
    = (a+1)*(a+1)     : by rwr [add_one]
... = a*a + a + a + 1 : by rwr [nat.right_distrib, nat.left_distrib, nat.one_mul, nat.mul_one]

/- interaction with inequalities -/

-- @[hott] theorem succ_sub {m n : ℕ} : m ≥ n → succ m - n  = succ (m - n) :=
-- sub_induction n m
--   (λk, assume H : 0 ≤ k, rfl)
--    (λk,
--     assume H : succ k ≤ 0,
--     absurd H (not_succ_le_zero _))
--   (λk l,
--     assume IH : k ≤ l → succ l - k = succ (l - k),
--     λH : succ k ≤ succ l,
--     calc
--       succ (succ l) - succ k = succ l - k             : by rwr succ_sub_succ
--                          ... = succ (l - k)           : IH (le_of_succ_le_succ H)
--                          ... = succ (succ l - succ k) : by rwr succ_sub_succ)

-- @[hott] theorem sub_eq_zero_of_le {n m : ℕ} (H : n ≤ m) : n - m = 0 :=
-- begin hinduction le.elim H with p k Hk, rwr Hk, apply sub_self_add end

-- @[hott] theorem add_sub_of_le {n m : ℕ} : n ≤ m → n + (m - n) = m :=
-- sub_induction n m
--   (λk,
--     assume H : 0 ≤ k,
--     calc
--       0 + (k - 0) = k - 0 : by rwr nat.zero_add
--               ... = k     : by rwr nat.sub_zero)
--   (λk, assume H : succ k ≤ 0, absurd H (not_succ_le_zero _))
--   (λk l,
--     assume IH : k ≤ l → k + (l - k) = l,
--     λH : succ k ≤ succ l,
--     calc
--       succ k + (succ l - succ k) = succ k + (l - k)   : by rwr succ_sub_succ
--                              ... = succ (k + (l - k)) : by rwr succ_add
--                              ... = succ l             : IH (le_of_succ_le_succ H))

-- @[hott] theorem add_sub_of_ge {n m : ℕ} (H : n ≥ m) : n + (m - n) = n :=
-- calc
--   n + (m - n) = n + 0 : by rwr sub_eq_zero_of_le H
--           ... = n     : by rwr nat.add_zero

-- @[hott] protected theorem sub_add_cancel {n m : ℕ} : n ≥ m → n - m + m = n :=
-- by rwr add.comm; apply add_sub_of_le

-- @[hott] theorem sub_add_of_le {n m : ℕ} : n ≤ m → n - m + m = m :=
-- by rwr add.comm; apply add_sub_of_ge

-- @[hott, elab_as_eliminator] theorem sub.cases {P : ℕ → Type _} {n m : ℕ} (H1 : n ≤ m → P 0)
--   (H2 : Πk, m + k = n -> P k) : P (n - m) :=
-- sum.elim (le.total n m)
--   (assume H3 : n ≤ m, by rwr sub_eq_zero_of_le H3; exact H1 H3)
--   (assume H3 : m ≤ n, H2 (n - m) (add_sub_of_le H3))

-- @[hott] theorem exists_sub_eq_of_le {n m : ℕ} (H : n ≤ m) : Σk, m - k = n :=
-- obtain (k : ℕ) (Hk : n + k = m), from le.elim H,
-- sigma.mk k
--   (calc
--     m - k = n + k - k : by rwr Hk
--       ... = n         : by rwr nat.add_sub_cancel)

-- @[hott] protected theorem add_sub_assoc {m k : ℕ} (H : k ≤ m) (n : ℕ) : n + m - k = n + (m - k) :=
-- have l1 : k ≤ m → n + m - k = n + (m - k), from
--   sub_induction k m
--     (λm : ℕ,
--       assume H : 0 ≤ m,
--       calc
--         n + m - 0 = n + m       : by rwr nat.sub_zero
--               ... = n + (m - 0) : by rwr nat.sub_zero)
--     (λk : ℕ, assume H : succ k ≤ 0, absurd H (not_succ_le_zero _))
--     (λk m,
--       assume IH : k ≤ m → n + m - k = n + (m - k),
--       λH : succ k ≤ succ m,
--       calc
--         n + succ m - succ k = succ (n + m) - succ k : by rwr add_succ
--                         ... = n + m - k             : by rwr succ_sub_succ
--                         ... = n + (m - k)           : IH (le_of_succ_le_succ H)
--                         ... = n + (succ m - succ k) : by rwr succ_sub_succ),
-- l1 H

-- @[hott] theorem le_of_sub_eq_zero {n m : ℕ} : n - m = 0 → n ≤ m :=
-- sub.cases
--   (assume H1 : n ≤ m, assume H2 : 0 = 0, H1)
--   (λk : ℕ,
--     assume H1 : m + k = n,
--     assume H2 : k = 0,
--     have H3 : n = m, from by rwr [←add_zero, ←H2]; exact H1⁻¹,
--     le_of_eq _)

-- @[hott] theorem sub_sub.cases {P : ℕ → ℕ → Type _} {n m : ℕ} (H1 : Πk, n = m + k -> P k 0)
--   (H2 : Πk, m = n + k → P 0 k) : P (n - m) (m - n) :=
-- sum.elim (le.total n m)
--   (assume H3 : n ≤ m,
--     (sub_eq_zero_of_le H3)⁻¹ ▸ (H2 (m - n) (add_sub_of_le H3)⁻¹))
--   (assume H3 : m ≤ n,
--     (sub_eq_zero_of_le H3)⁻¹ ▸ (H1 (n - m) (add_sub_of_le H3)⁻¹))

-- @[hott] protected theorem sub_eq_of_add_eq {n m k : ℕ} (H : n + m = k) : k - n = m :=
-- have H2 : k - n + n = m + n, from
--   calc
--     k - n + n = k     : nat.sub_add_cancel (le.intro H)
--           ... = n + m : H⁻¹
--           ... = m + n : by rwr add.comm,
-- add.right_cancel H2

-- @[hott] protected theorem eq_sub_of_add_eq {a b c : ℕ} (H : a + c = b) : a = b - c :=
-- by symmetry; apply nat.sub_eq_of_add_eq; rwra add.comm

-- @[hott] protected theorem sub_eq_of_eq_add {a b c : ℕ} (H : a = c + b) : a - b = c :=
-- by apply nat.sub_eq_of_add_eq; rwr add.comm; symmetry; exact H

-- @[hott] protected theorem sub_le_sub_right {n m : ℕ} (H : n ≤ m) (k : ℕ) : n - k ≤ m - k :=
-- obtain (l : ℕ) (Hl : n + l = m), from le.elim H,
-- sum.elim !le.total
--   (assume H2 : n ≤ k, (sub_eq_zero_of_le H2)⁻¹ ▸ !zero_le)
--   (assume H2 : k ≤ n,
--     have H3 : n - k + l = m - k, from
--       calc
--         n - k + l = l + (n - k) : add.comm
--               ... = l + n - k   : nat.add_sub_assoc H2 l
--               ... = n + l - k   : add.comm
--               ... = m - k       : by xrwr Hl,
--     le.intro H3)

-- @[hott] protected theorem sub_le_sub_left {n m : ℕ} (H : n ≤ m) (k : ℕ) : k - m ≤ k - n :=
-- by induction H; [refl, exact le.trans (pred_le _) H_ih]

-- @[hott] protected theorem sub_pos_of_lt {m n : ℕ} (H : m < n) : n - m > 0 :=
-- have H1 : n = n - m + m, from (nat.sub_add_cancel (le_of_lt H))⁻¹,
-- have   H2 : 0 + m < n - m + m, begin rwr [zero_add, -H1], exact H end,
-- !lt_of_add_lt_add_right H2

-- @[hott] protected theorem lt_of_sub_pos {m n : ℕ} (H : n - m > 0) : m < n :=
-- lt_of_not_ge
--   (λH1 : m ≥ n,
--     have H2 : n - m = 0, from sub_eq_zero_of_le H1,
--     !lt.irrefl (H2 ▸ H))

-- @[hott] protected theorem lt_of_sub_lt_sub_right {n m k : ℕ} (H : n - k < m - k) : n < m :=
-- lt_of_not_ge
--   (assume H1 : m ≤ n,
--     have H2 : m - k ≤ n - k, from nat.sub_le_sub_right H1 _,
--     not_le_of_gt H H2)

-- @[hott] protected theorem lt_of_sub_lt_sub_left {n m k : ℕ} (H : n - m < n - k) : k < m :=
-- lt_of_not_ge
--   (assume H1 : m ≤ k,
--     have H2 : n - k ≤ n - m, from nat.sub_le_sub_left H1 _,
--     not_le_of_gt H H2)

-- @[hott] protected theorem sub_lt_sub_add_sub (n m k : ℕ) : n - k ≤ (n - m) + (m - k) :=
-- sub.cases
--   (assume H : n ≤ m, (zero_add (m - k))⁻¹ ▸ nat.sub_le_sub_right H k)
--   (λmn : ℕ,
--     assume Hmn : m + mn = n,
--     sub.cases
--       (assume H : m ≤ k,
--         have   H2 : n - k ≤ n - m, from nat.sub_le_sub_left H n,
--         have H3 : n - k ≤ mn, from nat.sub_eq_of_add_eq Hmn ▸ H2,
--         show   n - k ≤ mn + 0,  begin rwr add_zero, assumption end)
--       (λkm : ℕ,
--         assume Hkm : k + km = m,
--         have H : k + (mn + km) = n, from
--           calc
--             k + (mn + km) = k + (km + mn): add.comm
--                       ... = k + km + mn  : add.assoc
--                       ... = m + mn       : Hkm
--                       ... = n            : Hmn,
--         have H2 : n - k = mn + km, from nat.sub_eq_of_add_eq H,
--         H2 ▸ !le.refl))

-- @[hott] protected theorem sub_lt_self {m n : ℕ} (H1 : m > 0) (H2 : n > 0) : m - n < m :=
-- calc
--   m - n = succ (pred m) - n             : succ_pred_of_pos H1
--     ... = succ (pred m) - succ (pred n) : succ_pred_of_pos H2
--     ... = pred m - pred n               : succ_sub_succ
--     ... ≤ pred m                        : sub_le
--     ... < succ (pred m)                 : lt_succ_self
--     ... = m                             : succ_pred_of_pos H1

-- @[hott] protected theorem le_sub_of_add_le {m n k : ℕ} (H : m + k ≤ n) : m ≤ n - k :=
-- calc
--   m = m + k - k : nat.add_sub_cancel
--     ... ≤ n - k : nat.sub_le_sub_right H k

-- @[hott] protected theorem lt_sub_of_add_lt {m n k : ℕ} (H : m + k < n) (H2 : k ≤ n) : m < n - k :=
-- lt_of_succ_le (nat.le_sub_of_add_le (calc
--     succ m + k = succ (m + k) : succ_add_eq_succ_add
--            ... ≤ n            : succ_le_of_lt H))

-- @[hott] protected theorem sub_lt_of_lt_add {v n m : nat} (h₁ : v < n + m) (h₂ : n ≤ v) : v - n < m :=
-- have succ v ≤ n + m,   from succ_le_of_lt h₁,
-- have succ (v - n) ≤ m, from
--   calc succ (v - n) = succ v - n : succ_sub h₂
--         ...     ≤ n + m - n      : nat.sub_le_sub_right this n
--         ...     = m              : nat.add_sub_cancel_left,
-- lt_of_succ_le this

-- /- distance -/

-- @[hott] def dist [reducible] (n m : ℕ) := (n - m) + (m - n)

-- @[hott] theorem dist.comm (n m : ℕ) : dist n m = dist m n :=
-- !add.comm

-- @[hott] theorem dist_self (n : ℕ) : dist n n = 0 :=
-- calc
--   (n - n) + (n - n) = 0 + (n - n) : nat.sub_self
--                 ... = 0 + 0       : nat.sub_self
--                 ... = 0           : rfl

-- @[hott] theorem eq_of_dist_eq_zero {n m : ℕ} (H : dist n m = 0) : n = m :=
-- have H2 : n - m = 0, from eq_zero_of_add_eq_zero_right H,
-- have H3 : n ≤ m, from le_of_sub_eq_zero H2,
-- have H4 : m - n = 0, from eq_zero_of_add_eq_zero_left H,
-- have H5 : m ≤ n, from le_of_sub_eq_zero H4,
-- le.antisymm H3 H5

-- @[hott] theorem dist_eq_zero {n m : ℕ} (H : n = m) : dist n m = 0 :=
-- by substvars; rwr [↑dist, *nat.sub_self, add_zero]

-- @[hott] theorem dist_eq_sub_of_le {n m : ℕ} (H : n ≤ m) : dist n m = m - n :=
-- calc
--   dist n m = 0 + (m - n) : {sub_eq_zero_of_le H}
--        ... = m - n       : zero_add

-- @[hott] theorem dist_eq_sub_of_lt {n m : ℕ} (H : n < m) : dist n m = m - n :=
-- dist_eq_sub_of_le (le_of_lt H)

-- @[hott] theorem dist_eq_sub_of_ge {n m : ℕ} (H : n ≥ m) : dist n m = n - m :=
-- !dist.comm ▸ dist_eq_sub_of_le H

-- @[hott] theorem dist_eq_sub_of_gt {n m : ℕ} (H : n > m) : dist n m = n - m :=
-- dist_eq_sub_of_ge (le_of_lt H)

-- @[hott] theorem dist_zero_right (n : ℕ) : dist n 0 = n :=
-- dist_eq_sub_of_ge !zero_le ⬝ !nat.sub_zero

-- @[hott] theorem dist_zero_left (n : ℕ) : dist 0 n = n :=
-- dist_eq_sub_of_le !zero_le ⬝ !nat.sub_zero

-- @[hott] theorem dist.intro {n m k : ℕ} (H : n + m = k) : dist k n = m :=
-- calc
--   dist k n = k - n : dist_eq_sub_of_ge (le.intro H)
--            ... = m : nat.sub_eq_of_add_eq H

-- @[hott] theorem dist_add_add_right (n k m : ℕ) : dist (n + k) (m + k) = dist n m :=
-- calc
--   dist (n + k) (m + k) = ((n+k) - (m+k)) + ((m+k)-(n+k)) : rfl
--                    ... = (n - m) + ((m + k) - (n + k))   : nat.add_sub_add_right
--                    ... = (n - m) + (m - n)               : nat.add_sub_add_right

-- @[hott] theorem dist_add_add_left (k n m : ℕ) : dist (k + n) (k + m) = dist n m :=
-- begin rwr [add.comm k n, add.comm k m]; apply dist_add_add_right end

-- @[hott] theorem dist_add_eq_of_ge {n m : ℕ} (H : n ≥ m) : dist n m + m = n :=
-- calc
--   dist n m + m = n - m + m : {dist_eq_sub_of_ge H}
--            ... = n         : nat.sub_add_cancel H

-- @[hott] theorem dist_eq_intro {n m k l : ℕ} (H : n + m = k + l) : dist n k = dist l m :=
-- calc
--   dist n k = dist (n + m) (k + m) : dist_add_add_right
--        ... = dist (k + l) (k + m) : H
--        ... = dist l m             : dist_add_add_left

-- @[hott] theorem dist_sub_eq_dist_add_left {n m : ℕ} (H : n ≥ m) (k : ℕ) :
--   dist (n - m) k = dist n (k + m) :=
-- have H2 : n - m + (k + m) = k + n, from
--   calc
--     n - m + (k + m) = n - m + (m + k) : add.comm
--                 ... = n - m + m + k   : add.assoc
--                 ... = n + k           : nat.sub_add_cancel H
--                 ... = k + n           : add.comm,
-- dist_eq_intro H2

-- @[hott] theorem dist_sub_eq_dist_add_right {k m : ℕ} (H : k ≥ m) (n : ℕ) :
--   dist n (k - m) = dist (n + m) k :=
-- dist.comm (k - m) n ▸ dist.comm k (n + m) ▸ dist_sub_eq_dist_add_left H n

-- @[hott] theorem dist.triangle_inequality (n m k : ℕ) : dist n k ≤ dist n m + dist m k :=
-- have (n - m) + (m - k) + ((k - m) + (m - n)) = (n - m) + (m - n) + ((m - k) + (k - m)),
-- begin rwr [add.comm (k - m) (m - n),
--                {n - m + _ + _}add.assoc,
--                {m - k + _}add.left_comm, -add.assoc] end,
-- this ▸ add_le_add !nat.sub_lt_sub_add_sub !nat.sub_lt_sub_add_sub

-- @[hott] theorem dist_add_add_le_add_dist_dist (n m k l : ℕ) : dist (n + m) (k + l) ≤ dist n k + dist m l :=
-- have H : dist (n + m) (k + m) + dist (k + m) (k + l) = dist n k + dist m l,
--   by rwr [dist_add_add_left, dist_add_add_right],
-- by rwr -H; apply dist.triangle_inequality

-- @[hott] theorem dist_mul_right (n k m : ℕ) : dist (n * k) (m * k) = dist n m * k :=
-- have Π n m, dist n m = n - m + (m - n), from λn m, rfl,
-- by rwr [this, this n m, right_distrib, *nat.mul_sub_right_distrib]

-- @[hott] theorem dist_mul_left (k n m : ℕ) : dist (k * n) (k * m) = k * dist n m :=
-- begin rwr [mul.comm k n, mul.comm k m, dist_mul_right, mul.comm] end

-- @[hott] theorem dist_mul_dist (n m k l : ℕ) : dist n m * dist k l = dist (n * k + m * l) (n * l + m * k) :=
-- have aux : Πk l, k ≥ l → dist n m * dist k l = dist (n * k + m * l) (n * l + m * k), from
--   λk l : ℕ,
--   assume H : k ≥ l,
--   have H2 : m * k ≥ m * l, from !mul_le_mul_left H,
--   have H3 : n * l + m * k ≥ m * l, from le.trans H2 !le_add_left,
--   calc
--     dist n m * dist k l = dist n m * (k - l)       : dist_eq_sub_of_ge H
--       ... = dist (n * (k - l)) (m * (k - l))       : dist_mul_right
--       ... = dist (n * k - n * l) (m * k - m * l)   : by rwr [*nat.mul_sub_left_distrib]
--       ... = dist (n * k) (m * k - m * l + n * l)   : dist_sub_eq_dist_add_left (!mul_le_mul_left H)
--       ... = dist (n * k) (n * l + (m * k - m * l)) : add.comm
--       ... = dist (n * k) (n * l + m * k - m * l)   : nat.add_sub_assoc H2 (n * l)
--       ... = dist (n * k + m * l) (n * l + m * k)   : dist_sub_eq_dist_add_right H3 _,
-- sum.elim !le.total
--   (assume H : k ≤ l, !dist.comm ▸ !dist.comm ▸ aux l k H)
--   (assume H : l ≤ k, aux k l H)

-- @[hott] lemma dist_eq_max_sub_min {i j : nat} : dist i j = (max i j) - min i j :=
-- sum.elim (lt_sum_ge i j)
--   (suppose i < j,
--     by rwr [max_eq_right_of_lt this, min_eq_left_of_lt this, dist_eq_sub_of_lt this])
--   (suppose i ≥ j,
--     by rwr [max_eq_left this , min_eq_right this, dist_eq_sub_of_ge this])

-- @[hott] lemma dist_succ {i j : nat} : dist (succ i) (succ j) = dist i j :=
-- by rwr [↑dist, *succ_sub_succ]

-- @[hott] lemma dist_le_max {i j : nat} : dist i j ≤ max i j :=
-- begin rwr dist_eq_max_sub_min, apply sub_le end

-- @[hott] lemma dist_pos_of_ne {i j : nat} : i ≠ j → dist i j > 0 :=
-- assume Pne, lt.by_cases
--   (suppose i < j, begin rwr [dist_eq_sub_of_lt this], apply nat.sub_pos_of_lt this end)
--   (suppose i = j, by contradiction)
--   (suppose i > j, begin rwr [dist_eq_sub_of_gt this], apply nat.sub_pos_of_lt this end)

end nat
end hott
