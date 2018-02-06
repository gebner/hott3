/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jeremy Avigad

Weak orders "≤", strict orders "<", and structures that include both.
-/
import .binary
universes u v w
hott_theory
set_option old_structure_cmd true

namespace hott

open algebra

variable {A : Type _}

/- weak orders -/

class has_le (α : Type u) := (le : α → α → Type u)
class has_lt (α : Type u) := (lt : α → α → Type u)

@[reducible] def ge {α : Type u} [has_le α] (a b : α) : Type u := has_le.le b a
@[reducible] def gt {α : Type u} [has_lt α] (a b : α) : Type u := has_lt.lt b a

hott_theory_cmd "local infix [parsing_only] ` <= ` := hott.has_le.le"
hott_theory_cmd "local infix ` ≤ `  := hott.has_le.le"
hott_theory_cmd "local infix ` < ` := hott.has_lt.lt"
hott_theory_cmd "local infix [parsing_only] ` >= ` := hott.ge"
hott_theory_cmd "local infix ` ≥ `  := hott.ge"
hott_theory_cmd "local infix ` > ` := hott.gt"

namespace algebra
@[hott, class] structure weak_order (A : Type _) extends has_le A :=
(le_refl : Πa, le a a)
(le_trans : Πa b c, le a b → le b c → le a c)
(le_antisymm : Πa b, le a b → le b a → a = b)

section
  variable [s : weak_order A]
  include s

  @[hott, refl] def le.rfl {a : A} : a ≤ a := weak_order.le_refl _
  @[hott] def le.refl (a : A) : a ≤ a := weak_order.le_refl _

  @[hott] def le_of_eq {a b : A} (H : a = b) : a ≤ b := transport (λx, a ≤ x) H (le.refl a)
  @[hott] def ge_of_eq {a b : A} (H : a = b) : a ≥ b := le_of_eq H⁻¹

  @[hott, trans] def le.trans {a b c : A} : a ≤ b → b ≤ c → a ≤ c := weak_order.le_trans _ _ _

  @[hott, trans] def le.trans_eq {a b c : A} (H1 : a ≤ b) (H2 : b = c) : a ≤ c :=
  le.trans H1 (le_of_eq H2)

  @[hott, trans] def le.eq_trans {a b c : A} (H1 : a = b) (H2 : b ≤ c) : a ≤ c :=
  le.trans (le_of_eq H1) H2

  @[hott, trans] def ge.trans {a b c : A} (H1 : a ≥ b) (H2: b ≥ c) : a ≥ c := le.trans H2 H1

  @[hott, trans] def ge.trans_eq {a b c : A} (H1 : a ≥ b) (H2 : b = c) : a ≥ c :=
  le.eq_trans H2⁻¹ H1

  @[hott, trans] def ge.eq_trans {a b c : A} (H1 : a = b) (H2 : b ≥ c) : a ≥ c :=
  le.trans_eq H2 H1⁻¹

  @[hott] def le.antisymm {a b : A} : a ≤ b → b ≤ a → a = b := weak_order.le_antisymm _ _

  -- Alternate syntax. (Abbreviations do not migrate well.)
  @[hott] def eq_of_le_of_ge {a b : A} : a ≤ b → b ≤ a → a = b := le.antisymm
end

@[hott, class] structure linear_weak_order (A : Type _) extends weak_order A :=
(le_total : Πa b, le a b ⊎ le b a)

section
  variables [linear_weak_order A]

  @[hott] def le.total (a b : A) : a ≤ b ⊎ b ≤ a := linear_weak_order.le_total _ _

  @[hott] theorem le_of_not_ge {a b : A} (H : ¬ a ≥ b) : a ≤ b := sum.resolve_left (le.total _ _) H

  @[hott] def le_by_cases (a b : A) {P : Type _} (H1 : a ≤ b → P) (H2 : b ≤ a → P) : P :=
  begin
    cases (le.total a b) with H H,
    { exact H1 H},
    { exact H2 H}
  end
end

/- strict orders -/

@[hott, class] structure strict_order (A : Type _) extends has_lt A :=
(lt_irrefl : Πa, ¬ lt a a)
(lt_trans : Πa b c, lt a b → lt b c → lt a c)

section
  variable [s : strict_order A]
  include s

  @[hott] def lt.irrefl (a : A) : ¬ a < a := strict_order.lt_irrefl _
  @[hott] def not_lt_self (a : A) : ¬ a < a := lt.irrefl _   -- alternate syntax

  @[hott] theorem lt_self_iff_empty (a : A) : a < a ↔ empty :=
  iff_empty_intro (lt.irrefl a)

  @[hott, trans] def lt.trans {a b c : A} : a < b → b < c → a < c := strict_order.lt_trans _ _ _

  @[hott, trans] def lt.trans_eq {a b c : A} (H1 : a < b) (H2 : b = c) : a < c :=
  by hinduction H2; exact H1

  @[hott, trans] def lt.eq_trans {a b c : A} (H1 : a = b) (H2 : b < c) : a < c :=
  by hinduction H1; exact H2

  @[hott, trans] def gt.trans {a b c : A} (H1 : a > b) (H2: b > c) : a > c := lt.trans H2 H1

  @[hott, trans] def gt.trans_eq {a b c : A} (H1 : a > b) (H2 : b = c) : a > c :=
  by hinduction H2; exact H1

  @[hott, trans] def gt.eq_trans {a b c : A} (H1 : a = b) (H2 : b > c) : a > c :=
  by hinduction H1; exact H2

  @[hott] def ne_of_lt {a b : A} (lt_ab : a < b) : a ≠ b :=
  assume eq_ab : a = b,
  show empty, from lt.irrefl b (eq_ab ▸ lt_ab)

  @[hott] theorem ne_of_gt {a b : A} (gt_ab : a > b) : a ≠ b :=
  ne.symm (ne_of_lt gt_ab)

  @[hott] theorem lt.asymm {a b : A} (H : a < b) : ¬ b < a :=
  assume H1 : b < a, lt.irrefl _ (lt.trans H H1)

  @[hott] theorem not_lt_of_gt {a b : A} (H : a > b) : ¬ a < b := lt.asymm H    -- alternate syntax
end

/- well-founded orders -/

@[hott, class] structure wf_strict_order (A : Type _) extends strict_order A :=
(wf_rec : ΠP : A → Type _, (Πx, (Πy, lt y x → P y) → P x) → Πx, P x)

@[hott] def wf.rec_on {A : Type _} [s : wf_strict_order A] {P : A → Type _}
    (x : A) (H : Πx, (Πy, wf_strict_order.lt y x → P y) → P x) : P x :=
wf_strict_order.wf_rec P H x

/- structures with a weak and a strict order -/

@[hott, class] structure order_pair (A : Type _) extends weak_order A, has_lt A :=
(le_of_lt : Π a b, lt a b → le a b)
(lt_of_lt_of_le : Π a b c, lt a b → le b c → lt a c)
(lt_of_le_of_lt : Π a b c, le a b → lt b c → lt a c)
(lt_irrefl : Π a, ¬ lt a a)

section
  variable [s : order_pair A]
  variables {a b c : A}
  include s

  @[hott] def le_of_lt : a < b → a ≤ b := order_pair.le_of_lt _ _

  @[hott, trans] def lt_of_lt_of_le : a < b → b ≤ c → a < c := order_pair.lt_of_lt_of_le _ _ _

  @[hott, trans] def lt_of_le_of_lt : a ≤ b → b < c → a < c := order_pair.lt_of_le_of_lt _ _ _

  @[hott] private def lt_irrefl (s' : order_pair A) (a : A) : ¬ a < a := order_pair.lt_irrefl _

  @[hott] private def lt_trans (s' : order_pair A) (a b c: A) (lt_ab : a < b) (lt_bc : b < c) :
    a < c :=
  lt_of_lt_of_le lt_ab (le_of_lt lt_bc)

  @[hott, instance] def order_pair.to_strict_order : strict_order A :=
  { lt_irrefl := lt_irrefl s, lt_trans := lt_trans s, ..s }

  @[hott, trans] def gt_of_gt_of_ge (H1 : a > b) (H2 : b ≥ c) : a > c := lt_of_le_of_lt H2 H1

  @[hott, trans] def gt_of_ge_of_gt (H1 : a ≥ b) (H2 : b > c) : a > c := lt_of_lt_of_le H2 H1

  @[hott] def not_le_of_gt (H : a > b) : ¬ a ≤ b :=
  assume H1 : a ≤ b,
  lt.irrefl _ (lt_of_lt_of_le H H1)

  @[hott] theorem not_lt_of_ge (H : a ≥ b) : ¬ a < b :=
  assume H1 : a < b,
  lt.irrefl _ (lt_of_le_of_lt H H1)
end

@[hott, class] structure strong_order_pair (A : Type _) extends weak_order A, has_lt A :=
(le_iff_lt_sum_eq : Πa b, le a b ↔ lt a b ⊎ a = b)
(lt_irrefl : Π a, ¬ lt a a)

@[hott] def le_iff_lt_sum_eq [s : strong_order_pair A] {a b : A} : a ≤ b ↔ a < b ⊎ a = b :=
strong_order_pair.le_iff_lt_sum_eq _ _

@[hott] def lt_sum_eq_of_le [s : strong_order_pair A] {a b : A} (le_ab : a ≤ b) : a < b ⊎ a = b :=
iff.mp le_iff_lt_sum_eq le_ab

@[hott] def le_of_lt_sum_eq [s : strong_order_pair A] {a b : A} (lt_sum_eq : a < b ⊎ a = b) :
  a ≤ b :=
iff.mpr le_iff_lt_sum_eq lt_sum_eq

@[hott] private def lt_irrefl' [s : strong_order_pair A] (a : A) : ¬ a < a :=
strong_order_pair.lt_irrefl _

@[hott] private def le_of_lt' [s : strong_order_pair A] (a b : A) : a < b → a ≤ b :=
λHlt, le_of_lt_sum_eq (sum.inl Hlt)

@[hott] private def lt_iff_le_prod_ne [s : strong_order_pair A] {a b : A} :
  a < b ↔ (a ≤ b × a ≠ b) :=
iff.intro
  (λHlt, pair (le_of_lt_sum_eq (sum.inl Hlt)) (λHab, absurd (Hab ▸ Hlt) (lt_irrefl' _)))
  (λHand,
   have Hor : a < b ⊎ a = b, from lt_sum_eq_of_le Hand.fst,
   sum.resolve_right Hor Hand.snd)

@[hott] theorem lt_of_le_of_ne [s : strong_order_pair A] {a b : A} : a ≤ b → a ≠ b → a < b :=
λH1 H2, iff.mpr lt_iff_le_prod_ne (pair H1 H2)

@[hott] private def ne_of_lt' [s : strong_order_pair A] {a b : A} (H : a < b) : a ≠ b :=
((iff.mp (@lt_iff_le_prod_ne _ _ _ _)) H).snd

@[hott] private def lt_of_lt_of_le' [s : strong_order_pair A] (a b c : A) : a < b → b ≤ c → a < c :=
assume lt_ab : a < b,
assume le_bc : b ≤ c,
have le_ac : a ≤ c, from le.trans (le_of_lt' _ _ lt_ab) le_bc,
have ne_ac : a ≠ c, from
  assume eq_ac : a = c,
  have le_ba : b ≤ a, from eq_ac⁻¹ ▸ le_bc,
  have eq_ab : a = b, from le.antisymm  (le_of_lt' _ _ lt_ab) le_ba,
  show empty, from ne_of_lt' lt_ab eq_ab,
show a < c, from iff.mpr (lt_iff_le_prod_ne) (pair le_ac ne_ac)

@[hott] def lt_of_le_of_lt' [s : strong_order_pair A] (a b c : A) : a ≤ b → b < c → a < c :=
assume le_ab : a ≤ b,
assume lt_bc : b < c,
have le_ac : a ≤ c, from le.trans le_ab (le_of_lt' _ _ lt_bc),
have ne_ac : a ≠ c, from
  assume eq_ac : a = c,
  have le_cb : c ≤ b, from eq_ac ▸ le_ab,
  have eq_bc : b = c, from le.antisymm  (le_of_lt' _ _ lt_bc) le_cb,
  show empty, from ne_of_lt' lt_bc eq_bc,
show a < c, from iff.mpr (lt_iff_le_prod_ne) (pair le_ac ne_ac)

@[hott, instance] def strong_order_pair.to_order_pair [s : strong_order_pair A] : order_pair A :=
{ lt_irrefl := lt_irrefl',
  le_of_lt := le_of_lt',
  lt_of_le_of_lt := lt_of_le_of_lt',
  lt_of_lt_of_le := lt_of_lt_of_le', ..s }

/- linear orders -/

@[hott, class] structure linear_order_pair (A : Type _) extends order_pair A, linear_weak_order A

@[hott, class] structure linear_strong_order_pair (A : Type _) extends strong_order_pair A,
    linear_weak_order A

@[hott, instance] def linear_strong_order_pair.to_linear_order_pair
    [s : linear_strong_order_pair A] : linear_order_pair A :=
{ ..s, ..strong_order_pair.to_order_pair }

section
  variable [s : linear_strong_order_pair A]
  variables (a b c : A)
  include s

  @[hott] def lt.trichotomy : a < b ⊎ a = b ⊎ b < a :=
  sum.elim (le.total a b)
    (assume H : a ≤ b,
      sum.elim (iff.mp le_iff_lt_sum_eq H) sum.inl (assume H1, sum.inr (sum.inl H1)))
    (assume H : b ≤ a,
      sum.elim (iff.mp le_iff_lt_sum_eq H)
        (assume H1, sum.inr (sum.inr H1))
        (assume H1, sum.inr (sum.inl (H1⁻¹))))

  @[hott] def lt.by_cases {a b : A} {P : Type _}
    (H1 : a < b → P) (H2 : a = b → P) (H3 : b < a → P) : P :=
  sum.elim (lt.trichotomy _ _)
    (assume H, H1 H)
    (assume H, sum.elim H (assume H', H2 H') (assume H', H3 H'))

  @[hott] def lt_ge_by_cases {a b : A} {P : Type _} (H1 : a < b → P) (H2 : a ≥ b → P) : P :=
  lt.by_cases H1 (λH, H2 (le_of_eq H⁻¹)) (λH, H2 (le_of_lt H))

  @[hott] def le_of_not_gt {a b : A} (H : ¬ a > b) : a ≤ b :=
  lt.by_cases (assume H', absurd H' H) (assume H', le_of_eq H'⁻¹) (assume H', le_of_lt H')

  @[hott] theorem lt_of_not_ge {a b : A} (H : ¬ a ≥ b) : a < b :=
  lt.by_cases
    (assume H', absurd begin exact le_of_lt H' end H)
    (assume H', absurd (le_of_eq H') H)
    (assume H', H')

  @[hott] theorem lt_sum_ge : a < b ⊎ a ≥ b :=
  lt.by_cases
    (assume H1 : a < b, sum.inl H1)
    (assume H1 : a = b, sum.inr (le_of_eq H1⁻¹))
    (assume H1 : a > b, sum.inr (le_of_lt H1))

  @[hott] theorem le_sum_gt : a ≤ b ⊎ a > b :=
  sum.swap (lt_sum_ge b a)

  @[hott] theorem lt_sum_gt_of_ne {a b : A} (H : a ≠ b) : a < b ⊎ a > b :=
  lt.by_cases (assume H1, sum.inl H1) (assume H1, absurd H1 H) (assume H1, sum.inr H1)
end

open decidable

@[hott, class] structure decidable_linear_order (A : Type _) extends linear_strong_order_pair A :=
(decidable_lt : decidable_rel lt)

section
  variable [s : decidable_linear_order A]
  variables {a b c d : A}
  include s
  open hott.decidable

  @[hott, instance] def decidable_lt : decidable (a < b) :=
  @decidable_linear_order.decidable_lt _ _ _ _

  @[hott, instance] def decidable_le : decidable (a ≤ b) :=
  by_cases
    (assume H : a < b, inl (le_of_lt H))
    (assume H : ¬ a < b,
      have H1 : b ≤ a, from le_of_not_gt H,
      by_cases
        (assume H2 : b < a, inr (not_le_of_gt H2))
        (assume H2 : ¬ b < a, inl (le_of_not_gt H2)))

  @[hott, instance] def has_decidable_eq : decidable (a = b) :=
  by_cases
    (assume H : a ≤ b,
      by_cases
        (assume H1 : b ≤ a, inl (le.antisymm H H1))
        (assume H1 : ¬ b ≤ a, inr (assume H2 : a = b, H1 (le_of_eq H2⁻¹))))
    (assume H : ¬ a ≤ b,
      (inr (assume H1 : a = b, H (le_of_eq H1))))

  @[hott] theorem eq_sum_lt_of_not_lt {a b : A} (H : ¬ a < b) : a = b ⊎ b < a :=
  if Heq :: a = b then sum.inl Heq else sum.inr (lt_of_not_ge (λ Hge, H (lt_of_le_of_ne Hge Heq)))

  @[hott] theorem eq_sum_lt_of_le {a b : A} (H : a ≤ b) : a = b ⊎ a < b :=
    begin
      hinduction eq_sum_lt_of_not_lt (not_lt_of_ge H) with x1 H' H',
      exact sum.inl H'⁻¹,
      exact sum.inr H'
    end

  @[hott] def lt.cases {B : Type _} (a b : A) (t_lt t_eq t_gt : B) : B :=
  if' a = b then t_eq else (if' a < b then t_lt else t_gt)

  @[hott] theorem lt.cases_of_eq {B : Type _} {a b : A} {t_lt t_eq t_gt : B} (H : a = b) :
  lt.cases a b t_lt t_eq t_gt = t_eq := if_pos H

  @[hott] theorem lt.cases_of_lt {B : Type _} {a b : A} {t_lt t_eq t_gt : B} (H : a < b) :
    lt.cases a b t_lt t_eq t_gt = t_lt :=
  if_neg (ne_of_lt H) ⬝ if_pos H

  @[hott] theorem lt.cases_of_gt {B : Type _} {a b : A} {t_lt t_eq t_gt : B} (H : a > b) :
    lt.cases a b t_lt t_eq t_gt = t_gt :=
  if_neg (ne.symm (ne_of_lt H)) ⬝ if_neg (lt.asymm H)

  @[hott] def min (a b : A) : A := if' a ≤ b then a else b
  @[hott] def max (a b : A) : A := if' a ≤ b then b else a

  /- these show min and max form a lattice -/

  @[hott] theorem min_le_left (a b : A) : min a b ≤ a :=
  hott.decidable.by_cases
    (assume H : a ≤ b, by dsimp [min]; rwr [if_pos H])
    (assume H : ¬ a ≤ b, by dsimp [min]; rwr [if_neg H]; apply le_of_lt (lt_of_not_ge H))

  @[hott] theorem min_le_right (a b : A) : min a b ≤ b :=
  hott.decidable.by_cases
    (assume H : a ≤ b, by dsimp [min]; rwr [if_pos H]; apply H)
    (assume H : ¬ a ≤ b, by dsimp [min]; rwr [if_neg H])

  @[hott] theorem le_min {a b c : A} (H₁ : c ≤ a) (H₂ : c ≤ b) : c ≤ min a b :=
  hott.decidable.by_cases
    (assume H : a ≤ b, by dsimp [min]; rwr [if_pos H]; apply H₁)
    (assume H : ¬ a ≤ b, by dsimp [min]; rwr [if_neg H]; apply H₂)

  @[hott] theorem le_max_left (a b : A) : a ≤ max a b :=
  hott.decidable.by_cases
    (assume H : a ≤ b, by dsimp [max]; rwr [if_pos H]; apply H)
    (assume H : ¬ a ≤ b, by dsimp [max]; rwr [if_neg H])

  @[hott] theorem le_max_right (a b : A) : b ≤ max a b :=
  hott.decidable.by_cases
    (assume H : a ≤ b, by dsimp [max]; rwr [if_pos H])
    (assume H : ¬ a ≤ b, by dsimp [max]; rwr [if_neg H]; apply le_of_lt (lt_of_not_ge H))

  @[hott] theorem max_le {a b c : A} (H₁ : a ≤ c) (H₂ : b ≤ c) : max a b ≤ c :=
  hott.decidable.by_cases
    (assume H : a ≤ b, by dsimp [max]; rwr [if_pos H]; apply H₂)
    (assume H : ¬ a ≤ b, by dsimp [max]; rwr [if_neg H]; apply H₁)

  @[hott] theorem le_max_left_iff_unit (a b : A) : a ≤ max a b ↔ unit :=
  iff_unit_intro (le_max_left a b)

  @[hott] theorem le_max_right_iff_unit (a b : A) : b ≤ max a b ↔ unit :=
  iff_unit_intro (le_max_right a b)

  /- these are also proved for lattices, but with inf and sup in place of min and max -/

  @[hott] theorem eq_min {a b c : A} (H₁ : c ≤ a) (H₂ : c ≤ b) (H₃ : Π{d}, d ≤ a → d ≤ b → d ≤ c) :
    c = min a b :=
  le.antisymm (le_min H₁ H₂) (H₃ (min_le_left _ _) (min_le_right _ _))

  @[hott] theorem min.comm (a b : A) : min a b = min b a :=
  eq_min (min_le_right _ _) (min_le_left _ _) (λ c H₁ H₂, le_min H₂ H₁)

  @[hott] theorem min.assoc (a b c : A) : min (min a b) c = min a (min b c) :=
  begin
    apply eq_min,
    { apply le.trans, apply min_le_left, apply min_le_left },
    { apply le_min, apply le.trans, apply min_le_left, apply min_le_right, apply min_le_right },
    { intros d H₁ H₂, apply le_min, apply le_min H₁, apply le.trans H₂, apply min_le_left,
      apply le.trans H₂, apply min_le_right }
  end

  @[hott] theorem min.left_comm (a b c : A) : min a (min b c) = min b (min a c) :=
  binary.left_comm (@min.comm A s) (@min.assoc A s) a b c

  @[hott] theorem min.right_comm (a b c : A) : min (min a b) c = min (min a c) b :=
  binary.right_comm (@min.comm A s) (@min.assoc A s) a b c

  @[hott] theorem min_self (a : A) : min a a = a :=
  by apply inverse; apply eq_min (le.refl a) le.rfl; intros; assumption

  @[hott] theorem min_eq_left {a b : A} (H : a ≤ b) : min a b = a :=
  by apply inverse; apply eq_min le.rfl H; intros; assumption

  @[hott] theorem min_eq_right {a b : A} (H : b ≤ a) : min a b = b :=
  by rwr min.comm; exact min_eq_left H

  @[hott] theorem eq_max {a b c : A} (H₁ : a ≤ c) (H₂ : b ≤ c) (H₃ : Π{d}, a ≤ d → b ≤ d → c ≤ d) :
    c = max a b :=
  le.antisymm (H₃ (le_max_left _ _) (le_max_right _ _)) (max_le H₁ H₂)

  @[hott] theorem max.comm (a b : A) : max a b = max b a :=
  eq_max (le_max_right _ _) (le_max_left _ _) (λ c H₁ H₂, max_le H₂ H₁)

  @[hott] theorem max.assoc (a b c : A) : max (max a b) c = max a (max b c) :=
  begin
    apply eq_max,
    { apply le.trans, apply le_max_left a b, apply le_max_left },
    { apply max_le, apply le.trans, apply le_max_right a b, apply le_max_left, apply le_max_right },
    { intros d H₁ H₂, apply max_le, apply max_le H₁, apply le.trans (le_max_left _ _) H₂,
      apply le.trans (le_max_right _ _) H₂}
  end

  @[hott] theorem max.left_comm (a b c : A) : max a (max b c) = max b (max a c) :=
  binary.left_comm (@max.comm A s) (@max.assoc A s) a b c

  @[hott] theorem max.right_comm (a b c : A) : max (max a b) c = max (max a c) b :=
  binary.right_comm (@max.comm A s) (@max.assoc A s) a b c

  @[hott] theorem max_self (a : A) : max a a = a :=
  by apply inverse; apply eq_max (le.refl a) le.rfl; intros; assumption

  @[hott] theorem max_eq_left {a b : A} (H : b ≤ a) : max a b = a :=
  by apply inverse; apply eq_max le.rfl H; intros; assumption

  @[hott] theorem max_eq_right {a b : A} (H : a ≤ b) : max a b = b :=
  by rwr max.comm; exact max_eq_left H

  /- these rely on lt_of_lt -/

  @[hott] theorem min_eq_left_of_lt {a b : A} (H : a < b) : min a b = a :=
  min_eq_left (le_of_lt H)

  @[hott] theorem min_eq_right_of_lt {a b : A} (H : b < a) : min a b = b :=
  min_eq_right (le_of_lt H)

  @[hott] theorem max_eq_left_of_lt {a b : A} (H : b < a) : max a b = a :=
  max_eq_left (le_of_lt H)

  @[hott] theorem max_eq_right_of_lt {a b : A} (H : a < b) : max a b = b :=
  max_eq_right (le_of_lt H)

  /- these use the fact that it is a linear ordering -/

  @[hott] theorem lt_min {a b c : A} (H₁ : a < b) (H₂ : a < c) : a < min b c :=
  sum.elim (le_sum_gt _ _)
    (assume H : b ≤ c, by rwr (min_eq_left H); apply H₁)
    (assume H : b > c, by rwr (min_eq_right_of_lt H); apply H₂)

  @[hott] theorem max_lt {a b c : A} (H₁ : a < c) (H₂ : b < c) : max a b < c :=
  sum.elim (le_sum_gt _ _)
    (assume H : a ≤ b, by rwr (max_eq_right H); apply H₂)
    (assume H : a > b, by rwr (max_eq_left_of_lt H); apply H₁)
end
end algebra
end hott
