/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Floris van Doorn
-/
import .path .meta.rewrite

universes u v w
hott_theory

/- prod -/

@[reducible] def pair := @prod.mk

@[hott] protected def prod.elim {a b c} (H₁ : a × b) (H₂ : a → b → c) : c :=
prod.rec H₂ H₁

@[hott] def prod.flip {α : Type u} {β : Type v} : α × β → β × α
| ⟨a,b⟩ := ⟨b,a⟩

@[hott] def prod.swap {α : Type u} {β : Type v} : α × β → β × α
| ⟨a,b⟩ := ⟨b,a⟩

@[hott, elab_as_eliminator] def prod.destruct {α : Type u} {β : Type v} {C} :=
@prod.cases_on α β C

/- sum -/

infixr ` ⊎ `:30 := sum

@[hott] protected def sum.elim {a b c} (H₁ : a ⊎ b) (H₂ : a → c) (H₃ : b → c) : c :=
sum.rec H₂ H₃ H₁

@[hott] def sum.swap {a b} : a ⊎ b → b ⊎ a
| (sum.inl ha) := sum.inr ha
| (sum.inr hb) := sum.inl hb

@[hott] def sum.functor {A A' B B'} (f : A → A') (g : B → B') : A ⊎ B → A' ⊎ B'
| (sum.inl a) := sum.inl (f a)
| (sum.inr b) := sum.inr (g b)

@[hott] def sum.functor_right (A) {B B'} (g : B → B') : A ⊎ B → A ⊎ B' :=
sum.functor id g

@[hott] def sum.functor_left {A A'} (B) (f : A → A') : A ⊎ B → A' ⊎ B :=
sum.functor f id

namespace hott
open unit

/- not -/

@[hott] def not (a : Type _) := a → empty
hott_theory_cmd "local prefix ¬ := hott.not"

@[hott] def absurd {a b : Type _} (H₁ : a) (H₂ : ¬a) : b :=
empty.rec (λ e, b) (H₂ H₁)

@[hott] def mt {a b : Type _} (H₁ : a → b) (H₂ : ¬b) : ¬a :=
assume Ha : a, absurd (H₁ Ha) H₂

@[hott] def not_empty : ¬empty :=
assume H : empty, H

@[hott] def non_contradictory (a : Type _) : Type _ := ¬¬a

@[hott] def non_contradictory_intro {a : Type _} (Ha : a) : ¬¬a :=
assume Hna : ¬a, absurd Ha Hna

@[hott] def not.intro {a : Type _} (H : a → empty) : ¬a := H

/- empty -/

@[hott] def empty.elim {c : Type _} (H : empty) : c :=
empty.rec _ H

@[hott, reducible] def ne {A : Type _} (a b : A) := ¬(a = b)
hott_theory_cmd "local notation a ≠ b := hott.ne a b"

namespace ne
  variable {A : Type _}
  variables {a b : A}

  @[hott] def intro (H : a = b → empty) : a ≠ b := H

  @[hott] def elim (H : a ≠ b) : a = b → empty := H

  @[hott] def irrefl (H : a ≠ a) : empty := H rfl

  @[hott] def symm (H : a ≠ b) : b ≠ a :=
  assume (H₁ : b = a), H (H₁⁻¹)
end ne

@[hott] def empty_of_ne {A : Type _} {a : A} : a ≠ a → empty := ne.irrefl

section
  variables {p : Type}

  @[hott] def ne_empty_of_self : p → p ≠ empty :=
  assume (Hp : p) (Heq : p = empty), Heq ▸ Hp

  @[hott] def ne_unit_of_not : ¬p → p ≠ unit :=
  assume (Hnp : ¬p) (Heq : p = unit), (Heq ▸ Hnp) star

  @[hott] def unit_ne_empty : ¬unit = empty :=
  ne_empty_of_self star
end

@[hott] def hott.non_contradictory_em (a : Type _) : ¬¬(a ⊎ ¬a) :=
assume not_em : ¬(a ⊎ ¬a),
  have neg_a : ¬a, from
    assume pos_a : a, absurd (sum.inl pos_a) not_em,
  absurd (sum.inr neg_a) not_em

variables {a : Type _} {b : Type _} {c : Type _} {d : Type _}

/- iff -/

@[hott] def iff (a b : Type _) := (a → b) × (b → a)

hott_theory_cmd "local notation a <-> b := hott.iff a b"
hott_theory_cmd "local notation a ↔ b := hott.iff a b"

@[hott, intro!] def iff.intro : (a → b) → (b → a) → (a ↔ b) := prod.mk

@[hott] def iff.elim : ((a → b) → (b → a) → c) → (a ↔ b) → c :=
λ H₁ H₂, prod.rec H₁ H₂

@[hott] def iff.elim_left : (a ↔ b) → a → b := prod.fst

@[hott] def iff.mp := @iff.elim_left

@[hott] def iff.elim_right : (a ↔ b) → b → a := prod.snd

@[hott] def iff.mpr := @iff.elim_right

@[hott, refl] def iff.refl (a : Type _) : a ↔ a :=
iff.intro (assume H, H) (assume H, H)

@[hott] def iff.rfl {a : Type _} : a ↔ a :=
iff.refl a

@[hott] def iff.of_eq {a b : Type _} (H : a = b) : a ↔ b :=
eq.rec_on H iff.rfl

@[hott, trans] def iff.trans (H₁ : a ↔ b) (H₂ : b ↔ c) : a ↔ c :=
iff.intro
  (assume Ha, iff.mp H₂ (iff.mp H₁ Ha))
  (assume Hc, iff.mpr H₁ (iff.mpr H₂ Hc))

@[hott, trans] def iff.trans_eq {a b c : Type _} (H₁ : a ↔ b) (H₂ : b = c) : a ↔ c :=
iff.trans H₁ (iff.of_eq H₂)

@[hott, trans] def iff.eq_trans {a b c : Type _} (H₁ : a = b) (H₂ : b ↔ c) : a ↔ c :=
iff.trans (iff.of_eq H₁) H₂

@[hott, symm] def iff.symm (H : a ↔ b) : b ↔ a :=
iff.intro (iff.elim_right H) (iff.elim_left H)

@[hott] def iff.comm : (a ↔ b) ↔ (b ↔ a) :=
iff.intro iff.symm iff.symm

@[hott] def not_iff_not_of_iff (H₁ : a ↔ b) : ¬a ↔ ¬b :=
iff.intro
 (assume (Hna : ¬ a) (Hb : b), Hna (iff.elim_right H₁ Hb))
 (assume (Hnb : ¬ b) (Ha : a), Hnb (iff.elim_left H₁ Ha))

@[hott] def of_iff_unit (H : a ↔ unit) : a :=
iff.mp (iff.symm H) ()

@[hott] def not_of_iff_empty : (a ↔ empty) → ¬a := iff.mp

@[hott] def iff_unit_intro (H : a) : a ↔ unit :=
iff.intro
  (λ Hl, ())
  (λ Hr, H)

@[hott] def iff_empty_intro (H : ¬a) : a ↔ empty :=
iff.intro H (empty.rec _)

@[hott] def not_non_contradictory_iff_absurd (a : Type _) : ¬¬¬a ↔ ¬a :=
iff.intro
  (λ (Hl : ¬¬¬a) (Ha : a), Hl (non_contradictory_intro Ha))
  absurd

@[hott, congr] def imp_congr (H1 : a ↔ c) (H2 : b ↔ d) : (a → b) ↔ (c → d) :=
iff.intro
  (λHab Hc, iff.mp H2 (Hab (iff.mpr H1 Hc)))
  (λHcd Ha, iff.mpr H2 (Hcd (iff.mp H1 Ha)))

@[hott] def not_not_intro (Ha : a) : ¬¬a :=
assume Hna : ¬a, Hna Ha

@[hott] def not_of_not_not_not (H : ¬¬¬a) : ¬a :=
λ Ha, absurd (not_not_intro Ha) H

@[hott, hsimp] def not_unit : (¬ unit) ↔ empty :=
iff_empty_intro (not_not_intro ())

@[hott, hsimp] def not_empty_iff : (¬ empty) ↔ unit :=
iff_unit_intro not_empty

@[hott] def not_congr (H : a ↔ b) : ¬a ↔ ¬b :=
iff.intro (λ H₁ H₂, H₁ (iff.mpr H H₂)) (λ H₁ H₂, H₁ (iff.mp H H₂))

@[hott, hsimp] def ne_self_iff_empty {A : Type _} (a : A) : (not (a = a)) ↔ empty :=
iff.intro empty_of_ne empty.elim

@[hott, hsimp] def eq_self_iff_unit {A : Type _} (a : A) : (a = a) ↔ unit :=
iff_unit_intro rfl

@[hott, hsimp] def iff_not_self (a : Type _) : (a ↔ ¬a) ↔ empty :=
iff_empty_intro (λ H,
   have H' : ¬a, from (λ Ha, (iff.mp H Ha) Ha),
   H' (iff.mpr H H'))

@[hott, hsimp] def not_iff_self (a : Type _) : (¬a ↔ a) ↔ empty :=
iff_empty_intro (λ H,
   have H' : ¬a, from (λ Ha, (iff.mpr H Ha) Ha),
   H' (iff.mp H H'))

@[hott, hsimp] def unit_iff_empty : (unit ↔ empty) ↔ empty :=
iff_empty_intro (λ H, iff.mp H ())

@[hott, hsimp] def empty_iff_unit : (empty ↔ unit) ↔ empty :=
iff_empty_intro (λ H, iff.mpr H ())

@[hott] def empty_of_unit_iff_empty : (unit ↔ empty) → empty :=
assume H, iff.mp H ()

/- prod simp rules -/
@[hott] def prod.imp {a b c d} (H₂ : a → c) (H₃ : b → d) : a × b → c × d
| ⟨ha, hb⟩ := ⟨H₂ ha, H₃ hb⟩

@[hott, congr] def prod_congr (H1 : a ↔ c) (H2 : b ↔ d) : (a × b) ↔ (c × d) :=
iff.intro (prod.imp (iff.mp H1) (iff.mp H2)) (prod.imp (iff.mpr H1) (iff.mpr H2))

@[hott, hsimp] def prod.comm : a × b ↔ b × a :=
iff.intro prod.swap prod.swap

@[hott, hsimp] def prod.assoc : (a × b) × c ↔ a × (b × c) :=
iff.intro
  (λ ⟨⟨Ha, Hb⟩, Hc⟩, ⟨Ha, ⟨Hb, Hc⟩⟩)
  (λ ⟨Ha, ⟨Hb, Hc⟩⟩, ⟨⟨Ha, Hb⟩, Hc⟩)

@[hott, hsimp] def prod.fst_comm : a × (b × c) ↔ b × (a × c) :=
iff.intro
  (λ ⟨Ha, ⟨Hb, Hc⟩⟩, ⟨Hb, ⟨Ha, Hc⟩⟩)
  (λ ⟨Hb, ⟨Ha, Hc⟩⟩, ⟨Ha, ⟨Hb, Hc⟩⟩)

@[hott] def prod_iff_left {a b : Type _} (Hb : b) : (a × b) ↔ a :=
iff.intro prod.fst (λHa, prod.mk Ha Hb)

@[hott] def prod_iff_right {a b : Type _} (Ha : a) : (a × b) ↔ b :=
iff.intro prod.snd (prod.mk Ha)

@[hott, hsimp] def prod_unit (a : Type _) : a × unit ↔ a :=
prod_iff_left ()

@[hott, hsimp] def unit_prod (a : Type _) : unit × a ↔ a :=
prod_iff_right ()

@[hott, hsimp] def prod_empty (a : Type _) : a × empty ↔ empty :=
iff_empty_intro prod.snd

@[hott, hsimp] def empty_prod  (a : Type _) : empty × a ↔ empty :=
iff_empty_intro prod.fst

@[hott, hsimp] def not_prod_self (a : Type _) : (¬a × a) ↔ empty :=
iff_empty_intro (λ H, prod.elim H (λ H₁ H₂, absurd H₂ H₁))

@[hott, hsimp] def prod_not_self (a : Type _) : (a × ¬a) ↔ empty :=
iff_empty_intro (λ H, prod.elim H (λ H₁ H₂, absurd H₁ H₂))

@[hott, hsimp] def prod_self (a : Type _) : a × a ↔ a :=
iff.intro prod.fst (assume H, prod.mk H H)

/- sum simp rules -/

@[hott] def sum.imp (H₂ : a → c) (H₃ : b → d) : a ⊎ b → c ⊎ d
| (sum.inl H) := sum.inl (H₂ H)
| (sum.inr H) := sum.inr (H₃ H)

@[hott] def sum.imp_left (H : a → b) : a ⊎ c → b ⊎ c :=
sum.imp H id

@[hott] def sum.imp_right (H : a → b) : c ⊎ a → c ⊎ b :=
sum.imp id H

@[hott, congr] def sum_congr (H1 : a ↔ c) (H2 : b ↔ d) : (a ⊎ b) ↔ (c ⊎ d) :=
iff.intro (sum.imp (iff.mp H1) (iff.mp H2)) (sum.imp (iff.mpr H1) (iff.mpr H2))

@[hott, hsimp] def sum.comm : a ⊎ b ↔ b ⊎ a := iff.intro sum.swap sum.swap

@[hott, hsimp] def sum.assoc : (a ⊎ b) ⊎ c ↔ a ⊎ (b ⊎ c) :=
iff.intro
  (λ Habc, match Habc with
    | sum.inl (sum.inl Ha) := sum.inl Ha
    | sum.inl (sum.inr Hb) := sum.inr (sum.inl Hb)
    | sum.inr Hc := sum.inr (sum.inr Hc)
    end)
  (λ Habc, match Habc with
    | sum.inl Ha := sum.inl (sum.inl Ha)
    | sum.inr (sum.inl Hb) := sum.inl (sum.inr Hb)
    | sum.inr (sum.inr Hc) := sum.inr Hc
    end)

@[hott, hsimp] def sum.left_comm : a ⊎ (b ⊎ c) ↔ b ⊎ (a ⊎ c) :=
begin
  transitivity, {symmetry, exact sum.assoc},
  transitivity, {apply sum_congr, apply sum.comm, refl},
  apply sum.assoc
end

@[hott, hsimp] def sum_unit (a : Type _) : a ⊎ unit ↔ unit :=
iff_unit_intro (sum.inr ())

@[hott, hsimp] def unit_sum (a : Type _) : unit ⊎ a ↔ unit :=
iff_unit_intro (sum.inl ())

@[hott, hsimp] def sum_empty (a : Type _) : a ⊎ empty ↔ a :=
iff.intro (λ Hae, match Hae with sum.inl Ha := Ha end) sum.inl

@[hott, hsimp] def empty_sum (a : Type _) : empty ⊎ a ↔ a :=
iff.trans sum.comm (sum_empty _)

@[hott, hsimp] def sum_self (a : Type _) : a ⊎ a ↔ a :=
iff.intro (λ Haa, Haa.elim id id) sum.inl

/- sum resolution rulse -/

@[hott] def sum.resolve_left {a b : Type _} (H : a ⊎ b) (na : ¬ a) : b :=
  sum.elim H (λ Ha, absurd Ha na) id

@[hott] def sum.neg_resolve_left {a b : Type _} (H : ¬ a ⊎ b) (Ha : a) : b :=
  sum.elim H (λ na, absurd Ha na) id

@[hott] def sum.resolve_right {a b : Type _} (H : a ⊎ b) (nb : ¬ b) : a :=
  sum.elim H id (λ Hb, absurd Hb nb)

@[hott] def sum.neg_resolve_right {a b : Type _} (H : a ⊎ ¬ b) (Hb : b) : a :=
  sum.elim H id (λ nb, absurd Hb nb)

/- iff simp rules -/

@[hott, hsimp] def iff_unit (a : Type _) : (a ↔ unit) ↔ a :=
iff.intro (assume H, iff.mpr H star) iff_unit_intro

@[hott, hsimp] def unit_iff (a : Type _) : (unit ↔ a) ↔ a :=
iff.trans iff.comm (iff_unit _)

@[hott, hsimp] def iff_empty (a : Type _) : (a ↔ empty) ↔ ¬ a :=
iff.intro prod.fst iff_empty_intro

@[hott, hsimp] def empty_iff (a : Type _) : (empty ↔ a) ↔ ¬ a :=
iff.trans iff.comm (iff_empty _)

@[hott, hsimp] def iff_self (a : Type _) : (a ↔ a) ↔ unit :=
iff_unit_intro iff.rfl

@[hott, congr] def iff_congr (H1 : a ↔ c) (H2 : b ↔ d) : (a ↔ b) ↔ (c ↔ d) :=
prod_congr (imp_congr H1 H2) (imp_congr H2 H1)

/- decidable -/

class inductive decidable (p : Type u) : Type u
| inl :  p → decidable
| inr : ¬p → decidable

@[hott, instance] def decidable_unit : decidable unit :=
decidable.inl ()

@[hott, instance] def decidable_empty : decidable empty :=
decidable.inr not_empty

-- We use "dependent" if-then-else to be able to communicate the if-then-else condition
-- to the branches
@[hott] def dite (c : Type _) [H : decidable c] {A : Type _} (Hp : c → A) (Hn : ¬ c → A): A :=
decidable.rec_on H Hp Hn

/- if-then-else -/

@[hott] def ite (c : Type _) [H : decidable c] {A : Type _} (t e : A) : A :=
decidable.rec_on H (λ Hc, t) (λ Hnc, e)

hott_theory_cmd "local notation `if' ` c ` then ` t:45 ` else ` e:45 := hott.ite c t e"
hott_theory_cmd "local notation `if ` binder ` :: ` c ` then ` t:scoped ` else ` e:scoped := hott.dite c t e"

namespace decidable
  variables {p : Type _} {q : Type _}

  @[hott] def by_cases {q : Type _} [C : decidable p] : (p → q) → (¬p → q) → q := dite _

  @[hott] theorem em (p : Type _) [H : decidable p] : p ⊎ ¬p := by_cases sum.inl sum.inr

  @[hott] theorem by_contradiction [Hp : decidable p] (H : ¬p → empty) : p :=
  if H1 :: p then H1 else empty.rec _ (H H1)
end decidable

section
  variables {p : Type _} {q : Type _}
  open hott.decidable
  @[hott] def decidable_of_decidable_of_iff (Hp : decidable p) (H : p ↔ q) : decidable q :=
  if Hp :: p then inl (iff.mp H Hp)
  else inr (iff.mp (not_iff_not_of_iff H) Hp)

  @[hott] def decidable_of_decidable_of_eq {p q : Type _} (Hp : decidable p) (H : p = q)
    : decidable q :=
  decidable_of_decidable_of_iff Hp (iff.of_eq H)

  @[hott] protected def sum.by_cases [Hp : decidable p] [Hq : decidable q] {A : Type _}
                                   (h : p ⊎ q) (h₁ : p → A) (h₂ : q → A) : A :=
  if hp :: p then h₁ hp else
    if hq :: q then h₂ hq else
      empty.rec _ (sum.elim h hp hq)
end

section
  variables {p : Type _} {q : Type _}
  open hott.decidable

  @[hott, instance] def decidable_prod [Hp : decidable p] [Hq : decidable q] : decidable (p × q) :=
  if hp :: p then
    if hq :: q then inl (prod.mk hp hq)
    else inr (assume H : p × q, hq H.snd)
  else inr (assume H : p × q, hp H.fst)

  @[hott, instance] def decidable_sum [Hp : decidable p] [Hq : decidable q] : decidable (p ⊎ q) :=
  if hp :: p then inl (sum.inl hp) else
    if hq :: q then inl (sum.inr hq) else
      inr (λ hpq, sum.rec hp hq hpq)

  @[hott, instance] def decidable_not [Hp : decidable p] : decidable (¬p) :=
  if hp :: p then inr (absurd hp) else inl hp

  @[hott, instance] def decidable_implies [Hp : decidable p] [Hq : decidable q] : decidable (p → q) :=
  if hp :: p then
    if hq :: q then inl (assume H, hq)
    else inr (assume H : p → q, absurd (H hp) hq)
  else inl (assume Hp, absurd Hp hp)

  @[hott, instance] def decidable_iff [Hp : decidable p] [Hq : decidable q] : decidable (p ↔ q) :=
  decidable_prod

end

@[hott, reducible] def decidable_pred {A : Type _} (R : A   →   Type _) := Π (a   : A), decidable (R a)
@[hott, reducible] def decidable_rel {A : Type _} (R : A → A → Type _) := Π (a b : A), decidable (R a b)
@[hott, reducible] def decidable_eq (A : Type _) := decidable_rel (@eq A)
@[hott, reducible, instance] def decidable_ne {A : Type _} [H : decidable_eq A] (a b : A) : decidable (a ≠ b) :=
decidable_implies

namespace bool
  protected def no_confusion {P : Sort u} {v1 v2 : bool} (H12 : v1 = v2) : bool.no_confusion_type P v1 v2 :=
  eq.rec (λ (H11 : v1 = v1), bool.cases_on v1 (λ (a : P), a) (λ (a : P), a)) H12 H12

  @[hott] def ff_ne_tt : ff = tt → empty :=
  bool.no_confusion
end bool

open hott.bool
@[hott] def is_dec_eq {A : Type _} (p : A → A → bool) : Type _   := Π ⦃x y : A⦄, p x y = tt → x = y
@[hott] def is_dec_refl {A : Type _} (p : A → A → bool) : Type _ := Πx, p x x = tt

open hott.decidable
@[hott, instance] protected def bool.has_decidable_eq : Πa b : bool, decidable (a = b)
| ff ff := inl rfl
| ff tt := inr ff_ne_tt
| tt ff := inr (ne.symm ff_ne_tt)
| tt tt := inl rfl

@[hott] def decidable_eq_of_bool_pred {A : Type _} {p : A → A → bool} (H₁ : is_dec_eq p) (H₂ : is_dec_refl p) : decidable_eq A :=
λ x y : A, if Hp :: p x y = tt then inl (H₁ Hp)
 else inr begin intro Hxy, apply Hp, rwr Hxy, apply H₂ end

/- inhabited -/

@[hott] protected def inhabited.value {A : Type _} : inhabited A → A
| ⟨v⟩ := v

@[hott] protected def inhabited.destruct {A : Type _} {B : Type _} (H1 : inhabited A) (H2 : A → B) : B :=
inhabited.rec H2 H1

/- subsingleton -/

class subsingleton (A : Type _) :=
(prop : (Π a b : A, a = b))

@[hott] protected def subsingleton.elim {A : Type _} [H : subsingleton A] : Π(a b : A), a = b :=
subsingleton.rec (λp, p) H

@[hott] protected theorem rec_subsingleton {p : Type _} [H : decidable p]
    {H1 : p → Type _} {H2 : ¬p → Type _}
    [H3 : Π(h : p), subsingleton (H1 h)] [H4 : Π(h : ¬p), subsingleton (H2 h)]
  : subsingleton (decidable.rec_on H H1 H2) :=
decidable.rec_on H (λh, H3 h) (λh, H4 h) --this can be proven using dependent version of "by_cases"

@[hott] def if_pos {c : Type _} [H : decidable c] (Hc : c) {A : Type _} {t e : A} : (ite c t e) = t :=
decidable.rec
  (λ Hc : c,    eq.refl (@ite c (decidable.inl Hc) A t e))
  (λ Hnc : ¬c,  absurd Hc Hnc)
  H

@[hott] def if_neg {c : Type _} [H : decidable c] (Hnc : ¬c) {A : Type _} {t e : A} : (ite c t e) = e :=
decidable.rec
  (λ Hc : c,    absurd Hc Hnc)
  (λ Hnc : ¬c,  eq.refl (@ite c (decidable.inr Hnc) A t e))
  H

@[hott, hsimp] theorem if_t_t (c : Type _) [H : decidable c] {A : Type _} (t : A) : (ite c t t) = t :=
decidable.rec
  (λ Hc  : c,  eq.refl (@ite c (decidable.inl Hc)  A t t))
  (λ Hnc : ¬c, eq.refl (@ite c (decidable.inr Hnc) A t t))
  H

@[hott] theorem implies_of_if_pos {c t e : Type _} [H : decidable c] (h : ite c t e) : c → t :=
assume Hc, transport id (if_pos Hc) h

@[hott] theorem implies_of_if_neg {c t e : Type _} [H : decidable c] (h : ite c t e) : ¬c → e :=
assume Hc, transport id (if_neg Hc) h

@[hott] theorem if_ctx_congr {A : Type _} {b c : Type _} [dec_b : decidable b] [dec_c : decidable c]
                     {x y u v : A}
                     (h_c : b ↔ c) (h_t : c → x = u) (h_e : ¬c → y = v) :
        ite b x y = ite c u v :=
if hp :: b then
  calc
    ite b x y = x           : if_pos hp
         ...  = u           : h_t (iff.mp h_c hp)
         ...  = ite c u v   : (if_pos (iff.mp h_c hp)).inverse
else
  calc
    ite b x y = y         : if_neg hp
         ...  = v         : h_e (iff.mp (not_iff_not_of_iff h_c) hp)
         ...  = ite c u v : (if_neg (iff.mp (not_iff_not_of_iff h_c) hp)).inverse

@[hott, congr] theorem if_congr {A : Type _} {b c : Type _} [dec_b : decidable b] [dec_c : decidable c]
                 {x y u v : A}
                 (h_c : b ↔ c) (h_t : x = u) (h_e : y = v) :
        ite b x y = ite c u v :=
@if_ctx_congr A b c dec_b dec_c x y u v h_c (λ h, h_t) (λ h, h_e)

@[hott, congr] theorem if_ctx_simp_congr {A : Type _} {b c : Type _} [dec_b : decidable b] {x y u v : A}
                        (h_c : b ↔ c) (h_t : c → x = u) (h_e : ¬c → y = v) :
        ite b x y = (@ite c (decidable_of_decidable_of_iff dec_b h_c) A u v) :=
@if_ctx_congr A b c dec_b (decidable_of_decidable_of_iff dec_b h_c) x y u v h_c h_t h_e

@[hott, congr] theorem if_simp_congr {A : Type _} {b c : Type _} [dec_b : decidable b] {x y u v : A}
                 (h_c : b ↔ c) (h_t : x = u) (h_e : y = v) :
        ite b x y = (@ite c (decidable_of_decidable_of_iff dec_b h_c) A u v) :=
@if_ctx_simp_congr A b c dec_b x y u v h_c (λ h, h_t) (λ h, h_e)

@[hott, hsimp] def if_unit {A : Type _} (t e : A) : (if' unit then t else e) = t :=
if_pos star

@[hott, hsimp] def if_empty {A : Type _} (t e : A) : (if' empty then t else e) = e :=
if_neg not_empty

@[hott] theorem if_ctx_congr_prop {b c x y u v : Type _} [dec_b : decidable b] [dec_c : decidable c]
                      (h_c : b ↔ c) (h_t : c → (x ↔ u)) (h_e : ¬c → (y ↔ v)) :
        ite b x y ↔ ite c u v :=
if hp :: b then
  calc
    ite b x y ↔ x         : iff.of_eq (if_pos hp)
         ...  ↔ u         : h_t (iff.mp h_c hp)
         ...  ↔ ite c u v : iff.of_eq (if_pos (iff.mp h_c hp)).inverse
else
  calc
    ite b x y ↔ y         : iff.of_eq (if_neg hp)
         ...  ↔ v         : h_e (iff.mp (not_iff_not_of_iff h_c) hp)
         ...  ↔ ite c u v : iff.of_eq (if_neg (iff.mp (not_iff_not_of_iff h_c) hp)).inverse

@[hott, congr] theorem if_congr_prop {b c x y u v : Type _} [dec_b : decidable b] [dec_c : decidable c]
                      (h_c : b ↔ c) (h_t : x ↔ u) (h_e : y ↔ v) :
        ite b x y ↔ ite c u v :=
if_ctx_congr_prop h_c (λ h, h_t) (λ h, h_e)

@[hott] theorem if_ctx_simp_congr_prop {b c x y u v : Type _} [dec_b : decidable b]
                               (h_c : b ↔ c) (h_t : c → (x ↔ u)) (h_e : ¬c → (y ↔ v)) :
        ite b x y ↔ (@ite c (decidable_of_decidable_of_iff dec_b h_c) _ u v) :=
@if_ctx_congr_prop b c x y u v dec_b (decidable_of_decidable_of_iff dec_b h_c) h_c h_t h_e

@[hott, congr] theorem if_simp_congr_prop {b c x y u v : Type _} [dec_b : decidable b]
                           (h_c : b ↔ c) (h_t : x ↔ u) (h_e : y ↔ v) :
        ite b x y ↔ (@ite c (decidable_of_decidable_of_iff dec_b h_c) _ u v) :=
@if_ctx_simp_congr_prop b c x y u v dec_b h_c (λ h, h_t) (λ h, h_e)

-- Remark: dite and ite are "definitionally equal" when we ignore the proofs.
@[hott] theorem dite_ite_eq (c : Type _) [H : decidable c] {A : Type _} (t : A) (e : A) :
  dite c (λh, t) (λh, e) = ite c t e :=
by refl

@[hott] def is_unit (c : Type _) [H : decidable c] : Type :=
if' c then unit else empty

@[hott] def is_empty (c : Type _) [H : decidable c] : Type :=
if' c then empty else unit

@[hott] def of_is_unit {c : Type _} [H₁ : decidable c] (H₂ : is_unit c) : c :=
if Hc :: c then Hc else begin induction H₁, assumption, cases H₂ end

notation `dec_star` := of_is_unit star

@[hott] theorem not_of_not_is_unit {c : Type _} [H₁ : decidable c] (H₂ : ¬ is_unit c) : ¬ c :=
if Hc :: c then absurd star (if_pos Hc ▸ H₂) else Hc

@[hott] theorem not_of_is_empty {c : Type _} [H₁ : decidable c] (H₂ : is_empty c) : ¬ c :=
if Hc :: c then begin induction H₁, cases H₂, assumption end else Hc

@[hott] theorem of_not_is_empty {c : Type _} [H₁ : decidable c] (H₂ : ¬ is_empty c) : c :=
if Hc :: c then Hc else absurd star (if_neg Hc ▸ H₂)

end hott
