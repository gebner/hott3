/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Floris van Doorn

Definition of is_trunc (n-truncatedness)

Ported from Coq HoTT.
-/
import .equiv .pathover .logic

universes u v l
hott_theory

namespace hott

open hott.eq nat sigma unit

/- Truncation levels -/

inductive trunc_index : Type
| minus_two : trunc_index
| succ : trunc_index → trunc_index

open trunc_index

/-
   notation for trunc_index is -2, -1, 0, 1, ...
   from 0 and up this comes from the way numerals are parsed in Lean.
   Any structure with a 0, a 1, and a + have numerals defined in them.
-/

notation `ℕ₋₂` := trunc_index -- input using \N-2

instance has_zero_trunc_index : has_zero ℕ₋₂ :=
has_zero.mk (succ (succ minus_two))

instance has_one_trunc_index : has_one ℕ₋₂ :=
has_one.mk (succ (succ (succ minus_two)))

namespace trunc_index

  notation `-1` := trunc_index.succ trunc_index.minus_two -- ISSUE: -1 gets printed as -2.+1?
  notation `-2` := trunc_index.minus_two
  postfix `.+1`:(max+1) := trunc_index.succ
  postfix `.+2`:(max+1) := λn, (n .+1 .+1)

  --addition, where we add two to the result
  @[hott] def add_plus_two (n m : ℕ₋₂) : ℕ₋₂ :=
  trunc_index.rec_on m n (λ k l, l .+1)

  infix ` +2+ `:65 := trunc_index.add_plus_two

  -- addition of trunc_indices, where results smaller than -2 are changed to -2
  @[hott] protected def add (n m : ℕ₋₂) : ℕ₋₂ :=
  trunc_index.cases_on m
    (trunc_index.cases_on n -2 (λn', (trunc_index.cases_on n' -2 id)))
    (λm', trunc_index.cases_on m'
      (trunc_index.cases_on n -2 id)
      (add_plus_two n))

  /- we give a weird name to the reflexivity step to avoid overloading le.refl
     (which can be used if types.trunc is imported) -/
  inductive le (a : ℕ₋₂) : ℕ₋₂ → Type
  | tr_refl : le a
  | step : Π {b}, le b → le (b.+1)

  attribute [refl] le.tr_refl

end trunc_index

local infix ` ≤ ` := trunc_index.le -- TODO(gabriel)

instance has_add_trunc_index : has_add ℕ₋₂ :=
has_add.mk trunc_index.add

namespace trunc_index

  @[hott] def sub_two (n : ℕ) : ℕ₋₂ :=
  nat.rec_on n -2 (λ n k, k.+1)

  @[hott] def add_two (n : ℕ₋₂) : ℕ :=
  trunc_index.rec_on n nat.zero (λ n k, nat.succ k)

  postfix `.-2`:(max+1) := sub_two
  postfix `.-1`:(max+1) := λn, (n .-2 .+1)

  @[hott] def of_nat (n : ℕ) : ℕ₋₂ :=
  n.-2.+2

  instance: has_coe ℕ ℕ₋₂ := ⟨of_nat⟩

  @[hott] def succ_le_succ {n m : ℕ₋₂} (H : n ≤ m) : n.+1 ≤ m.+1 :=
  begin induction H, refl, apply le.step; assumption end

  @[hott] def minus_two_le (n : ℕ₋₂) : -2 ≤ n :=
  begin induction n, refl, apply le.step; assumption end

end trunc_index open trunc_index

namespace is_trunc

  -- export [notation] [coercion] trunc_index

  /- truncated types -/

  /-
    Just as in Coq HoTT we define an internal version of contractibility and is_trunc, but we only
    use `is_trunc` and `is_contr`
  -/

  structure contr_internal (A : Type u) :=
    (center : A)
    (center_eq : Π(a : A), center = a)

  @[hott] def is_trunc_internal (n : ℕ₋₂) : Type u → Type u :=
    trunc_index.rec_on n
      (λA, contr_internal A)
      (λn trunc_n A, (Π(x y : A), trunc_n (x = y)))

end is_trunc open is_trunc

class is_trunc (n : ℕ₋₂) (A : Type u) :=
  (to_internal : is_trunc_internal n A)

open nat trunc_index

namespace is_trunc

  notation `is_contr` := is_trunc -2
  notation `is_prop` := is_trunc -1
  notation `is_set`  := is_trunc 0

  variables {A : Type u} {B : Type v}

  @[hott] def is_trunc_succ_intro {A : Type _} {n : ℕ₋₂} (H : ∀x y : A, is_trunc n (x = y))
    : is_trunc n.+1 A :=
  is_trunc.mk (λ x y, is_trunc.to_internal _ _)

  @[hott, instance] def is_trunc_eq
    (n : ℕ₋₂) [H : is_trunc (n.+1) A] (x y : A) : is_trunc n (x = y) :=
  is_trunc.mk (is_trunc.to_internal (n.+1) A x y)

  /- contractibility -/

  @[hott] def is_contr.mk (center : A) (center_eq : Π(a : A), center = a) : is_contr A :=
  is_trunc.mk (contr_internal.mk center center_eq)

  @[hott] def center (A : Type _) [H : is_contr A] : A :=
  contr_internal.center (is_trunc.to_internal -2 A)

  @[hott] def center' {A : Type _} (H : is_contr A) : A := center A

  @[hott] def center_eq [H : is_contr A] (a : A) : center _ = a :=
  contr_internal.center_eq (is_trunc.to_internal -2 A) a

  @[hott] def eq_of_is_contr [H : is_contr A] (x y : A) : x = y :=
  (center_eq x)⁻¹ ⬝ (center_eq y)

  @[hott] def prop_eq_of_is_contr {A : Type _} [H : is_contr A] {x y : A} (p q : x = y) : p = q :=
  have K : ∀ (r : x = y), eq_of_is_contr x y = r, from (λ r, by induction r; apply con.left_inv),
  (K p)⁻¹ ⬝ K q

  @[hott] def is_contr_eq {A : Type _} [H : is_contr A] (x y : A) : is_contr (x = y) :=
  is_contr.mk (eq_of_is_contr _ _) (λ p, prop_eq_of_is_contr _ _)

  /- truncation is upward close -/

  -- n-types are also (n+1)-types
  @[hott, instance] def is_trunc_succ (A : Type _) (n : ℕ₋₂)
    [H : is_trunc n A] : is_trunc (n.+1) A :=
  begin
    induction n with n IH generalizing A; apply is_trunc_succ_intro; intros x y,
    { exact @is_contr_eq A H x y },
    { refine @IH _ (@is_trunc_eq _ _ H _ _) , }
  end

  --in the proof the type of H is given explicitly to make it available for class inference

  @[hott] def is_trunc_of_le (A : Type.{l}) {n m : ℕ₋₂} (Hnm : n ≤ m)
    [Hn : is_trunc n A] : is_trunc m A :=
  begin
    induction Hnm with m Hnm IH,
    { exact Hn },
    { exact @is_trunc_succ _ _ IH }
  end

  @[hott] def is_trunc_of_imp_is_trunc {n : ℕ₋₂} (H : A → is_trunc (n.+1) A)
    : is_trunc (n.+1) A :=
  @is_trunc_succ_intro _ _ (λx y, @is_trunc_eq _ _ (H x) x y)

  @[hott] def is_trunc_of_imp_is_trunc_of_le {n : ℕ₋₂} (Hn : -1 ≤ n) (H : A → is_trunc n A)
    : is_trunc n A :=
  begin
    induction Hn with n' Hn'; apply is_trunc_of_imp_is_trunc H
  end

  -- these must be definitions, because we need them to compute sometimes
  @[hott] def is_trunc_of_is_contr (A : Type _) (n : ℕ₋₂) [H : is_contr A] : is_trunc n A :=
  trunc_index.rec_on n H (λn H, by apply_instance)

  @[hott] def is_trunc_succ_of_is_prop (A : Type _) (n : ℕ₋₂) [H : is_prop A]
      : is_trunc (n.+1) A :=
  is_trunc_of_le A (show -1 ≤ n.+1, from succ_le_succ (minus_two_le n))

  @[hott] def is_trunc_succ_succ_of_is_set (A : Type _) (n : ℕ₋₂) [H : is_set A]
      : is_trunc (n.+2) A :=
  is_trunc_of_le A (show 0 ≤ n.+2, from succ_le_succ (succ_le_succ (minus_two_le n)))

  /- props -/

  @[hott] def is_prop.elim [H : is_prop A] (x y : A) : x = y :=
  by apply center

  @[hott] def is_prop.elim' (x y : A) (H : is_prop A) : x = y :=
  is_prop.elim x y

  @[hott] def is_contr_of_inhabited_prop {A : Type _} [H : is_prop A] (x : A) : is_contr A :=
  is_contr.mk x (λy, by apply is_prop.elim)

  @[hott] def is_prop_of_imp_is_contr {A : Type _} (H : A → is_contr A) : is_prop A :=
  @is_trunc_succ_intro A -2
    (λx y,
      have H2 : is_contr A, from H x,
      by apply is_contr_eq)

  @[hott] def is_prop.mk {A : Type _} (H : ∀x y : A, x = y) : is_prop A :=
  is_prop_of_imp_is_contr (λ x, is_contr.mk x (H x))

  @[hott] def is_prop_elim_self {A : Type _} {H : is_prop A} (x : A) : is_prop.elim x x = idp :=
  by apply is_prop.elim

  /- sets -/

  @[hott] def is_set.mk (A : Type _) (H : ∀(x y : A) (p q : x = y), p = q) : is_set A :=
  @is_trunc_succ_intro _ _ (λ x y, is_prop.mk (H x y))

  @[hott] def is_set.elim [H : is_set A] ⦃x y : A⦄ (p q : x = y) : p = q :=
  by apply is_prop.elim

  @[hott] def is_set.elim' ⦃x y : A⦄ (p q : x = y) (H : is_set A) : p = q :=
  is_set.elim p q

  /- instances -/

  @[instance, hott] def is_contr_sigma_eq {A : Type u} (a : A)
    : is_contr (Σ(x : A), a = x) :=
  is_contr.mk (sigma.mk a idp) (λ ⟨b,q⟩, by induction q; refl)

  @[instance, hott] def is_contr_sigma_eq' {A : Type u} (a : A)
    : is_contr (Σ(x : A), x = a) :=
  is_contr.mk (sigma.mk a idp) (λ ⟨b,q⟩, by clear _fun_match; induction q; refl)

  @[hott] def ap_fst_center_eq_sigma_eq {A : Type _} {a x : A} (p : a = x)
    : ap sigma.fst (center_eq ⟨x, p⟩) = p :=
  by induction p; reflexivity

  @[hott] def ap_fst_center_eq_sigma_eq' {A : Type _} {a x : A} (p : x = a)
    : ap sigma.fst (center_eq ⟨x, p⟩) = p⁻¹ :=
  by induction p; reflexivity

  @[hott] def is_contr_unit : is_contr unit :=
  is_contr.mk star (λp, unit.rec_on p idp)

  @[hott] def is_prop_empty : is_prop empty :=
  is_prop.mk (λx, by induction x)

  local attribute [instance] is_contr_unit is_prop_empty

  @[hott,instance] def is_trunc_unit (n : ℕ₋₂) : is_trunc n unit :=
  by apply is_trunc_of_is_contr

  @[hott,instance] def is_trunc_empty (n : ℕ₋₂) : is_trunc (n.+1) empty :=
  by apply is_trunc_succ_of_is_prop

  /- interaction with equivalences -/

  section
  open hott.is_equiv hott.equiv

  @[hott] def is_contr_is_equiv_closed (f : A → B) [Hf : is_equiv f] [HA: is_contr A]
    : (is_contr B) :=
  is_contr.mk (f (center A)) (λp, eq_of_eq_inv (center_eq _))

  @[hott] def is_contr_equiv_closed (H : A ≃ B) [HA: is_contr A] : is_contr B :=
  is_contr_is_equiv_closed H

  @[hott] def equiv_of_is_contr_of_is_contr [HA : is_contr A] [HB : is_contr B] : A ≃ B :=
  equiv.mk
    (λa, center B)
    (is_equiv.adjointify (λa, center B) (λb, center A) center_eq center_eq)

  @[hott] def is_trunc_is_equiv_closed (n : ℕ₋₂) (f : A → B) [H : is_equiv f]
    (HA : is_trunc n A) : is_trunc n B :=
  begin
    revert A B f H HA, induction n with n IH; intros,
    { exact is_contr_is_equiv_closed f },
    { apply is_trunc_succ_intro, intros, apply IH (ap f⁻¹ᶠ)⁻¹ᶠ, all_goals {apply_instance} }
  end

  @[hott] def is_trunc_is_equiv_closed_rev (n : ℕ₋₂) (f : A → B) [H : is_equiv f]
    (HA : is_trunc n B) : is_trunc n A :=
  is_trunc_is_equiv_closed n f⁻¹ᶠ HA

  @[hott] def is_trunc_equiv_closed (n : ℕ₋₂) (f : A ≃ B) (HA : is_trunc n A)
    : is_trunc n B :=
  is_trunc_is_equiv_closed n f HA

  @[hott] def is_trunc_equiv_closed_rev (n : ℕ₋₂) (f : A ≃ B) (HA : is_trunc n B)
    : is_trunc n A :=
  is_trunc_is_equiv_closed n f⁻¹ᶠ HA

  @[hott] def is_equiv_of_is_prop [HA : is_prop A] [HB : is_prop B]
    (f : A → B) (g : B → A) : is_equiv f :=
  by fapply is_equiv.mk f g; intros; {apply is_prop.elim <|> apply is_set.elim}

  @[hott] def is_equiv_of_is_contr [HA : is_contr A] [HB : is_contr B]
    (f : A → B) : is_equiv f :=
  by fapply is_equiv.mk f; intros; {apply center <|> apply is_prop.elim <|> apply is_set.elim}

  @[hott] def equiv_of_is_prop [HA : is_prop A] [HB : is_prop B]
    (f : A → B) (g : B → A) : A ≃ B :=
  equiv.mk f (is_equiv_of_is_prop f g)

  @[hott] def equiv_of_iff_of_is_prop [HA : is_prop A] [HB : is_prop B] (H : A ↔ B) : A ≃ B :=
  equiv_of_is_prop (iff.elim_left H) (iff.elim_right H)

  /- truncatedness of lift -/
  @[hott,instance] def is_trunc_lift (A : Type _) (n : ℕ₋₂)
    [H : is_trunc n A] : is_trunc n (ulift A) :=
  is_trunc_equiv_closed _ (equiv_lift _) H

  end

  /- interaction with the Unit type -/

  open equiv
  /- A contractible type is equivalent to unit. -/
  variable (A)
  @[hott] def equiv_unit_of_is_contr [H : is_contr A] : A ≃ unit :=
  equiv.MK (λ (x : A), ())
           (λ (u : unit), center A)
           (λ (u : unit), unit.rec_on u idp)
           (λ (x : A), center_eq x)

  /- interaction with pathovers -/
  variable {A}
  variables {C : A → Type _}
            {a a₂ : A} (p : a = a₂)
            (c : C a) (c₂ : C a₂)

  instance is_trunc_pathover
    (n : ℕ₋₂) [H : is_trunc (n.+1) (C a)] : is_trunc n (c =[p] c₂) :=
  begin
  refine @is_trunc_equiv_closed_rev _ _ n _ _, tactic.swap,
  apply pathover_equiv_eq_tr,
  apply is_trunc_eq,
  end

  @[hott] def is_prop.elimo [H : is_prop (C a)] : c =[p] c₂ :=
  pathover_of_eq_tr (by apply is_prop.elim)

  @[hott] def is_prop.elimo' (H : is_prop (C a)) : c =[p] c₂ :=
  is_prop.elimo p c c₂

  @[hott] def is_prop_elimo_self {A : Type _} (B : A → Type _) {a : A} (b : B a) {H : is_prop (B a)} :
    @is_prop.elimo A B a a idp b b H = idpo :=
  by apply is_prop.elim

  variables {p c c₂}
  @[hott] def is_set.elimo (q q' : c =[p] c₂) [H : is_set (C a)] : q = q' :=
  by apply is_prop.elim

  -- TODO: port "Truncated morphisms"

  /- truncated universe -/

end is_trunc

structure trunctype (n : ℕ₋₂) :=
  (carrier : Type u)
  (struct : is_trunc n carrier)

@[hott] instance (n): has_coe_to_sort (trunctype n) := {
  S := Type u,
  coe := trunctype.carrier
}

notation n `-Type` := trunctype n
hott_theory_cmd "local notation Prop := -1-Type"
notation `Set`  := 0-Type

-- attribute trunctype.carrier [coercion]
attribute [instance] trunctype.struct

notation `Prop.mk` := @trunctype.mk -1
notation `Set.mk` := @trunctype.mk (-1.+1)

@[hott] protected def trunctype.mk' (n : ℕ₋₂) (A : Type _) [H : is_trunc n A]
  : n-Type :=
trunctype.mk A H

namespace is_trunc

  @[hott] def tlift {n : ℕ₋₂} (A : trunctype.{u} n)
    : trunctype.{max u v} n :=
  trunctype.mk (ulift A) (is_trunc_lift _ _)

end is_trunc

end hott
