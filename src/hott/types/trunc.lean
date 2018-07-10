/-
Copyright (c) 2015 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn

Properties of trunc_index, is_trunc, trunctype, trunc, and the pointed versions of these
-/

-- NOTE: the fact that (is_trunc n A) is a mere proposition is proved in .prop_trunc

import ..function .unit
universes u v w
hott_theory
namespace hott

open hott.sigma hott.pi hott.function hott.equiv trunctype nat
     hott.is_equiv hott.prod pointed hott.nat hott.is_trunc hott.algebra hott.sum sum hott.unit

  /- basic computation with ℕ₋₂, its operations and its order -/
namespace trunc_index

instance has_le_trunc_index : has_le ℕ₋₂ :=
⟨trunc_index.le⟩

@[hott] def minus_one_le_succ (n : ℕ₋₂) : -1 ≤ n.+1 :=
succ_le_succ (minus_two_le n)

@[hott] def zero_le_of_nat (n : ℕ) : 0 ≤ of_nat n :=
succ_le_succ (minus_one_le_succ _)

@[hott, reducible] protected def code : ℕ₋₂ → ℕ₋₂ → Type
| -2       -2       := unit
| -2       (succ m) := empty
| (succ n) -2       := empty
| (succ n) (succ m) := n = m

@[hott] protected def refl : Πn, trunc_index.code n n
| -2       := ⋆
| (succ n) := idp

@[hott] protected def encode {n m : ℕ₋₂} (p : n = m) : trunc_index.code n m :=
p ▸ trunc_index.refl n

@[hott] protected def decode : Π(n m : ℕ₋₂), trunc_index.code n m → n = m
| -2       -2       := λc, idp
| -2       (succ l) := λc, empty.elim c
| (succ k) -2       := λc, empty.elim c
| (succ k) (succ l) := λc, ap succ c

@[hott] def succ_ne_minus_two (n : ℕ₋₂) : succ n ≠ -2 :=
trunc_index.encode

@[hott, instance] protected def has_decidable_eq : Π(n m : ℕ₋₂), decidable (n = m)
| -2     -2     := decidable.inl rfl
| (n.+1) -2     := decidable.inr trunc_index.encode
| -2     (m.+1) := decidable.inr trunc_index.encode
| (n.+1) (m.+1) :=
    match has_decidable_eq n m with
    | decidable.inl xeqy := decidable.inl (ap succ xeqy)
    | decidable.inr xney := decidable.inr (λh, xney (trunc_index.encode h))
    end

@[hott] def not_succ_le_minus_two {n : ℕ₋₂} (H : n .+1 ≤ -2) : empty :=
begin
  have : Πm, n.+1 ≤ m → m = -2 → empty,
  { intros m H, hinduction H with m H IH, exact succ_ne_minus_two n, exact succ_ne_minus_two m },
  exact this -2 H idp
end

@[hott] protected def le_trans {n m k : ℕ₋₂} (H1 : n ≤ m) (H2 : m ≤ k) : n ≤ k :=
begin
  induction H2 with k H2 IH,
  { exact H1},
  { exact le.step IH}
end

@[hott] protected def pred (n : ℕ₋₂) : ℕ₋₂ :=
trunc_index.rec -2 (λm _, m) n

@[hott] protected def pred_le (n : ℕ₋₂) : trunc_index.pred n ≤ n := by cases n; repeat { constructor }

@[hott] def pred_le_pred {n m : ℕ₋₂} (H : n ≤ m) : trunc_index.pred n ≤ trunc_index.pred m :=
begin 
  hinduction H with k H2 IH, apply le.tr_refl, exact trunc_index.le_trans IH (trunc_index.pred_le k)
end

@[hott] def le_of_succ_le_succ {n m : ℕ₋₂} (H : n.+1 ≤ m.+1) : n ≤ m :=
pred_le_pred H

@[hott] def not_succ_le_self {n : ℕ₋₂} : ¬n.+1 ≤ n :=
begin
  induction n with n IH; intro H,
  { exact not_succ_le_minus_two H},
  { exact IH (le_of_succ_le_succ H)}
end

@[hott] protected def le_antisymm {n m : ℕ₋₂} (H1 : n ≤ m) (H2 : m ≤ n) : n = m :=
begin
  induction H2 with n H2 IH,
  { refl },
  { apply empty.elim, apply @not_succ_le_self n, exact trunc_index.le_trans H1 H2}
end

@[hott] protected def le_succ {n m : ℕ₋₂} (H1 : n ≤ m) : n ≤ m.+1 :=
le.step H1

@[hott] protected def self_le_succ (n : ℕ₋₂) : n ≤ n.+1 :=
le.step (trunc_index.le.tr_refl n)

-- the order is total
@[hott] protected def le_sum_le (n m : ℕ₋₂) : n ≤ m ⊎ m ≤ n :=
begin
  induction m with m IH,
  { exact inr (minus_two_le _)},
  { cases IH with H H,
    { exact inl (trunc_index.le_succ H)},
    { hinduction H with n' H x,
      { exact inl (trunc_index.self_le_succ _)},
      { exact inr (succ_le_succ H)}}}
end

end trunc_index open trunc_index

@[hott, instance, reducible] def linear_weak_order_trunc_index :
  linear_weak_order trunc_index :=
linear_weak_order.mk le trunc_index.le.tr_refl @trunc_index.le_trans @trunc_index.le_antisymm
                     trunc_index.le_sum_le

namespace trunc_index

/- more theorems about truncation indices -/

@[hott] def zero_add (n : ℕ₋₂) : (0 : ℕ₋₂) + n = n :=
begin
  cases n with n, refl,
  cases n with n, refl,
  induction n with n IH, refl, exact ap succ IH
end

@[hott] def add_zero (n : ℕ₋₂) : n + (0 : ℕ₋₂) = n :=
by refl

@[hott] def succ_add_nat (n : ℕ₋₂) (m : ℕ) : n.+1 + m = (n + m).+1 :=
begin induction m with m IH, refl, exact ap succ IH end

@[hott] def nat_add_succ (n : ℕ) (m : ℕ₋₂) : ↑n + m.+1 = (n + m).+1 :=
begin
  cases m with m, refl,
  cases m with m, refl,
  induction m with m IH, refl, exact ap succ IH
end

@[hott] def add_nat_succ (n : ℕ₋₂) (m : ℕ) : n + (nat.succ m) = (n + m).+1 :=
by refl

@[hott] def nat_succ_add (n : ℕ) (m : ℕ₋₂) : ↑(nat.succ n) + m = (n + m).+1 :=
begin
  cases m with m, refl,
  cases m with m, refl,
  induction m with m IH, refl, exact ap succ IH
end

@[hott] def sub_two_add_two (n : ℕ₋₂) : sub_two (add_two n) = n :=
begin
  induction n with n IH,
  { refl },
  { exact ap succ IH}
end

@[hott] def add_two_sub_two (n : ℕ) : add_two (sub_two n) = n :=
begin
  induction n with n IH,
  { refl },
  { exact ap nat.succ IH}
end

@[hott] def of_nat_add_plus_two_of_nat (n m : ℕ) : n +2+ m = of_nat (n + m + 2) :=
begin
  induction m with m IH,
  { refl },
  { exact ap succ IH}
end

@[hott] def of_nat_add_of_nat (n m : ℕ) : of_nat n + of_nat m = of_nat (n + m) :=
begin
  induction m with m IH,
  { refl },
  { exact ap succ IH}
end

@[hott] def succ_add_plus_two (n m : ℕ₋₂) : n.+1 +2+ m = (n +2+ m).+1 :=
begin
  induction m with m IH,
  { refl },
  { exact ap succ IH}
end

@[hott] def add_plus_two_succ (n m : ℕ₋₂) : n +2+ m.+1 = (n +2+ m).+1 :=
idp

@[hott] def add_succ_succ (n m : ℕ₋₂) : n + m.+2 = n +2+ m :=
idp

@[hott] def succ_add_succ (n m : ℕ₋₂) : n.+1 + m.+1 = n +2+ m :=
begin
  cases m with m IH,
  { refl },
  { apply succ_add_plus_two}
end

@[hott] def succ_succ_add (n m : ℕ₋₂) : n.+2 + m = n +2+ m :=
begin
  cases m with m IH,
  { refl },
  { exact succ_add_succ _ _ ⬝ succ_add_plus_two _ _}
end

@[hott] def succ_sub_two (n : ℕ) : (nat.succ n).-2 = n.-2 .+1 := rfl
@[hott] def sub_two_succ_succ (n : ℕ) : n.-2.+1.+1 = n := rfl
@[hott] def succ_sub_two_succ (n : ℕ) : (nat.succ n).-2.+1 = n := rfl

@[hott] def of_nat_add_two (n : ℕ₋₂) : of_nat (add_two n) = n.+2 :=
begin induction n with n IH, refl, exact ap succ IH end

@[hott] def of_nat_le_of_nat {n m : ℕ} (H : n ≤ m) : (of_nat n ≤ of_nat m) :=
begin
  induction H with m H IH,
  { apply le.refl },
  { exact trunc_index.le_succ IH}
end

@[hott] def sub_two_le_sub_two {n m : ℕ} (H : n ≤ m) : n.-2 ≤ m.-2 :=
begin
  induction H with m H IH,
  { apply le.refl },
  { exact trunc_index.le_succ IH}
end

@[hott] def add_two_le_add_two {n m : ℕ₋₂} (H : n ≤ m) : add_two n ≤ add_two m :=
begin
  induction H with m H IH,
  { refl },
  { constructor, exact IH},
end

@[hott] def le_of_sub_two_le_sub_two {n m : ℕ} (H : n.-2 ≤ m.-2) : n ≤ m :=
begin
  rwr [←add_two_sub_two n, ←add_two_sub_two m],
  exact add_two_le_add_two H,
end

@[hott] def le_of_of_nat_le_of_nat {n m : ℕ} (H : of_nat n ≤ of_nat m) : n ≤ m :=
begin
  apply le_of_sub_two_le_sub_two,
  exact le_of_succ_le_succ (le_of_succ_le_succ H)
end

@[hott] protected theorem succ_le_of_not_le {n m : ℕ₋₂} (H : ¬ n ≤ m) : m.+1 ≤ n :=
begin
  cases (le.total n m) with H2 H2,
  { apply empty.elim, exact H H2},
  { hinduction H2 with n' H2' x,
    { apply empty.elim, exact H (le.refl _)},
    { exact succ_le_succ H2'}}
end

@[hott, instance] def trunc_index.decidable_le : Π(n m : ℕ₋₂), decidable (n ≤ m) :=
begin
  intro n, induction n with n IH; intro m,
  { left, apply minus_two_le},
  cases m with m,
  { right, apply not_succ_le_minus_two},
  cases IH m with H H,
  { left, apply succ_le_succ H},
  right, intro H2, apply H, exact le_of_succ_le_succ H2
end

end trunc_index open trunc_index

namespace is_trunc

variables {A : Type _} {B : Type _} {n : ℕ₋₂}

/- closure properties of truncatedness -/
@[hott] theorem is_trunc_is_embedding_closed (f : A → B) [Hf : is_embedding f] [HB : is_trunc n B]
  (Hn : -1 ≤ n) : is_trunc n A :=
begin
  unfreezeI; induction n with n,
    {apply empty.elim, exact not_succ_le_minus_two Hn},
    {apply is_trunc_succ_intro, intros a a',
        fapply @is_trunc_is_equiv_closed_rev _ _ n (ap f), resetI, apply_instance }
end

@[hott] theorem is_trunc_is_retraction_closed (f : A → B) [Hf : is_retraction f]
  (n : ℕ₋₂) [HA : is_trunc n A] : is_trunc n B :=
begin
  unfreezeI; induction n with n IH generalizing A B f Hf HA,
  { induction Hf with g ε, fapply is_contr.mk,
    { exactI f (center A) },
    { intro b, apply concat,
      { apply (ap f), exact (center_eq (g b)) },
      { apply ε }}},
  { induction Hf with g ε,
    apply is_trunc_succ_intro, intros b b',
    napply @IH (g b = g b') _ (λq, (ε b)⁻¹ ⬝ ap f q ⬝ ε b'),
    { apply (is_retraction.mk (ap g)),
      { intro p, induction p, dsimp [ap], apply con.left_inv }},
    { apply is_trunc_eq }}
end

@[hott] def is_embedding_to_fun (A B : Type _) : is_embedding (@to_fun A B)  :=
λf f', is_equiv_ap_to_fun _ _

/- theorems about trunctype -/
@[hott] protected def trunctype.sigma_char (n : ℕ₋₂) :
  (trunctype.{u} n) ≃ (Σ (A : Type u), is_trunc n A) :=
begin
  fapply equiv.MK,
  { intro A, exact (⟨carrier A, struct A⟩)},
  { intro S, exact (trunctype.mk S.1 S.2)},
  { intro S, induction S with S1 S2, refl },
  { intro A, induction A with A1 A2, refl },
end

@[hott] def trunctype_eq_equiv (n : ℕ₋₂) (A B : n-Type) :
  (A = B) ≃ (carrier A = carrier B) :=
calc
  (A = B) ≃ (to_fun (trunctype.sigma_char n) A = to_fun (trunctype.sigma_char n) B)
            : eq_equiv_fn_eq_of_equiv (trunctype.sigma_char n) A B
    ... ≃ ((to_fun (trunctype.sigma_char n) A).1 = (to_fun (trunctype.sigma_char n) B).1)
            : equiv.symm (equiv_subtype _ _)
    ... ≃ (carrier A = carrier B) : erfl

@[hott, instance] theorem is_trunc_trunctype (n : ℕ₋₂) : is_trunc n.+1 (n-Type) :=
begin
  apply is_trunc_succ_intro, intros X Y,
  fapply is_trunc_equiv_closed_rev _ (trunctype_eq_equiv _ _ _),
  fapply is_trunc_equiv_closed_rev _ (eq_equiv_equiv _ _),
  induction n,
  { napply is_contr_of_inhabited_prop,
    { apply is_trunc_equiv },
    { apply equiv_of_is_contr_of_is_contr }},
  { apply is_trunc_equiv }
end

/- univalence for truncated types -/
@[hott] def teq_equiv_equiv {n : ℕ₋₂} {A B : n-Type} : (A = B) ≃ (A ≃ B) :=
trunctype_eq_equiv n A B ⬝e eq_equiv_equiv A B

@[hott] def tua {n : ℕ₋₂} {A B : n-Type} (f : A ≃ B) : A = B :=
(trunctype_eq_equiv n A B)⁻¹ᶠ (ua f)

@[hott] def tua_refl {n : ℕ₋₂} (A : n-Type) : tua (@erfl A) = idp :=
begin
  refine ap (trunctype_eq_equiv n A A)⁻¹ᶠ (ua_refl A) ⬝ _,
  refine ap (eq_of_fn_eq_fn _) _ ⬝ eq_of_fn_eq_fn'_idp _ _,
  apply ap (dpair_eq_dpair idp) (is_prop.elim _ idpo),
  apply is_trunc.is_trunc_pathover
end

@[hott] def tua_trans {n : ℕ₋₂} {A B C : n-Type} (f : A ≃ B) (g : B ≃ C)
  : tua (f ⬝e g) = tua f ⬝ tua g :=
begin
  refine ap (trunctype_eq_equiv n A C)⁻¹ᶠ (ua_trans f g) ⬝ _,
  refine ap (eq_of_fn_eq_fn _) _ ⬝ eq_of_fn_eq_fn'_con _ _ _,
  refine _ ⬝ dpair_eq_dpair_con _ _ _ _,
  apply ap (dpair_eq_dpair _), apply is_prop.elim
end

@[hott] def tua_symm {n : ℕ₋₂} {A B : n-Type} (f : A ≃ B) : tua f⁻¹ᵉ = (tua f)⁻¹ :=
begin
  apply eq_inv_of_con_eq_idp',
  refine (tua_trans _ _)⁻¹ ⬝ _,
  refine ap tua _ ⬝ (tua_refl _),
  apply equiv_eq, exact to_right_inv f
end

@[hott] def tcast {n : ℕ₋₂} {A B : n-Type} (p : A = B) (a : A) : B :=
cast (ap trunctype.carrier p) a

@[hott] def ptcast {n : ℕ₋₂} {A B : n-Type*} (p : A = B) : ↑A →* ↑B :=
pcast (ap ptrunctype.to_pType p)

@[hott] theorem tcast_tua_fn {n : ℕ₋₂} {A B : n-Type} (f : A ≃ B) : tcast (tua f) = to_fun f :=
begin
  cases A with A HA, cases B with B HB, dsimp at f,
  hinduction f using rec_on_ua_idp,
  have : HA = HB, from is_prop.elim _ _, hinduction this,
  exact ap tcast (tua_refl _)
end

/- theorems about decidable equality and axiom K -/
@[hott] theorem is_set_of_axiom_K {A : Type _} (K : Π{a : A} (p : a = a), p = idp) : is_set A :=
is_set.mk _ (λa b p q, begin induction q, apply K end)

@[hott] theorem is_set_of_relation {A : Type u} (R : A → A → Type u)
  (mere : Π(a b : A), is_prop (R a b)) (refl : Π(a : A), R a a)
  (imp : Π{a b : A}, R a b → a = b) : is_set A :=
is_set_of_axiom_K
  (λa p,
    have H2 : transport (λx, R a x → a = x) p (@imp a a) = @imp a a, from apdt (@imp a) p,
    have H3 : Π(r : R a a), transport (λx, a = x) p (imp r)
                            = imp (transport (λx, R a x) p r), from
      to_fun ((heq_pi _ _ _)⁻¹ᵉ) H2,
    have H4 : imp (refl a) ⬝ p = imp (refl a), from
      calc
        imp (refl a) ⬝ p = transport (λx, a = x) p (imp (refl a)) : (eq_transport_r _ _)⁻¹
          ... = imp (transport (λx, R a x) p (refl a)) : H3 _
          ... = imp (refl a) : ap imp (is_prop.elim _ _),
    cancel_left (imp (refl a)) H4)

@[hott] def relation_equiv_eq {A : Type _} (R : A → A → Type _)
  (mere : Π(a b : A), is_prop (R a b)) (refl : Π(a : A), R a a)
  (imp : Π{a b : A}, R a b → a = b) (a b : A) : R a b ≃ a = b :=
have is_set A, from is_set_of_relation R mere refl @imp,
by exactI equiv_of_is_prop imp (λp, transport (R a) p (refl a))

local attribute [reducible] not
@[hott] theorem is_set_of_double_neg_elim {A : Type _} (H : Π(a b : A), ¬¬a = b → a = b)
  : is_set A :=
is_set_of_relation (λa b, ¬¬a = b) (by apply_instance) (λa n, n idp) H

section
open decidable
--this is proven differently in init.hedberg
@[hott] theorem is_set_of_decidable_eq (A : Type _) [H : decidable_eq A] : is_set A :=
is_set_of_double_neg_elim (λa b, decidable.by_contradiction)
end

@[hott] theorem is_trunc_of_axiom_K_of_le {A : Type _} {n : ℕ₋₂} (H : -1 ≤ n)
  (K : Π(a : A), is_trunc n (a = a)) : is_trunc (n.+1) A :=
@is_trunc_succ_intro _ _ (λa b, is_trunc_of_imp_is_trunc_of_le H
  begin intro p; induction p; apply K end)

@[hott] theorem is_trunc_succ_of_is_trunc_loop (Hn : -1 ≤ n) (Hp : Π(a : A), is_trunc n (a = a))
  : is_trunc (n.+1) A :=
begin
  apply is_trunc_succ_intro, intros a a',
  apply is_trunc_of_imp_is_trunc_of_le Hn, intro p,
  induction p, apply Hp
end

@[hott] theorem is_prop_iff_is_contr {A : Type _} (a : A) :
  is_prop A ↔ is_contr A :=
iff.intro (λH, by exactI is_contr.mk a (is_prop.elim a)) (by introI; apply_instance)

@[hott] theorem is_trunc_succ_iff_is_trunc_loop (A : Type _) (Hn : -1 ≤ n) :
  is_trunc (n.+1) A ↔ Π(a : A), is_trunc n (a = a) :=
iff.intro (by introI; apply_instance) (is_trunc_succ_of_is_trunc_loop Hn)

@[hott] theorem is_trunc_iff_is_contr_loopn_succ (n : ℕ) (A : Type _)
  : is_trunc n A ↔ Π(a : A), is_contr (Ω[n+1](pointed.Mk a)) :=
begin
  induction n with n IH generalizing A,
  { dsimp [loopn], transitivity _,
    { apply is_trunc_succ_iff_is_trunc_loop, apply le.refl },
    { apply pi_iff_pi, intro a, apply is_prop_iff_is_contr, refl }},
  { dsimp [loopn],
    transitivity _,
    { apply @is_trunc_succ_iff_is_trunc_loop @n, apply minus_one_le_succ },
    apply pi_iff_pi, intro a, transitivity _, apply IH,
    transitivity _, apply pi_iff_pi, intro p,
    rwr [@loopn_space_loop_irrel (pointed.MK A a) n p],
    exact ⟨λf, f idp, λH _, H⟩ }
end

@[hott] theorem is_trunc_iff_is_contr_loopn (n : ℕ) (A : Type _)
  : is_trunc (n.-2.+1) A ↔ (Π(a : A), is_contr (Ω[n](pointed.Mk a))) :=
begin
  induction n with n,
  { dsimp [sub_two,loopn], apply iff.intro,
      intros H a, exactI is_contr_of_inhabited_prop a,
      intro H, apply is_prop_of_imp_is_contr, exact H},
  { applyI is_trunc_iff_is_contr_loopn_succ },
end

-- rename to is_contr_loopn_of_is_trunc
@[hott] theorem is_contr_loop_of_is_trunc (n : ℕ) (A : Type*) [H : is_trunc (n.-2.+1) A] :
  is_contr (Ω[n] A) :=
begin
  unfreezeI; induction A,
  apply iff.mp (is_trunc_iff_is_contr_loopn _ _) H
end

-- rename to is_trunc_loopn_of_is_trunc
@[hott] theorem is_trunc_loop_of_is_trunc (n : ℕ₋₂) (k : ℕ) (A : Type*) [H : is_trunc n A] :
  is_trunc n (Ω[k] A) :=
begin
  induction k with k IH,
  { exact H },
  { applyI is_trunc_eq }
end

@[hott] def is_trunc_loopn (k : ℕ₋₂) (n : ℕ) (A : Type*) [H : is_trunc (k+n) A]
  : is_trunc k (Ω[n] A) :=
begin
  unfreezeI; induction n with n IH generalizing k H, exact H,
  napply is_trunc_eq, napply IH, rwr [succ_add_nat], rwr [add_nat_succ] at H, exact H
end

@[hott] def is_set_loopn (n : ℕ) (A : Type*) [is_trunc n A] : is_set (Ω[n] A) :=
have is_trunc (0 + ↑n) A, by rwr [trunc_index.zero_add]; apply_instance,
by exactI is_trunc_loopn 0 n A

@[hott] def pequiv_punit_of_is_contr (A : Type*) (H : is_contr A) : A ≃* unit*.to_pType :=
pequiv_of_equiv (equiv_unit_of_is_contr A) (@is_prop.elim unit _ _ _)

@[hott] def pequiv_punit_of_is_contr' (A : Type _) (H : is_contr A)
  : pointed.MK A (center A) ≃* unit*.to_pType :=
pequiv_punit_of_is_contr (pointed.MK A (center A)) H

@[hott] def is_trunc_is_contr_fiber (n : ℕ₋₂) {A B : Type _} (f : A → B)
  (b : B) [is_trunc n A] [is_trunc n B] : is_trunc n (is_contr (fiber f b)) :=
begin
  unfreezeI; cases n,
  { applyI is_contr_of_inhabited_prop, napply is_contr_fun_of_is_equiv,
    apply is_equiv_of_is_contr },
  { applyI is_trunc_succ_of_is_prop }
end

end is_trunc open is_trunc

namespace trunc
variables {n : ℕ₋₂} {A : Type u} {B : Type _} {a₁ a₂ a₃ a₄ : A}

@[hott] def trunc_functor2 {n : ℕ₋₂} {A B C : Type _} (f : A → B → C)
  (x : trunc n A) (y : trunc n B) : trunc n C :=
by hinduction x with a; hinduction y with b; exact tr (f a b)

@[hott] def tconcat (p : trunc n (a₁ = a₂)) (q : trunc n (a₂ = a₃)) :
  trunc n (a₁ = a₃) :=
trunc_functor2 concat p q

@[hott] def tinverse (p : trunc n (a₁ = a₂)) : trunc n (a₂ = a₁) :=
trunc_functor _ inverse p

@[hott, reducible] def tidp : trunc n (a₁ = a₁) :=
tr idp

@[hott] def tassoc (p : trunc n (a₁ = a₂)) (q : trunc n (a₂ = a₃))
  (r : trunc n (a₃ = a₄)) : tconcat (tconcat p q) r = tconcat p (tconcat q r) :=
by hinduction p; hinduction q; hinduction r; exact ap tr (con.assoc _ _ _)

@[hott] def tidp_tcon (p : trunc n (a₁ = a₂)) : tconcat tidp p = p :=
by hinduction p; exact ap tr (idp_con _)

@[hott] def tcon_tidp (p : trunc n (a₁ = a₂)) : tconcat p tidp = p :=
by hinduction p; refl

@[hott] def left_tinv (p : trunc n (a₁ = a₂)) : tconcat (tinverse p) p = tidp :=
by hinduction p; exact ap tr (con.left_inv _)

@[hott] def right_tinv (p : trunc n (a₁ = a₂)) : tconcat p (tinverse p) = tidp :=
by hinduction p; exact ap tr (con.right_inv _)

@[hott] def tap (f : A → B) (p : trunc n (a₁ = a₂)) : trunc n (f a₁ = f a₂) :=
trunc_functor _ (ap f) p

@[hott] def tap_tidp (f : A → B) : tap f (@tidp n A a₁) = tidp := idp
@[hott] def tap_tcon (f : A → B) (p : trunc n (a₁ = a₂)) (q : trunc n (a₂ = a₃)) :
  tap f (tconcat p q) = tconcat (tap f p) (tap f q) :=
by hinduction p; hinduction q; exact ap tr (ap_con _ _ _)

/- characterization of equality in truncated types -/
@[hott] protected def code (n : ℕ₋₂) (aa aa' : trunc n.+1 A) : trunctype.{u} n :=
by hinduction aa with a; hinduction aa' with a'; exact trunctype.mk' n (trunc n (a = a'))

@[hott] protected def encode {n : ℕ₋₂} {aa aa' : trunc n.+1 A}
  : aa = aa' → trunc.code n aa aa' :=
begin
  intro p, induction p, hinduction aa with a, exact tr idp
end

@[hott] protected def decode {n : ℕ₋₂} (aa aa' : trunc n.+1 A) :
  trunc.code n aa aa' → aa = aa' :=
begin
  hinduction aa' with a', hinduction aa with a,
  dsimp [trunc.code, trunc.rec_on], intro x,
  hinduction x with p, exact ap tr p,
end

@[hott] def trunc_eq_equiv (n : ℕ₋₂) (aa aa' : trunc n.+1 A)
  : aa = aa' ≃ trunc.code n aa aa' :=
begin
  fapply equiv.MK,
  { apply trunc.encode},
  { apply trunc.decode},
  { hinduction aa', hinduction aa, intro x,
    hinduction x with p,
      induction p, refl },
  { intro p, hinduction p, hinduction aa, refl },
end

@[hott] def tr_eq_tr_equiv (n : ℕ₋₂) (a a' : A)
  : (tr a = tr a' :> trunc n.+1 A) ≃ trunc n (a = a') :=
trunc_eq_equiv _ _ _

@[hott] def trunc_eq {n : ℕ₋₂} {a a' : A} (p : trunc n (a = a')) :tr a = tr a' :> trunc n.+1 A :=
(tr_eq_tr_equiv _ _ _)⁻¹ᵉ.to_fun p

@[hott] def code_mul {n : ℕ₋₂} {aa₁ aa₂ aa₃ : trunc n.+1 A}
  (g : trunc.code n aa₁ aa₂) (h : trunc.code n aa₂ aa₃) : trunc.code n aa₁ aa₃ :=
begin
  hinduction aa₁ with a₁, hinduction aa₂ with a₂, hinduction aa₃ with a₃,
  apply tconcat g h,
end

/- encode preserves concatenation -/
@[hott] def encode_con' {n : ℕ₋₂} {aa₁ aa₂ aa₃ : trunc n.+1 A} (p : aa₁ = aa₂) (q : aa₂ = aa₃)
  : trunc.encode (p ⬝ q) = code_mul (trunc.encode p) (trunc.encode q) :=
begin
  induction p, induction q, hinduction aa₁ with a₁, refl
end

@[hott] def encode_con {n : ℕ₋₂} {a₁ a₂ a₃ : A} (p : tr a₁ = tr a₂ :> trunc (n.+1) A)
  (q : tr a₂ = tr a₃ :> trunc (n.+1) A)
  : trunc.encode (p ⬝ q) = tconcat (trunc.encode p) (trunc.encode q) :=
encode_con' p q

/- the principle of unique choice -/
@[hott] def unique_choice {P : A → Type _} [H : Πa, is_prop (P a)] (f : Πa, ∥ P a ∥) (a : A)
  : P a :=
(trunc_equiv _ _).to_fun (f a)

/- transport over a truncated family -/
@[hott] def trunc_transport {a a' : A} {P : A → Type _} (p : a = a') (n : ℕ₋₂) (x : P a)
  : transport (λa, trunc n (P a)) p (tr x) = tr (p ▸ x) :=
by induction p; refl

/- pathover over a truncated family -/
@[hott] def trunc_pathover {A : Type _} {B : A → Type _} {n : ℕ₋₂} {a a' : A} {p : a = a'}
  {b : B a} {b' : B a'} (q : b =[p] b') : @tr n _ b =[p; λa, trunc n (B a)] @tr n _ b' :=
by induction q; constructor

/- truncations preserve truncatedness -/
@[hott, instance, priority 500] def is_trunc_trunc_of_is_trunc (A : Type _)
  (n m : ℕ₋₂) [H : is_trunc n A] : is_trunc n (trunc m A) :=
begin
  unfreezeI; induction n with n IH generalizing A m H,
  { napply is_contr_equiv_closed,
    { symmetry, napply trunc_equiv, applyI (@is_trunc_of_le _ -2), apply minus_two_le},
    apply_instance },
  { induction m with m,
    { apply (@is_trunc_of_le _ -2), apply minus_two_le},
    { apply is_trunc_succ_intro, intros aa aa',
      hinduction aa, hinduction aa',
      apply is_trunc_equiv_closed_rev,
      { apply tr_eq_tr_equiv },
      { apply IH }}}
end

/- equivalences between truncated types (see also hit.trunc) -/
@[hott] def trunc_trunc_equiv_left (A : Type _) {n m : ℕ₋₂} (H : n ≤ m)
  : trunc n (trunc m A) ≃ trunc n A :=
begin
  haveI H2 := is_trunc_of_le (trunc n A) H,
  fapply equiv.MK,
  { intro x, hinduction x with x, hinduction x with x, exact tr x },
  { intro x, hinduction x with x, exact tr (tr x) },
  { intro x, hinduction x with x, refl },
  { intro x, hinduction x with x, hinduction x with x, refl }
end

@[hott] def trunc_trunc_equiv_right (A : Type _) {n m : ℕ₋₂} (H : n ≤ m)
  : trunc m (trunc n A) ≃ trunc n A :=
begin
  napply trunc_equiv,
  exact is_trunc_of_le _ H,
end

@[hott] def trunc_equiv_trunc_of_le {n m : ℕ₋₂} {A B : Type _} (H : n ≤ m)
  (f : trunc m A ≃ trunc m B) : trunc n A ≃ trunc n B :=
(trunc_trunc_equiv_left A H)⁻¹ᵉ ⬝e trunc_equiv_trunc n f ⬝e trunc_trunc_equiv_left B H

@[hott] def trunc_trunc_equiv_trunc_trunc (n m : ℕ₋₂) (A : Type _)
  : trunc n (trunc m A) ≃ trunc m (trunc n A) :=
begin
  fapply equiv.MK; intro x,
  { hinduction x with x, hinduction x with x, exact tr (tr x) },
  { hinduction x with x, hinduction x with x, exact tr (tr x) },
  { hinduction x with x, hinduction x with x, refl },
  { hinduction x with x, hinduction x with x, refl }
end

@[hott] theorem is_trunc_trunc_of_le (A : Type _)
  (n : ℕ₋₂) {m k : ℕ₋₂} (H : m ≤ k) [is_trunc n (trunc k A)] : is_trunc n (trunc m A) :=
begin
  apply is_trunc_equiv_closed,
  { apply trunc_trunc_equiv_left, exact H },
  apply_instance
end

@[hott] def trunc_functor_homotopy {X Y : Type _} (n : ℕ₋₂) {f g : X → Y}
  (p : f ~ g) (x : trunc n X) : trunc_functor n f x = trunc_functor n g x :=
begin
  hinduction x with x, exact ap tr (p x)
end

@[hott] def trunc_functor_homotopy_of_le {n k : ℕ₋₂} {A B : Type _} (f : A → B) (H : n ≤ k) :
  to_fun (trunc_trunc_equiv_left B H) ∘
  trunc_functor n (trunc_functor k f) ∘
  to_fun (trunc_trunc_equiv_left A H)⁻¹ᵉ ~
    trunc_functor n f :=
begin
  intro x, hinduction x with x, refl
end

@[hott] def is_equiv_trunc_functor_of_le {n k : ℕ₋₂} {A B : Type _} (f : A → B) (H : n ≤ k)
  [Hf : is_equiv (trunc_functor k f)] : is_equiv (trunc_functor n f) :=
is_equiv_of_equiv_of_homotopy (trunc_equiv_trunc_of_le H (equiv.mk (trunc_functor k f) Hf))
                              (trunc_functor_homotopy_of_le f H)

/- trunc_functor preserves surjectivity -/

--set_option trace.hinduction true
@[hott] def is_surjective_trunc_functor {A B : Type _} (n : ℕ₋₂) (f : A → B) [H : is_surjective f]
  : is_surjective (trunc_functor n f) :=
begin
  cases n with n; intro b,
  { exact tr (fiber.mk (center _) (is_prop.elim _ _)) },
  { haveI : Πb, is_trunc n.+1 (image (trunc_functor n.+1 f) b),
    { intro b, exact is_trunc_of_le _ (minus_one_le_succ _) },
    unfreezeI; hinduction b with b,
    hinduction H b with x p, induction p with a p,
    exact tr (fiber.mk (tr a) (ap tr p)) }
end

/- truncation of pointed types -/
@[hott] def ptrunc (n : ℕ₋₂) (X : Type*) : Type* :=
⟨trunc n X, tr pt⟩

@[hott] instance is_trunc_ptrunc (n : ℕ₋₂) (X : Type*) : is_trunc n (ptrunc n X) :=
is_trunc_trunc n X

@[hott] def pttrunc (n : ℕ₋₂) (X : Type*) : n-Type* :=
ptrunctype.mk (trunc n X) (is_trunc_trunc n X) (tr pt)

/- pointed maps involving ptrunc -/
@[hott] def ptrunc_functor {X Y : Type*} (n : ℕ₋₂) (f : X →* Y)
  : ptrunc n X →* ptrunc n Y :=
pmap.mk (trunc_functor n f) (ap tr (respect_pt f))

@[hott] def ptr (n : ℕ₋₂) (A : Type*) : A →* ptrunc n A :=
pmap.mk tr idp

@[hott] def puntrunc (n : ℕ₋₂) (A : Type*) [is_trunc n A] : ptrunc n A →* A :=
pmap.mk untrunc_of_is_trunc idp

@[hott] def ptrunc.elim (n : ℕ₋₂) {X Y : Type*} [is_trunc n Y] (f : X →* Y) :
  ptrunc n X →* Y :=
pmap.mk (trunc.elim f) (respect_pt f)

/- pointed equivalences involving ptrunc -/
@[hott] def ptrunc_pequiv_ptrunc (n : ℕ₋₂) {X Y : Type*} (H : X ≃* Y)
  : ptrunc n X ≃* ptrunc n Y :=
pequiv_of_equiv (trunc_equiv_trunc n (equiv_of_pequiv H)) (ap tr (respect_pt H.to_pmap))

@[hott] def ptrunc_pequiv (n : ℕ₋₂) (X : Type*) [H : is_trunc n X]
  : ptrunc n X ≃* X :=
pequiv_of_equiv (trunc_equiv n X) idp

@[hott] def ptrunc_ptrunc_pequiv_left (A : Type*) {n m : ℕ₋₂} (H : n ≤ m)
  : ptrunc n (ptrunc m A) ≃* ptrunc n A :=
pequiv_of_equiv (trunc_trunc_equiv_left A H) idp

@[hott] def ptrunc_ptrunc_pequiv_right (A : Type*) {n m : ℕ₋₂} (H : n ≤ m)
  : ptrunc m (ptrunc n A) ≃* ptrunc n A :=
pequiv_of_equiv (trunc_trunc_equiv_right A H) idp

@[hott] def ptrunc_pequiv_ptrunc_of_le {n m : ℕ₋₂} {A B : Type*} (H : n ≤ m)
  (f : ptrunc m A ≃* ptrunc m B) : ptrunc n A ≃* ptrunc n B :=
(ptrunc_ptrunc_pequiv_left A H)⁻¹ᵉ* ⬝e*
ptrunc_pequiv_ptrunc n f ⬝e*
ptrunc_ptrunc_pequiv_left B H

@[hott] def ptrunc_ptrunc_pequiv_ptrunc_ptrunc (n m : ℕ₋₂) (A : Type*)
  : ptrunc n (ptrunc m A) ≃* ptrunc m (ptrunc n A) :=
pequiv_of_equiv (trunc_trunc_equiv_trunc_trunc n m A) idp

@[hott] def loop_ptrunc_pequiv (n : ℕ₋₂) (A : Type*) :
  Ω (ptrunc (n+1) A) ≃* ptrunc n (Ω A) :=
pequiv_of_equiv (tr_eq_tr_equiv _ _ _) idp

@[hott] def loop_ptrunc_pequiv_con {n : ℕ₋₂} {A : Type*} (p q : Ω (ptrunc (n+1) A)) :
  (loop_ptrunc_pequiv n A).to_pmap (p ⬝ q) =
    tconcat ((loop_ptrunc_pequiv n A).to_pmap p) ((loop_ptrunc_pequiv n A).to_pmap q) :=
encode_con p q

@[hott] def loopn_ptrunc_pequiv (n : ℕ₋₂) (k : ℕ) (A : Type*) :
  Ω[k] (ptrunc (n+k) A) ≃* ptrunc n (Ω[k] A) :=
begin
  induction k with k IH generalizing n,
  { refl },
  { refine _ ⬝e* loop_ptrunc_pequiv n (Ω[k] A),
    change Ω (Ω[k] (ptrunc (n + succ k) A)) ≃* Ω (ptrunc (n + 1) (Ω[k] A)),
    apply loop_pequiv_loop,
    refine _ ⬝e* IH (n.+1),
    exact loopn_pequiv_loopn k (pequiv_of_eq (ap (λn, ptrunc n A) (succ_add_nat _ _)⁻¹ᵖ)) }
end

@[hott] def loopn_ptrunc_pequiv_con {n : ℕ₋₂} {k : ℕ} {A : Type*}
  (p q : Ω[succ k] (ptrunc (n+nat.succ k) A)) :
  (loopn_ptrunc_pequiv n (succ k) A).to_pmap (p ⬝ q) =
  tconcat ((loopn_ptrunc_pequiv n (succ k) A).to_pmap p)
          ((loopn_ptrunc_pequiv n (succ k) A).to_pmap q)  :=
begin
  refine _ ⬝ loop_ptrunc_pequiv_con _ _,
  exact ap (loop_ptrunc_pequiv _ _).to_fun (loop_pequiv_loop_con _ _ _)
end

@[hott] def loopn_ptrunc_pequiv_inv_con {n : ℕ₋₂} {k : ℕ} {A : Type*}
  (p q : ptrunc n (Ω[succ k] A)) :
  (loopn_ptrunc_pequiv n (succ k) A)⁻¹ᵉ*.to_fun (tconcat p q) =
  (loopn_ptrunc_pequiv n (succ k) A)⁻¹ᵉ*.to_fun p ⬝
  (loopn_ptrunc_pequiv n (succ k) A)⁻¹ᵉ*.to_fun q :=
equiv.inv_preserve_binary (loopn_ptrunc_pequiv n (succ k) A).to_equiv concat tconcat
  (@loopn_ptrunc_pequiv_con n k A) p q

/- pointed homotopies involving ptrunc -/
@[hott] def ptrunc_functor_pcompose {X Y Z : Type*} (n : ℕ₋₂) (g : Y →* Z)
  (f : X →* Y) : ptrunc_functor n (g ∘* f) ~* ptrunc_functor n g ∘* ptrunc_functor n f :=
begin
  fapply phomotopy.mk,
  { exact trunc_functor_compose n g f },
  { refine idp_con _ ⬝ _, refine whisker_right _ (ap_compose' _ _ _) ⬝ _,
    refine whisker_right _ (ap_compose tr g _) ⬝ _, exact (ap_con _ _ _)⁻¹ },
end

@[hott] def ptrunc_functor_pid (X : Type*) (n : ℕ₋₂) :
  ptrunc_functor n (pid X) ~* pid (ptrunc n X) :=
begin
  fapply phomotopy.mk,
  { apply trunc_functor_id},
  { refl },
end

@[hott] def ptrunc_functor_pcast {X Y : Type*} (n : ℕ₋₂) (p : X = Y) :
  ptrunc_functor n (pcast p) ~* pcast (ap (ptrunc n) p) :=
begin
  fapply phomotopy.mk,
  { intro x, refine trunc_functor_cast _ _ _ ⬝ _,
    refine ap010 (@hott.eq.cast (ptrunc n X) (@ptrunc n Y)) _ x,
    refine ap_compose' _ _ _ ⬝ _ ⬝ ap_compose _ _ _, refl },
  { induction p, refl },
end

@[hott] def ptrunc_functor_phomotopy {X Y : Type*} (n : ℕ₋₂) {f g : X →* Y}
  (p : f ~* g) : ptrunc_functor n f ~* ptrunc_functor n g :=
begin
  fapply phomotopy.mk,
  { exact trunc_functor_homotopy n p},
  { refine (ap_con _ _ _)⁻¹ ⬝ _, exact ap02 tr (to_homotopy_pt p)},
end

@[hott] def pcast_ptrunc (n : ℕ₋₂) {A B : Type*} (p : A = B) :
  pcast (ap (ptrunc n) p) ~* ptrunc_functor n (pcast p) :=
begin
  fapply phomotopy.mk,
  { intro a, induction p, exact (trunc_functor_id _ _ _)⁻¹ },
  { induction p, refl }
end

@[hott] def ptrunc_elim_ptr (n : ℕ₋₂) {X Y : Type*} [is_trunc n Y] (f : X →* Y) :
  ptrunc.elim n f ∘* ptr n X ~* f :=
begin
  fapply phomotopy.mk,
  { refl },
  { refl }
end

@[hott] def ptrunc_elim_phomotopy (n : ℕ₋₂) {X Y : Type*} [is_trunc n Y] {f g : X →* Y}
  (H : f ~* g) : ptrunc.elim n f ~* ptrunc.elim n g :=
begin
  fapply phomotopy.mk,
  { intro x, hinduction x with x, exact H x },
  { exact to_homotopy_pt H }
end

@[hott] def ap1_ptrunc_functor (n : ℕ₋₂) {A B : Type*} (f : A →* B) :
  Ω→ (ptrunc_functor (n.+1) f) ∘* (loop_ptrunc_pequiv n A)⁻¹ᵉ*.to_pmap ~*
  (loop_ptrunc_pequiv n B)⁻¹ᵉ*.to_pmap ∘* ptrunc_functor n (Ω→ f) :=
begin
  fapply phomotopy.mk,
  { intro p, hinduction p with p,
    refine ((ap_inv _ _)⁻¹ ◾ (ap_compose _ _ _)⁻¹ ◾ idp) ⬝ _ ⬝ (ap_con _ _ _)⁻¹ᵖ,
    apply whisker_right, refine _ ⬝ (ap_con _ _ _)⁻¹ᵖ,
    exact whisker_left _ (ap_compose' _ _ _)⁻¹ᵖ },
  { induction B with B b, induction f with f p, dsimp at f, dsimp at p, hinduction p, refl }
end

@[hott] def ap1_ptrunc_elim (n : ℕ₋₂) {A B : Type*} (f : A →* B) [is_trunc (n.+1) B] :
  Ω→ (ptrunc.elim (n.+1) f) ∘* (loop_ptrunc_pequiv n A)⁻¹ᵉ*.to_pmap ~*
  ptrunc.elim n (Ω→ f) :=
begin
  fapply phomotopy.mk,
  { intro p, hinduction p with p, exact idp ◾ (ap_compose _ _ _)⁻¹ ◾ idp },
  { refl }
end

@[hott] def ap1_ptr (n : ℕ₋₂) (A : Type*) :
  Ω→ (ptr (n.+1) A) ~* (loop_ptrunc_pequiv n A)⁻¹ᵉ*.to_pmap ∘* ptr n (Ω A) :=
begin
  fapply phomotopy.mk,
  { intro p, apply idp_con },
  { refl }
end

@[hott] def ptrunc_elim_ptrunc_functor (n : ℕ₋₂) {A B C : Type*} (g : B →* C) (f : A →* B)
  [is_trunc n C] :
  ptrunc.elim n g ∘* ptrunc_functor n f ~* ptrunc.elim n (g ∘* f) :=
begin
  fapply phomotopy.mk,
  { intro x, hinduction x with a, refl },
  { refine idp_con _ ⬝ whisker_right _ (ap_compose' _ _ _)⁻¹ᵖ },
end

end trunc open trunc

/- The truncated encode-decode method -/
namespace eq

@[hott] def truncated_encode {k : ℕ₋₂} {A : Type _} {a₀ a : A} {code : A → Type _}
  [Πa, is_trunc k (code a)] (c₀ : code a₀) (p : trunc k (a₀ = a)) : code a :=
begin
  hinduction p with p,
  exact transport code p c₀
end

@[hott] def truncated_encode_decode_method {k : ℕ₋₂} {A : Type _} (a₀ a : A) (code : A → Type _)
  [Πa, is_trunc k (code a)] (c₀ : code a₀)
  (decode : Π(a : A) (c : code a), trunc k (a₀ = a))
  (encode_decode : Π(a : A) (c : code a), truncated_encode c₀ (decode a c) = c)
  (decode_encode : decode a₀ c₀ = tr idp) : trunc k (a₀ = a) ≃ code a :=
begin
  fapply equiv.MK,
  { exact truncated_encode c₀},
  { apply decode},
  { intro c, apply encode_decode},
  { intro p, hinduction p with p, induction p, exact decode_encode},
end

end eq


/- some consequences for properties about functions (surjectivity etc.) -/
namespace function
variables {A : Type _} {B : Type _}
@[hott, instance] def is_surjective_of_is_equiv (f : A → B) [H : is_equiv f] : is_surjective f :=
λb, begin dsimp [image, image'], apply center end

@[hott] def is_equiv_equiv_is_embedding_times_is_surjective (f : A → B)
  : is_equiv f ≃ (is_embedding f × is_surjective f) :=
equiv_of_is_prop
  (λH, (by resetI; apply_instance, by resetI; apply_instance))
  (λP, prod.rec_on P (λH₁ H₂, by exactI is_equiv_of_is_surjective_of_is_embedding _))

/-
  @[hott] theorem 8.8.1:
  A function is an equivalence if it's an embedding and it's action on sets is an surjection
-/
@[hott] def is_equiv_of_is_surjective_trunc_of_is_embedding {A B : Type _} (f : A → B)
  [H : is_embedding f] [H' : is_surjective (trunc_functor 0 f)] : is_equiv f :=
have is_surjective f,
begin
  intro b,
  hinduction H' (tr b) with x p, hinduction p with a p,
  hinduction a with a, dsimp [trunc_functor] at p,
  hinduction ((tr_eq_tr_equiv _ _ _).to_fun p) with x q,
  exact image.mk a q
end,
by exactI is_equiv_of_is_surjective_of_is_embedding f

/-
  Corollary 8.8.2:
  A function f is an equivalence if Ωf and trunc_functor 0 f are equivalences
-/
@[hott] def is_equiv_of_is_equiv_ap1_of_is_equiv_trunc {A B : Type _} (f : A → B)
  [H : Πa, is_equiv (ap1 (pmap_of_map f a))] [H' : is_equiv (trunc_functor 0 f)] :
  is_equiv f :=
have is_embedding f,
begin
  intros a a',
  apply is_equiv_of_imp_is_equiv,
  intro p,
  have q := ap (@tr 0 _) p,
  have r := @eq_of_fn_eq_fn' _ _ (trunc_functor 0 f) _ (tr a) (tr a') q,
  hinduction (tr_eq_tr_equiv _ _ _).to_fun r with x s,
  induction s,
  apply is_equiv.homotopy_closed (ap1 (pmap_of_map f a)),
  intro p, apply idp_con
end,
by exactI is_equiv_of_is_surjective_trunc_of_is_embedding f

-- Whitehead's principle itself is in homotopy.homotopy_group, since it needs the @[hott] def of
-- a homotopy group.

end function
end hott