/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Floris van Doorn

Theorems about the natural numbers specific to HoTT
-/
import .order ..pointed .sub
universes u v w
hott_theory
namespace hott

open nat is_trunc hott.algebra hott.is_equiv hott.equiv

namespace nat
  @[hott, instance] def is_prop_le (n m : ℕ) : is_prop (n ≤ m) :=
  begin
    have lem : Π{n m : ℕ} (p : n ≤ m) (q : n = m), p = nat.le_of_eq q,
    begin
      intros, cases p with m p IH,
      { have H' : q = idp, by apply is_set.elim,
        cases H', reflexivity },
      { cases q, apply empty.elim, apply not_succ_le_self p }
    end,
    apply is_prop.mk, intros H1 H2, induction H2 with m H2 IH,
    { exact lem H1 idp },
    { cases H1,
      { apply empty.elim, apply not_succ_le_self H2},
      { exact ap le.step (IH _)}},
  end

  @[hott, instance] def is_prop_lt (n m : ℕ) : is_prop (n < m) := is_prop_le _ _

  @[hott] def le_equiv_succ_le_succ (n m : ℕ) : (n ≤ m) ≃ (succ n ≤ succ m) :=
  equiv_of_is_prop succ_le_succ le_of_succ_le_succ
  @[hott] theorem le_succ_equiv_pred_le (n m : ℕ) : (n ≤ succ m) ≃ (pred n ≤ m) :=
  equiv_of_is_prop pred_le_pred le_succ_of_pred_le

  @[hott] theorem lt_by_cases_lt {a b : ℕ} {P : Type _} (H1 : a < b → P) (H2 : a = b → P)
    (H3 : a > b → P) (H : a < b) : lt.by_cases H1 H2 H3 = H1 H :=
  begin
     dsimp [lt.by_cases], hinduction (lt.trichotomy a b) with p H' H',
     { exact ap H1 (is_prop.elim _ _)},
     { apply empty.elim, cases H' with H' H', apply lt.irrefl b, exact H' ▸ H,
       exact lt.asymm H H'}
  end

  @[hott] theorem lt_by_cases_eq {a b : ℕ} {P : Type _} (H1 : a < b → P) (H2 : a = b → P)
    (H3 : a > b → P) (H : a = b) : lt.by_cases H1 H2 H3 = H2 H :=
  begin
    dsimp [lt.by_cases], induction (lt.trichotomy a b) with H' H',
    { apply empty.elim, apply lt.irrefl b, exact H ▸ H'},
    { cases H' with H' H', exact ap H2 (is_prop.elim _ _), apply empty.elim , apply lt.irrefl b,
      exact H ▸ H'}
  end

  @[hott] theorem lt_by_cases_ge {a b : ℕ} {P : Type _} (H1 : a < b → P) (H2 : a = b → P)
    (H3 : a > b → P) (H : a > b) : lt.by_cases H1 H2 H3 = H3 H :=
  begin
    dsimp [lt.by_cases], induction (lt.trichotomy a b) with H' H',
    { apply empty.elim, exact lt.asymm H H'},
    { cases H' with H' H', apply empty.elim, apply lt.irrefl b, exact H' ▸ H,
      exact ap H3 (is_prop.elim _ _)}
  end

  @[hott] theorem lt_ge_by_cases_lt {n m : ℕ} {P : Type _} (H1 : n < m → P) (H2 : n ≥ m → P)
    (H : n < m) : lt_ge_by_cases H1 H2 = H1 H :=
  by apply lt_by_cases_lt

  @[hott] theorem lt_ge_by_cases_ge {n m : ℕ} {P : Type _} (H1 : n < m → P) (H2 : n ≥ m → P)
    (H : n ≥ m) : lt_ge_by_cases H1 H2 = H2 H :=
  begin
    dsimp [lt_ge_by_cases,lt.by_cases], induction (lt.trichotomy n m) with H' H',
    { apply empty.elim, apply lt.irrefl m, exact lt_of_le_of_lt H H'},
    { cases H' with H' H'; apply ap H2 (is_prop.elim _ _)}
  end

  @[hott] theorem lt_ge_by_cases_le {n m : ℕ} {P : Type _} {H1 : n ≤ m → P} {H2 : n ≥ m → P}
    (H : n ≤ m) (Heq : Π(p : n = m), H1 (le_of_eq p) = H2 (le_of_eq p⁻¹))
    : lt_ge_by_cases (λH', H1 (le_of_lt H')) H2 = H1 H :=
  begin
    dsimp [lt_ge_by_cases,lt.by_cases], induction (lt.trichotomy n m) with H' H',
    { apply ap H1 (is_prop.elim _ _)},
    { cases H' with H' H',
      { induction H', symmetry,
        exact ap H1 (is_prop.elim _ _) ⬝ Heq idp ⬝ ap H2 (is_prop.elim _ _)},
      { apply empty.elim, apply lt.irrefl n, apply lt_of_le_of_lt H H'}}
  end

  @[hott] def nat_eq_equiv (n m : ℕ) : (n = m) ≃ nat.code n m :=
  equiv.MK nat.encode
           (nat.decode n m)
           begin
             revert m, induction n; intro m; induction m; intro c,
               induction c, reflexivity,
               exact empty.elim c,
               exact empty.elim c,
               dsimp [nat.decode, nat.encode], rwr [←tr_compose], apply n_ih
           end
           begin
             intro p, induction p, induction n,
               reflexivity,
               exact ap02 succ n_ih
           end

  @[hott, instance] def pointed_nat : pointed ℕ :=
  pointed.mk 0

  open sigma sum
  @[hott] def eq_even_or_eq_odd (n : ℕ) : (Σk, 2 * k = n) ⊎ (Σk, 2 * k + 1 = n) :=
  begin
    induction n with n IH,
    { exact inl ⟨0, idp⟩},
    { induction IH with H H; induction H with k p; induction p,
      { exact inr ⟨k, idp⟩},
      { refine inl ⟨k+1, idp⟩}}
  end

  @[hott] def rec_on_even_odd {P : ℕ → Type _} (n : ℕ) (H : Πk, P (2 * k)) (H2 : Πk, P (2 * k + 1))
    : P n :=
  begin
    cases eq_even_or_eq_odd n with v v; induction v with k p; induction p,
    { exact H k},
    { exact H2 k}
  end

  /- this inequality comes up a couple of times when using the freudenthal suspension @[hott] theorem -/
  @[hott] theorem add_mul_le_mul_add (n m k : ℕ) : n + (succ m) * k ≤ (succ m) * (n + k) :=
  calc
    n + (succ m) * k ≤ (m * n + n) + (succ m) * k : add_le_add_right (le_add_left _ _) _
      ... = (succ m) * n + (succ m) * k : by rwr ←succ_mul
      ... = (succ m) * (n + k) : by rwr ←hott.algebra.left_distrib

  /-
    Some operations work only for successors. For example fin (succ n) has a 0 and a 1, but fin 0
    doesn't. However, we want a bit more, because sometimes we want a zero of (fin a)
    where a is either
    - equal to a successor, but not definitionally a successor (e.g. (0 : fin (3 + n)))
    - definitionally equal to a successor, but not in a way that type class inference can infer.
      (e.g. (0 : fin 4). Note that 4 is bit0 (bit0 one), but (bit0 x) (defined as x + x),
        is not always a successor)
    To solve this we use an auxillary class `is_succ` which can solve whether a number is a
    successor.
  -/

  @[hott, class] inductive is_succ : ℕ → Type
  | mk : Π(n : ℕ), is_succ (succ n)

  attribute [instance] is_succ.mk

  @[hott, instance] def is_succ_1 : is_succ 1 := is_succ.mk 0

  @[hott, instance] def is_succ_add_right (n m : ℕ) [H : is_succ m] : is_succ (n+m) :=
  by unfreezeI; induction H with m; constructor

  @[hott, instance, priority 900] def is_succ_add_left (n m : ℕ) [H : is_succ n] :
    is_succ (n+m) :=
  by unfreezeI; induction H with n; cases m with m; constructor

  @[hott] def is_succ_bit0 (n : ℕ) [H : is_succ n] : is_succ (bit0 n) :=
  by dsimp [bit0]; apply_instance

  -- level 2 is useful for abelian homotopy groups, which only exist at level 2 and higher
  @[hott, class] inductive is_at_least_two : ℕ → Type
  | mk : Π(n : ℕ), is_at_least_two (succ (succ n))

  attribute [instance] is_at_least_two.mk

  @[hott, instance] def is_at_least_two_succ (n : ℕ) [H : is_succ n] :
    is_at_least_two (succ n) :=
  by unfreezeI; induction H with n; constructor

  @[hott, instance] def is_at_least_two_add_right (n m : ℕ) [H : is_at_least_two m] :
    is_at_least_two (n+m) :=
  by unfreezeI; induction H with m; constructor

  @[hott, instance] def is_at_least_two_add_left (n m : ℕ) [H : is_at_least_two n] :
    is_at_least_two (n+m) :=
  by unfreezeI; induction H with n; cases m with m; try { cases m with m }; constructor

  @[hott, instance, priority 900] def is_at_least_two_add_both (n m : ℕ)
    [H : is_succ n] [K : is_succ m] : is_at_least_two (n+m) :=
  by unfreezeI; induction H with n; induction K with m; cases m with m; constructor

  @[hott] def is_at_least_two_bit0 (n : ℕ) [H : is_succ n] : is_at_least_two (bit0 n) :=
  by dsimp [bit0]; apply_instance

  @[hott] def is_at_least_two_bit1 (n : ℕ) [H : is_succ n] : is_at_least_two (bit1 n) :=
  by dsimp [bit1, bit0]; apply_instance

  /- some facts about iterate -/

  @[hott] def iterate_succ {A : Type _} (f : A → A) (n : ℕ) (x : A) :
    f^[succ n] x = f^[n] (f x) :=
  begin induction n with n p, refl, exact ap f p end

  @[hott] lemma iterate_sub {A : Type _} (f : A ≃ A) {n m : ℕ} (h : n ≥ m) (a : A) :
    iterate f (n - m) a = iterate f n (iterate f⁻¹ᶠ m a) :=
  begin
    induction m with m p generalizing n h,
    { refl },
    { cases n with n, apply empty.elim, apply not_succ_le_zero _ h,
      rwr [succ_sub_succ], refine p (le_of_succ_le_succ h) ⬝ _,
      refine ap (f^[n]) _ ⬝ (iterate_succ _ _ _)⁻¹, exact (to_right_inv _ _)⁻¹ }
  end

  @[hott] def iterate_commute {A : Type _} {f g : A → A} (n : ℕ) (h : f ∘ g ~ g ∘ f) :
    iterate f n ∘ g ~ g ∘ iterate f n :=
  begin induction n with n IH, refl, exact λx, ap f (IH x) ⬝ h _ end

  @[hott] def iterate_equiv {A : Type _} (f : A ≃ A) (n : ℕ) : A ≃ A :=
  equiv.mk (iterate f n)
    begin induction n with n IH, apply is_equiv_id, exactI is_equiv_compose f (iterate f n) end

  @[hott] def iterate_inv {A : Type _} (f : A ≃ A) (n : ℕ) :
    (iterate_equiv f n)⁻¹ᶠ ~ iterate f⁻¹ᶠ n :=
  begin
    induction n with n p; intro a,
      refl,
      exact p (f⁻¹ᶠ a) ⬝ (iterate_succ _ _ _)⁻¹
  end

  @[hott] def iterate_left_inv {A : Type _} (f : A ≃ A) (n : ℕ) (a : A) : f⁻¹ᵉ^[n] (f^[n] a) = a :=
  (iterate_inv f n (f^[n] a))⁻¹ ⬝ to_left_inv (iterate_equiv f n) a

  @[hott] def iterate_right_inv {A : Type _} (f : A ≃ A) (n : ℕ) (a : A) : f^[n] (f⁻¹ᵉ^[n] a) = a :=
  ap (f^[n]) (iterate_inv f n a)⁻¹ ⬝ to_right_inv (iterate_equiv f n) a



end nat
end hott
