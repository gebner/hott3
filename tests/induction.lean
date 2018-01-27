import hott.init
open expr tactic pexpr hott
universes u v
noncomputable theory
axiom sorry' : Π{α : Sort _}, α /- no warnings are generated when using this axiom -/

@[induction] def foo2 {X Y : Type} {P : X × Y → Type} (x : X × Y) (z : Πa b, P ⟨a, b⟩) : P x := sorry'
@[induction] def foo3 {P : ℕ × ℕ → Sort _} (x : ℕ × ℕ) (z : ℕ → P (0,0)) : P x := sorry'
@[induction] def foo4 {X Y : Type} {P : Type} (x : X × Y) (z : X → Y → P) : P := sorry'
@[induction] def foo5 {X : Type} {P : Type} (x : ℕ × X) (z : X → X → P) : P := sorry'
@[induction] def foo6 {P : hott.trunc -2 nat → Type} (x : hott.trunc -2 nat) (z : Π(n : ℕ), P (hott.trunc.tr n)) : P x := sorry'
@[induction] def foo7 {P : hott.trunc -2 nat → Type _} (x : hott.trunc -2 nat) (z : Πx, P x → P x) : (ℕ → P (hott.trunc.tr 0)) → P x := sorry'
@[induction] def foo8 {P : hott.trunc -2 nat → Type _} (x : hott.trunc -2 nat) : P x := sorry'
@[induction] def foo9 (n : ℕ₋₂) (A : Type _) {P : hott.trunc n A → Type _} (x : hott.trunc n A) : (Πx, P x) → P x := sorry'
@[induction] def foo10 (n : ℕ₋₂) (A : Type _) {P : Type _} (x : hott.trunc n A) : (ℕ → P) → P := sorry'
attribute [induction] trunc.rec
attribute [induction] hott.quotient.rec
attribute [induction, priority 2000] hott.trunc.rec
attribute [induction] hott.eq.idp_rec_on
attribute [induction] hott.eq.idp_rec_on
attribute [induction] hott.eq.rec
attribute [induction] prod.elim
def foo11 {X : Type} {P : Type} (x : X) (z : X → X → P) : P := sorry'
def foo12 {X : Type} {P : Type} (x : ℕ × X) (z : x = x → P) : P := sorry'
def foo13 {X : Type} {P : Type} (x : ℕ) (z : P) : P := sorry'

run_cmd success_if_fail $ get_induction_info `foo11
run_cmd success_if_fail $ get_induction_info `foo12
run_cmd success_if_fail $ get_induction_info `foo13

def indfoo {X Y : Type} (x : hott.trunc -2 nat) : hott.eq x x :=
begin
  hinduction x using foo7 with x' p n, all_goals { exact sorry' }
end

def indfoo2 (x : ℕ) (y : ℕ) : x = x :=
begin
  hinduction_only x with n IH,
  all_goals { exact sorry' }
end

def indfoo3 {X Y : Type} {P : bool × bool → Type} (x : bool × bool) (z : Πx, P x) : P x :=
begin
  hinduction_only x,
  exact sorry'
end

def indfoo4 {X Y : Type} {P : Type} (x : bool × bool) (z : P) : P :=
begin
  success_if_fail { hinduction x using foo5 },
  hinduction x,
  exact sorry'
end

def indfoo5 {X Y : Type} {P : hott.trunc -2 nat → Type} (x : hott.trunc -2 nat) (z : Πx, P x) : P x :=
begin
  hinduction_only x,
  exact sorry'
end

def indfoo6 {X Y : Type} (x : hott.trunc -2 nat) : hott.eq x x :=
begin
  hinduction x using trunc.rec with x' p n, reflexivity
end

example {X Y : Type} (x : hott.trunc -2 nat) : hott.eq x x :=
begin
  hinduction x using foo8 with x' p n
end

example {X Y : Type} (x : hott.trunc -2 nat) : hott.eq x x :=
begin
  hinduction x using foo9 with x' p n, all_goals { exact sorry' }
end

example {X Y : Type} (x : hott.trunc -2 nat) : hott.eq x x :=
begin
  success_if_fail { hinduction x using foo10 with x' p n }, exact sorry'
end

example (x : ℕ) (y : ℕ) : x = x :=
begin
  hinduction_only x using nat.rec with n IH generalizing y,
  all_goals { exact sorry' }
end

example (x : ℕ) (y : ℕ) : x = x :=
begin
  revert y,
  hinduction_only x using nat.rec with n IH,
  all_goals { intro },
  all_goals { exact sorry' }
end

example (x : ℕ) (p : x = 3) : x = x :=
begin
  hinduction_only x using nat.rec with n IH,
  all_goals { exact sorry' }
end

example (x : ℕ) : let y := x in Π(p : y = y), x = y :=
begin
  intros _ _,
  hinduction_only x using nat.rec with n IH generalizing y,
  all_goals { exact sorry' }
end

hott_theory

@[induction] def eqrec1 {A : Type u} {a : A} {C : Π (a' : A), a = a' → Sort v} (H : C a (refl a)) {a' : A} (n : a = a') : C a' n := sorry'
@[induction] def eqrec2 {A : Type u} {a : A} {C : a = a → Sort v} (H : C (refl a)) (n : a = a) : C n := sorry'
@[induction] def eqrec3 {A : Type u} {C : Π (a' : A), a' = a' → Sort v} (H : Πa, C a (refl a)) {a : A} (n : a = a) : C a n := sorry'
@[induction] def eqrec4 {A : Type u} {a : A} {C : A → Sort v} (H : C a) {a' : A} (n : a = a') : C a' := sorry'
@[induction] def eqrec5 {A : Type u} {a : A} {C : Sort v} (H : C) {a' : A} (n : a = a') : C := sorry'
attribute [induction] pathover.rec idp_rec_on
-- #print eqrec1._ind_info
-- #print eqrec2._ind_info
-- #print eqrec3._ind_info
-- #print eqrec4._ind_info
-- #print eqrec5._ind_info

open hott.trunc hott.is_trunc
@[hott] def trunc_sigma_equiv {n : ℕ₋₂} {A : Type _} {P : A → Type _} :
  trunc n (Σ x, P x) ≃ trunc n (Σ x, trunc n (P x)) :=
begin
  fapply equiv.MK; intro x,
  { hinduction x with p, exact tr ⟨p.1, tr p.2⟩ },
  { hinduction x with p, induction p with a p, hinduction p with p, exact tr ⟨a, p⟩ },
  all_goals { exact sorry' }
end

@[hott] def trunc_sigma_equiv2 {n : ℕ₋₂} {A : Type _} {P : A → Type _} :
  trunc n (Σ x, P x) ≃ trunc n (Σ x, trunc n (P x)) :=
begin
  fapply equiv.MK; intro x,
  { hinduction x with p, exact tr ⟨p.1, tr p.2⟩ },
  { hinduction x with p, have x := p.2, hinduction x with q, exact tr ⟨p.1, q⟩ },
  all_goals { exact sorry' }
end


def eqrecfail1 {A : Type u} {a : A} {C : Π (a' : A), a = a' → Sort v} (H : C a (refl a)) {a' : A} (n : a = a') : C (id a') n := sorry'
def eqrecfail2 {A : Type u} {a : A} {C : Π (a' : A), a = a' → Sort v} (H : C a (refl a)) {a' : A} (n : a = a') : C a' (n ⬝ idp) := sorry'
def eqrecfail3 {A : Type u} {a : A} {C : Π (a' : A), a = a' → Sort v} (H : C a (refl a)) {a' : A} (n : a = id a') : C a' n := sorry'

run_cmd success_if_fail $ get_induction_info `eqrecfail1
run_cmd success_if_fail $ get_induction_info `eqrecfail2
run_cmd success_if_fail $ get_induction_info `eqrecfail3
--run_cmd success_if_fail $ get_induction_info `eqrecfail4
-- #print eqrec1._ind_info
-- #print idp_rec_on._ind_info
-- #print idp_rec_on