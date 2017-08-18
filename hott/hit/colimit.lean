/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn

Definition of general colimits and sequential colimits.
-/
import hott.init

universes u v w
hott_theory

namespace hott

/- definition of a general colimit -/
open hott.eq nat hott.quotient sigma equiv is_trunc

namespace colimit
section
  parameters {I : Type u} {J : Type v} (A : I → Type w) (dom cod : J → I)
             (f : Π(j : J), A (dom j) → A (cod j))
  variables {i : I} (a : A i) (j : J) (b : A (dom j))

  local notation `B` := Σ(i : I), A i
  inductive colim_rel : B → B → Type (max u v w)
  | Rmk : Π{j : J} (a : A (dom j)), colim_rel ⟨cod j, f j a⟩ ⟨dom j, a⟩
  open colim_rel
  local notation `R` := colim_rel

  -- TODO: define this in root namespace
  @[hott] def colimit : Type _ :=
  quotient colim_rel

  @[hott] def incl : colimit :=
  class_of R ⟨i, a⟩

  @[hott, reducible] def ι := @incl

  @[hott] def cglue : eq.{max u v w} (ι (f j b)) (ι b) :=
  eq_of_rel colim_rel (Rmk _ : colim_rel ⟨_, f j b⟩ ⟨_, b⟩)

  @[hott, elab_as_eliminator] protected def rec {P : colimit → Type _}
    (Pincl : Π⦃i : I⦄ (x : A i), P (ι x))
    (Pglue : Π(j : J) (x : A (dom j)), Pincl (f j x) =[cglue j x] Pincl x)
      (y : colimit) : P y :=
  begin
    fapply (quotient.rec_on y),
    { intro a, induction a, apply Pincl},
    { intros a a' H, induction H, apply Pglue}
  end

  @[hott, elab_as_eliminator] protected def rec_on {P : colimit → Type _} (y : colimit)
    (Pincl : Π⦃i : I⦄ (x : A i), P (ι x))
    (Pglue : Π(j : J) (x : A (dom j)), Pincl (f j x) =[cglue j x] Pincl x) : P y :=
  rec Pincl Pglue y

  @[hott] theorem rec_cglue {P : colimit → Type _}
    (Pincl : Π⦃i : I⦄ (x : A i), P (ι x))
    (Pglue : Π(j : J) (x : A (dom j)), Pincl (f j x) =[cglue j x] Pincl x)
      {j : J} (x : A (dom j)) : apd (rec Pincl Pglue) (cglue j x) = Pglue j x :=
  by delta cglue hott.colimit.rec; dsimp [quotient.rec_on]; apply rec_eq_of_rel

  @[hott] protected def elim {P : Type _} (Pincl : Π⦃i : I⦄ (x : A i), P)
    (Pglue : Π(j : J) (x : A (dom j)), Pincl (f j x) = Pincl x) (y : colimit) : P :=
  @rec (λ _, P) Pincl (λj a, pathover_of_eq _ (Pglue j a)) y

  @[hott] protected def elim_on {P : Type _} (y : colimit)
    (Pincl : Π⦃i : I⦄ (x : A i), P)
    (Pglue : Π(j : J) (x : A (dom j)), Pincl (f j x) = Pincl x) : P :=
  elim Pincl Pglue y

  @[hott, hsimp] def elim_incl {P : Type _} (Pincl : Π⦃i : I⦄ (x : A i), P)
    (Pglue : Π(j : J) (x : A (dom j)), Pincl (f j x) = Pincl x) :
    hott.colimit.elim Pincl Pglue (ι a) = Pincl a := idp

  @[hott] theorem elim_cglue {P : Type _}
    (Pincl : Π⦃i : I⦄ (x : A i), P)
    (Pglue : Π(j : J) (x : A (dom j)), Pincl (f j x) = Pincl x)
      {j : J} (x : A (dom j)) : ap.{max u v w} (elim Pincl Pglue) (cglue j x) = Pglue j x :=
  begin
    apply eq_of_fn_eq_fn_inv (pathover_constant _ _ _),
    dsimp [pathover_constant, equiv.MK, is_equiv.adjointify, is_equiv.mk],
    rwr ← apd_eq_pathover_of_eq_ap,
    delta colimit.elim; rwr rec_cglue,
  end

  @[hott] protected def elim_type (Pincl : Π⦃i : I⦄ (x : A i), Type _)
    (Pglue : Π(j : J) (x : A (dom j)), Pincl (f j x) ≃ Pincl x) (y : colimit) : Type _ :=
  elim Pincl (λj a, ua (Pglue j a)) y

  @[hott] protected def elim_type_on (y : colimit)
    (Pincl : Π⦃i : I⦄ (x : A i), Type _)
    (Pglue : Π(j : J) (x : A (dom j)), Pincl (f j x) ≃ Pincl x) : Type _ :=
  elim_type Pincl Pglue y

  @[hott] theorem elim_type_cglue (Pincl : Π⦃i : I⦄ (x : A i), Type _)
    (Pglue : Π(j : J) (x : A (dom j)), Pincl (f j x) ≃ Pincl x)
      {j : J} (x : A (dom j)) : transport (elim_type Pincl Pglue) (cglue j x) = (Pglue j x).to_fun :=
  by rwr tr_eq_cast_ap_fn; delta elim_type; rwr elim_cglue; apply cast_ua_fn

  @[hott] protected def rec_prop {P : colimit → Type _} [H : Πx, is_prop (P x)]
    (Pincl : Π⦃i : I⦄ (x : A i), P (ι x)) (y : colimit) : P y :=
  rec Pincl (λa b, is_prop.elimo _ _ _) y

  @[hott] protected def elim_prop {P : Type _} [H : is_prop P] (Pincl : Π⦃i : I⦄ (x : A i), P)
    (y : colimit) : P :=
  elim Pincl (λa b, is_prop.elim _ _) y

end
end colimit

/- definition of a sequential colimit -/
namespace seq_colim
section
  /-
    we define it directly in terms of quotients. An alternative definition could be
    @[hott] def seq_colim := colimit.colimit A id succ f
  -/
  parameters {A : ℕ → Type u} (f : Π⦃n⦄, A n → A (succ n))
  variables {n : ℕ} (a : A n)

  local notation `B` := Σ(n : ℕ), A n
  inductive seq_rel : B → B → Type u
  | Rmk : Π{n : ℕ} (a : A n), seq_rel ⟨succ n, f a⟩ ⟨n, a⟩
  open seq_rel
  local notation `R` := seq_rel

  -- TODO: define this in root namespace
  @[hott] def seq_colim : Type _ :=
  quotient seq_rel

  @[hott] def inclusion : seq_colim :=
  class_of R ⟨n, a⟩

  @[reducible,hott] def sι := @inclusion

  @[hott] def glue : sι (f a) = sι a :=
  eq_of_rel seq_rel (Rmk a)

  @[hott] protected def rec {P : seq_colim → Type _}
    (Pincl : Π⦃n : ℕ⦄ (a : A n), P (sι a))
    (Pglue : Π(n : ℕ) (a : A n), Pincl (f a) =[glue a] Pincl a) (aa : seq_colim) : P aa :=
  begin
    fapply (quotient.rec_on aa),
    { intro a, induction a, apply Pincl},
    { intros a a' H, induction H, apply Pglue}
  end

  @[hott] protected def rec_on {P : seq_colim → Type _} (aa : seq_colim)
    (Pincl : Π⦃n : ℕ⦄ (a : A n), P (sι a))
    (Pglue : Π⦃n : ℕ⦄ (a : A n), Pincl (f a) =[glue a] Pincl a)
      : P aa :=
  rec Pincl Pglue aa

  @[hott] theorem rec_glue {P : seq_colim → Type _} (Pincl : Π⦃n : ℕ⦄ (a : A n), P (sι a))
    (Pglue : Π⦃n : ℕ⦄ (a : A n), Pincl (f a) =[glue a] Pincl a) {n : ℕ} (a : A n)
      : apd (rec Pincl Pglue) (glue a) = Pglue a :=
  by delta glue seq_colim.rec; dsimp [quotient.rec_on]; apply rec_eq_of_rel

  @[hott] protected def elim {P : Type _} (Pincl : Π⦃n : ℕ⦄ (a : A n), P)
    (Pglue : Π⦃n : ℕ⦄ (a : A n), Pincl (f a) = Pincl a) : seq_colim → P :=
  rec Pincl (λn a, pathover_of_eq _ (Pglue a))

  @[hott, hsimp] def elim_incl {P : Type _} (Pincl : Π⦃n : ℕ⦄ (a : A n), P)
    (Pglue : Π⦃n : ℕ⦄ (a : A n), Pincl (f a) = Pincl a) :
    hott.seq_colim.elim Pincl Pglue (sι a) = Pincl a :=
  idp

  @[hott] protected def elim_on {P : Type _} (aa : seq_colim)
    (Pincl : Π⦃n : ℕ⦄ (a : A n), P)
    (Pglue : Π⦃n : ℕ⦄ (a : A n), Pincl (f a) = Pincl a) : P :=
  elim Pincl Pglue aa

  @[hott] theorem elim_glue {P : Type _} (Pincl : Π⦃n : ℕ⦄ (a : A n), P)
    (Pglue : Π⦃n : ℕ⦄ (a : A n), Pincl (f a) = Pincl a) {n : ℕ} (a : A n)
      : ap (elim Pincl Pglue) (glue a) = Pglue a :=
  begin
    apply eq_of_fn_eq_fn_inv (pathover_constant _ _ _),
    dsimp [pathover_constant, equiv.MK, is_equiv.adjointify, is_equiv.mk],
    rwr ← apd_eq_pathover_of_eq_ap,
    delta elim; rwr rec_glue,
  end

  @[hott] protected def elim_type (Pincl : Π⦃n : ℕ⦄ (a : A n), Type _)
    (Pglue : Π⦃n : ℕ⦄ (a : A n), Pincl (f a) ≃ Pincl a) : seq_colim → Type _ :=
  elim Pincl (λn a, ua (Pglue a))

  @[hott] protected def elim_type_on (aa : seq_colim)
    (Pincl : Π⦃n : ℕ⦄ (a : A n), Type _)
    (Pglue : Π⦃n : ℕ⦄ (a : A n), Pincl (f a) ≃ Pincl a) : Type _ :=
  elim_type Pincl Pglue aa

  @[hott] theorem elim_type_glue (Pincl : Π⦃n : ℕ⦄ (a : A n), Type _)
    (Pglue : Π⦃n : ℕ⦄ (a : A n), Pincl (f a) ≃ Pincl a) {n : ℕ} (a : A n)
      : transport (elim_type Pincl Pglue) (glue a) = (Pglue a).to_fun :=
  by rwr tr_eq_cast_ap_fn; dunfold elim_type; rwr elim_glue; apply cast_ua_fn

  @[hott] theorem elim_type_glue_inv (Pincl : Π⦃n : ℕ⦄ (a : A n), Type _)
    (Pglue : Π⦃n : ℕ⦄ (a : A n), Pincl (f a) ≃ Pincl a) {n : ℕ} (a : A n)
    : transport (hott.seq_colim.elim_type Pincl Pglue) (glue a)⁻¹ = to_inv (Pglue a) :=
  by rwr tr_eq_cast_ap_fn; dunfold elim_type; rwr [ap_inv, elim_glue]; dsimp; apply cast_ua_inv_fn

  @[hott] protected def rec_prop {P : seq_colim → Type _} [H : Πx, is_prop (P x)]
    (Pincl : Π⦃n : ℕ⦄ (a : A n), P (sι a)) (aa : seq_colim) : P aa :=
  rec Pincl (by intros; apply is_prop.elimo) aa

  @[hott] protected def elim_prop {P : Type _} [H : is_prop P] (Pincl : Π⦃n : ℕ⦄ (a : A n), P)
    : seq_colim → P :=
  elim Pincl (λa b, is_prop.elim _ _)


end
end seq_colim

end hott