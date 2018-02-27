/-
Copyright (c) 2015 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob von Raumer, Floris van Doorn

Proof of the @[hott] theorem that (is_trunc n A) is a mere proposition
We prove this here to avoid circular dependency of files
We want to use this in .equiv; .equiv is imported by .function and .function is imported by .trunc
-/

import hott.types.pi

universe u
namespace hott
hott_theory
open hott.sigma

namespace is_trunc
  @[hott] def is_contr.sigma_char (A : Type u) :
    (Σ (center : A), Π (a : A), center = a) ≃ (is_contr A) :=
  begin
    fapply equiv.MK,
    { intro S, exact (is_contr.mk S.1 S.2)},
    { intro H, cases H with H', cases H' with ce co, exact ⟨ce, co⟩},
    { intro H, cases H with H', cases H' with ce co, exact idp},
    { intro S, cases S, apply idp}
  end

  @[hott] def is_trunc.pi_char (n : ℕ₋₂) (A : Type u) :
    (Π (x y : A), is_trunc n (x = y)) ≃ (is_trunc (n .+1) A) :=
  begin
    fapply equiv.MK,
    { exact is_trunc_succ_intro},
    { introsI H x y, apply is_trunc_eq},
    { intro H, cases H, apply idp},
    { introI P, apply eq_of_homotopy, intro a, apply eq_of_homotopy, intro b,
      change is_trunc.mk (to_internal n (a = b)) = P a b,
      induction (P a b), apply idp},
  end

  @[hott] lemma is_prop_is_trunc (n : ℕ₋₂) (A : Type u) : is_prop (is_trunc n A) :=
  begin
    induction n generalizing A,
    { apply is_trunc_equiv_closed,
      { apply is_contr.sigma_char },
      apply is_prop.mk, intros,
      fapply sigma_eq, apply x.2,
      apply is_prop.elimo', apply pi.is_prop_pi_eq },
    { apply is_trunc_equiv_closed,
      apply is_trunc.pi_char,
      unfreezeI, apply_instance },
  end

  local attribute [instance] is_prop_is_trunc
  @[hott, instance] def is_trunc_succ_is_trunc (n m : ℕ₋₂) (A : Type u) :
    is_trunc (n.+1) (is_trunc m A) :=
  is_trunc_succ_of_is_prop (is_trunc m A) n

end is_trunc

end hott