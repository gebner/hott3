/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn

Theorems about the unit type
-/

import ..init
universes u v w
hott_theory
namespace hott
open hott.is_equiv hott.equiv option pointed is_trunc function unit

notation `⋆` := unit.star

namespace unit

  @[hott] protected def eta : Π(u : unit), ⋆ = u
  | ⋆ := idp

  @[hott] def unit_equiv_option_empty : unit ≃ option empty :=
  begin
    fapply equiv.MK,
    { intro u, exact none },
    { intro e, exact ⋆ },
    { intro e, cases e, reflexivity, apply empty.elim e },
    { intro u, cases u, reflexivity },
  end

  -- equivalences involving unit and other type constructors are in the file
  -- of the other constructor

  /- pointed and truncated unit -/  

  @[hott] def punit : Set* :=
  have H : is_set unit, by apply_instance, 
  pSet.mk unit H ⋆

  notation `unit*` := punit

  @[hott, instance] def is_contr_punit : is_contr punit :=
  is_contr_unit

  @[hott] def unit_arrow_eq {X : Type _} (f : unit → X) : (λx : unit, f ⋆) = f :=
  by apply eq_of_homotopy; intro u; induction u; reflexivity

  open hott.funext
  local attribute [instance] is_equiv_apdt
  @[hott] def unit_arrow_eq_compose {X Y : Type _} (g : X → Y) (f : unit → X) :
    unit_arrow_eq (g ∘ f) = ap (λ(f : unit → X), g ∘ f) (unit_arrow_eq f) :=
  begin
    refine eq_of_fn_eq_fn' apd10 _,
    refine right_inv apd10 _ ⬝ _,
    delta unit_arrow_eq, rwr [compose_eq_of_homotopy],
    refine _ ⬝ (right_inv apd10 _)⁻¹,
    apply eq_of_homotopy, intro u, induction u, reflexivity
  end

end unit
end hott
