/-
Copyright (c) 2016 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn

The definition of pointed types. This file is here to avoid circularities in the import graph
-/
import .trunc
universes u v w

namespace hott
hott_theory

open eq equiv is_equiv is_trunc

class pointed (A : Type u) :=
  (point : A)

structure pType :=
  (carrier : Type u)
  (Point   : carrier)

notation `Type*` := pType

namespace pointed
  instance: has_coe_to_sort pType := {
    S := _,
    coe := pType.carrier,
  }
  variables {A : Type _}

  @[hott] def pt [H : pointed A] := point A
  @[hott] def Point (A : Type*) := pType.Point A
  @[hott] def carrier (A : Type*) := pType.carrier A
  @[hott] protected def Mk {A : Type _} (a : A) := pType.mk A a
  @[hott] protected def MK (A : Type _) (a : A) := pType.mk A a
  @[hott] protected def mk' (A : Type _) [H : pointed A] : Type* :=
  pType.mk A (point A)
  @[hott, instance] def pointed_carrier (A : Type*) : pointed A.carrier :=
  pointed.mk (Point A)

end pointed
open pointed

set_option old_structure_cmd true

section
  structure ptrunctype (n : ℕ₋₂) extends trunctype.{u} n, pType.{u}

  @[hott, instance] def is_trunc_ptrunctype {n : ℕ₋₂} (X : ptrunctype n)
    : is_trunc n X.carrier :=
  X.struct

  @[hott] instance is_trunc_pointed {n : ℕ₋₂} (X : ptrunctype n)
    : pointed X.carrier :=
  pointed_carrier X.to_pType

end

notation n `-Type*` := ptrunctype n
@[reducible, hott] def pSet := 0-Type*
notation `Set*` := pSet

namespace pointed

  @[hott] protected def ptrunctype.mk' (n : ℕ₋₂)
    (A : Type _) [pointed A] [is_trunc n A] : n-Type* :=
  ptrunctype.mk A (by apply_instance) pt

  @[hott] protected def pSet.mk := @ptrunctype.mk (-1.+1)
  @[hott] protected def pSet.mk' := ptrunctype.mk' (-1.+1)

  @[hott] def ptrunctype_of_trunctype {n : ℕ₋₂} (A : n-Type) (a : A)
    : n-Type* :=
  ptrunctype.mk A.carrier (by apply_instance) a

  @[hott] def ptrunctype_of_pType {n : ℕ₋₂} (A : Type*) (H : is_trunc n A.carrier)
    : n-Type* :=
  ptrunctype.mk A.carrier (by apply_instance) pt

  @[hott] def pSet_of_Set (A : Set) (a : A) : Set* :=
  ptrunctype.mk A.carrier (by apply_instance) a

  @[hott] def pSet_of_pType (A : Type*) (H : is_set A.carrier) : Set* :=
  ptrunctype.mk A.carrier (by apply_instance) pt

  -- Any contractible type is pointed
  @[hott, instance] def pointed_of_is_contr
    (A : Type _) [H : is_contr A] : pointed A :=
  pointed.mk (center _)

end pointed

/- pointed maps -/
structure ppi {A : Type*} (P : A → Type _) (x₀ : P pt) :=
  (to_fun : Π a : A, P a)
  (resp_pt : to_fun (Point A) = x₀)

@[hott] def pppi' {A : Type*} (P : A → Type*) : Type _ :=
ppi (λ a, (P a).carrier) pt

@[hott] def ppi_const {A : Type*} (P : A → Type*) : pppi' P :=
ppi.mk (λa, pt) idp

@[hott] def pppi {A : Type*} (P : A → Type*) : Type* :=
pointed.MK (pppi' P) (ppi_const P)

-- do we want to make this already pointed?
@[hott] def pmap (A B : Type*) : Type _ := (@pppi A (λa, B)).carrier

@[hott] instance {A : Type*} (P : A → Type _) (x₀): has_coe_to_fun (ppi P x₀) := {
  F := λ f, Π a, P a,
  coe := λ f a, f.to_fun a
}

infix ` →* `:28 := pmap
notation `Π*` binders `, ` r:(scoped P, pppi P) := r


namespace pointed


  @[hott] def pppi.mk {A : Type*} {P : A → Type*} (f : Πa, P a)
    (p : f pt = pt) : pppi P :=
  ppi.mk f p

  @[hott] def pppi.to_fun {A : Type*} {P : A → Type*} (f : pppi' P)
    (a : A) : P a :=
  ppi.to_fun f a

  @[hott] instance {A : Type*} {P : A → Type*}: has_coe_to_fun (pppi' P) := {
    F := λ f, Π a, P a,
    coe := λ f a, f.to_fun a,
  }

	@[hott] def pmap.mk {A B : Type*} (f : A → B)
    (p : f (Point A) = Point B) : A →* B :=
	pppi.mk f p

  @[reducible] def pmap.to_fun {A B : Type*} (f : A →* B) : A → B :=
  pppi.to_fun f

  @[hott] instance pmap.has_coe_to_fun {A B : Type*}: has_coe_to_fun (A →* B) := {
    F := λ f, A → B,
    coe := pmap.to_fun,
  }

  @[hott] def respect_pt {A : Type*} {P : A → Type _} {p₀ : P pt}
    (f : ppi P p₀) : f pt = p₀ :=
  ppi.resp_pt f

  -- notation `Π*` binders `, ` r:(scoped P, ppi _ P) := r
  -- @[hott] def pmxap.mk [constructor] {A B : Type*} (f : A → B) (p : f pt = pt) : A →* B :=
  -- ppi.mk f p
  -- @[hott] def pmap.to_fun [coercion] [unfold 3] {A B : Type*} (f : A →* B) : A → B := f

end pointed open pointed

/- pointed homotopies -/
@[hott] def phomotopy {A : Type*} {P : A → Type _} {p₀ : P pt} (f g : ppi P p₀) : Type _ :=
ppi (λa, f a = g a) (respect_pt f ⬝ (respect_pt g)⁻¹)

-- structure phomotopy {A B : Type*} (f g : A →* B) : Type _ :=
--   (homotopy : f ~ g)
--   (homotopy_pt : homotopy pt ⬝ respect_pt g = respect_pt f)

namespace pointed
  variables {A : Type*} {P : A → Type _} {p₀ : P pt} {f g : ppi P p₀}

  infix ` ~* `:50 := phomotopy
  @[hott] def phomotopy.mk (h : f.to_fun ~ g.to_fun)
    (p : h pt ⬝ respect_pt g = respect_pt f) : f ~* g :=
  ppi.mk h (eq_con_inv_of_con_eq p)

  @[hott] def to_homotopy (p : f ~* g) : Πa, f a = g a := ppi.to_fun p
  @[hott] def to_homotopy_pt (p : f ~* g) :
    p.to_fun pt ⬝ respect_pt g = respect_pt f :=
  con_eq_of_eq_con_inv (respect_pt p)


end pointed

end hott
