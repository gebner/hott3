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
  instance : has_coe_to_sort pType.{u} := {
    S := Type u,
    coe := pType.carrier,
  }
  variables {A : Type _}

  @[hott, reducible] def pt [H : pointed A] := point A
  @[hott, reducible] def Point (A : Type*) := pType.Point A
  @[hott, reducible] def carrier (A : Type*) := pType.carrier A
  @[hott, reducible] protected def Mk {A : Type _} (a : A) := pType.mk A a
  @[hott, reducible] protected def MK (A : Type _) (a : A) := pType.mk A a
  @[hott, reducible] protected def mk' (A : Type _) [H : pointed A] : Type* :=
  pType.mk A (point A)
  @[hott, instance, priority 1900] def pointed_carrier (A : Type*) : pointed A :=
  pointed.mk (Point A)

  @[hott, hsimp] def coe_pType_mk (A : Type _) (a : A) :
    @coe_sort _ pointed.has_coe_to_sort {pType . carrier := A, Point := a} = A :=
  by refl

  @[hott, hsimp] def pt_pointed_mk (A : Type _) (a : A) :
    @pt A (pointed.mk a) = a :=
  by refl

  @[hott, hsimp] def Point_pType_mk (A : Type _) (a : A) :
    Point (pType.mk A a) = a :=
  by refl

end pointed
open pointed

section
/-- Todo: ptrunctype should have pType as a *field*, because otherwise it's annoying that Lean doesn't have definitional eta for structures -/
  structure ptrunctype (n : ℕ₋₂) :=
    (pcarrier : Type*)
    (struct : is_trunc n pcarrier)

  notation n `-Type*` := ptrunctype n
  @[hott] abbreviation pSet := 0-Type*
  notation `Set*` := pSet

  @[hott] instance pType_of_ptrunctype (n : ℕ₋₂) : has_coe (n-Type*) Type* :=
  ⟨λx, x.pcarrier⟩

  @[hott, reducible] def ptrunctype.to_pType {n : ℕ₋₂} (X : ptrunctype.{u} n) : pType.{u} :=
  ↑X

  @[hott] instance pType_of_pSet : has_coe Set* Type* :=
  hott.pType_of_ptrunctype 0

  @[hott, reducible] def ptrunctype.to_trunctype {n : ℕ₋₂} (X : n-Type*) : n-Type :=
  ⟨X, X.struct⟩

  @[hott] instance trunctype_of_ptrunctype (n : ℕ₋₂) : has_coe (n-Type*) (n-Type) :=
  ⟨λx, x.to_trunctype⟩

  @[hott, hsimp] def coe_ptrunctype_mk (A : Type*) {n : ℕ₋₂} (H : is_trunc n A) :
    ↑{ptrunctype . pcarrier := A, struct := H} = A :> Type* :=
  by refl

  @[hott, hsimp] def coe_sort_ptrunctype_mk (A : Type*) {n : ℕ₋₂} (H : is_trunc n A) :
    ↥{ptrunctype . pcarrier := A, struct := H} = @coe_sort _ _ A :=
  by refl


  -- @[hott] instance ptrunctype.has_coe_to_sort (n) : has_coe_to_sort (ptrunctype n) :=
  -- ⟨_, ptrunctype.carrier⟩

  @[hott] instance is_trunc_ptrunctype {n : ℕ₋₂} (X : ptrunctype n)
    : is_trunc n X :=
  X.struct

  @[hott] instance is_trunc_pointed {n : ℕ₋₂} (X : ptrunctype n)
    : pointed X :=
  pointed_carrier X.to_pType

end

namespace pointed

  @[hott] protected def ptrunctype.mk' (n : ℕ₋₂)
    (A : Type _) [pointed A] [is_trunc n A] : n-Type* :=
  ptrunctype.mk (pointed.MK A pt) (by apply_instance)

  @[hott] protected def pSet.mk := @ptrunctype.mk (-1.+1)
  @[hott] protected def pSet.mk' := ptrunctype.mk' (-1.+1)

  @[hott] def ptrunctype_of_trunctype {n : ℕ₋₂} (A : n-Type) (a : A)
    : n-Type* :=
  ptrunctype.mk (pointed.MK A a) (by apply_instance)

  @[hott] def ptrunctype_of_pType {n : ℕ₋₂} (A : Type*) (H : is_trunc n A)
    : n-Type* :=
  ptrunctype.mk A (by apply_instance)

  @[hott] def pSet_of_Set (A : Set) (a : A) : Set* :=
  ptrunctype_of_trunctype A a

  @[hott] def pSet_of_pType (A : Type*) (H : is_set A) : Set* :=
  ptrunctype.mk A (by apply_instance)

  -- Any contractible type is pointed
  @[hott, instance] def pointed_of_is_contr
    (A : Type _) [H : is_contr A] : pointed A :=
  pointed.mk (center _)

end pointed

/- pointed maps -/
variables {A : Type*}

structure ppi (P : A → Type _) (x₀ : P pt) :=
  (to_fun : Π a : A, P a)
  (resp_pt : to_fun (Point A) = x₀)

@[hott] def pppi' (P : A → Type*) : Type _ :=
ppi (λ a, P a) pt

@[hott] def ppi_const (P : A → Type*) : pppi' P :=
ppi.mk (λa, pt) idp

@[hott] def pppi (P : A → Type*) : Type* :=
pointed.MK (pppi' P) (ppi_const P)

-- do we want to make this already pointed?
@[hott] def pmap (A B : Type*) : Type _ := @pppi A (λa, B)

@[hott] instance (P : A → Type _) (x₀): has_coe_to_fun (ppi P x₀) := {
  F := λ f, Π a, P a,
  coe := λ f a, f.to_fun a
}

@[hott, hsimp] def coe_fn_ppi {P : A → Type _} {x₀} (f : Πa, P a) (p : f (Point A) = x₀) :
  @coe_fn _ (hott.has_coe_to_fun P x₀) {ppi . to_fun := f, resp_pt := p} = f :=
by refl

infix ` →* `:28 := pmap
notation `Π*` binders `, ` r:(scoped P, pppi P) := r

namespace pointed


  @[hott] def pppi.mk {P : A → Type*} (f : Πa, P a)
    (p : f pt = pt) : pppi P :=
  ppi.mk f p

  @[hott] def pppi.to_fun {P : A → Type*} (f : pppi' P)
    (a : A) : P a :=
  ppi.to_fun f a

  @[hott] instance {P : A → Type*}: has_coe_to_fun (pppi' P) := {
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
    coe := pmap.to_fun }

  @[hott] def respect_pt {P : A → Type _} {p₀ : P pt}
    (f : ppi P p₀) : f pt = p₀ :=
  ppi.resp_pt f

  @[hott, hsimp] def mk_to_fun {P : A → Type _} {p₀ : P pt}
    (f : Πa, P a) (p : f pt = p₀) (a : A) : (ppi.mk f p).to_fun a = f a :=
  by refl

  @[hott, hsimp] def mk_to_fun' {P : A → Type _} {p₀ : P pt}
    (f : Πa, P a) (p : f pt = p₀) (a : A) : ppi.mk f p a = f a :=
  by refl

  @[hott, hsimp] def pmap_mk_to_fun {A B : Type*} (f : A → B) (p : f pt = pt) (a : A) :
    (pmap.mk f p).to_fun a = f a :=
  by refl

  @[hott, hsimp] def pmap_mk_to_fun' {A B : Type*} (f : A → B) (p : f pt = pt) (a : A) :
    pmap.mk f p a = f a :=
  by refl

  @[hott, hsimp] def respect_pt_mk {P : A → Type _} {p₀ : P pt}
    (f : Πa, P a) (p : f pt = p₀) : respect_pt (ppi.mk f p) = p :=
  by refl

  @[hott, hsimp] def respect_pt_pmap_mk {A B : Type*} (f : A → B) (p : f pt = pt) :
    respect_pt (pmap.mk f p) = p :=
  by refl

  -- notation `Π*` binders `, ` r:(scoped P, ppi _ P) := r
  -- @[hott] def pmxap.mk [constructor] {A B : Type*} (f : A → B) (p : f pt = pt) : A →* B :=
  -- ppi.mk f p
  -- @[hott] def pmap.to_fun [coercion] [unfold 3] {A B : Type*} (f : A →* B) : A → B := f

/- pointed homotopies -/
@[hott] def phomotopy {P : A → Type _} {p₀ : P pt} (f g : ppi P p₀) : Type _ :=
ppi (λa, f a = g a) (respect_pt f ⬝ (respect_pt g)⁻¹)

-- structure phomotopy {A B : Type*} (f g : A →* B) : Type _ :=
--   (homotopy : f ~ g)
--   (homotopy_pt : homotopy pt ⬝ respect_pt g = respect_pt f)

  variables {P : A → Type _} {p₀ : P pt} {f g : ppi P p₀}

  infix ` ~* `:50 := phomotopy
  @[hott] def phomotopy.mk (h : f ~ g)
    (p : h pt ⬝ respect_pt g = respect_pt f) : f ~* g :=
  ppi.mk h (eq_con_inv_of_con_eq p)

  @[hott] protected def phomotopy.to_fun (h : f ~* g) : Π a : A, f a = g a :=
  ppi.to_fun h

  @[hott] instance phomotopy.has_coe_to_fun: has_coe_to_fun (f ~* g) := {
    F := _,
    coe := phomotopy.to_fun,
  }

  @[hott] def to_homotopy (p : f ~* g) : Πa, f a = g a := p
  @[hott] def to_homotopy_pt (p : f ~* g) :
    p pt ⬝ respect_pt g = respect_pt f :=
  con_eq_of_eq_con_inv (respect_pt p)


end pointed

end hott
