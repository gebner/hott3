/-
Copyright (c) 2017 Gabriel Ebner, Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Floris van Doorn

Declaration of the primitive hits in Lean
-/
import .trunc .pathover .meta.induction

universes u v w l
hott_theory

namespace hott
open is_trunc eq

/-
  We take two higher inductive types (hits) as primitive notions in Lean. We define all other hits
  in terms of these two hits. The hits which are primitive are
    - n-truncation
    - quotients (not truncated)
  For each of the hits we add the following constants:
    - the type formation
    - the term and path constructors
    - the dependent recursor

  Both HITs are essentially newtypes that impose an additional restriction on
  the minor premise in the eliminator.  We implement these types without
  modifying the kernel.  For each type, we define a private structure with
  unrestricted eliminator.  We then define the correct recursor on top, and
  manually add the path constructors axiomatically.  There are two protections
  against use of the internal (unsound) eliminator: 1) it is private, 2) it
  is marked with [nothott] so that the HoTT checker rejects it.

  In this file we only define the dependent recursor. For the nondependent recursor and all other
  uses of these hits, see the folder ../hit/
-/

private structure trunc_impl (n : ℕ₋₂) (A : Type u) : Type u :=
(a : A)

@[hott] def trunc (n : ℕ₋₂) (A : Type u) : Type u :=
trunc_impl n A

namespace trunc
  @[hott] def tr {n : ℕ₋₂} {A : Type u} (a : A) : trunc n A :=
  trunc_impl.mk n a

  @[hott] axiom is_trunc_trunc (n : ℕ₋₂) (A : Type u) : is_trunc n (trunc n A)
  attribute [instance] is_trunc_trunc

  @[hott, induction, priority 1000] protected def rec {n : ℕ₋₂} {A : Type u} {P : trunc n A → Type v}
    [Pt : Πaa, is_trunc n (P aa)] (H : Πa, P (tr a)) (aa : trunc n A) : P aa :=
  (match aa with ⟨_, a⟩ := ⟨Pt, H _⟩ end : _ × P aa).snd

  attribute [nothott] trunc_impl.rec
  attribute [irreducible] trunc

  @[hott, hsimp, reducible, elab_as_eliminator] protected definition rec_on {n : ℕ₋₂} {A : Type u}
    {P : trunc n A → Type v} (aa : trunc n A) [Pt : Πaa, is_trunc n (P aa)] (H : Πa, P (tr a))
    : P aa :=
  trunc.rec H aa
end trunc

private structure quotient_impl {A : Type u} (R : A → A → Type v) : Type (max u v) :=
(a : A)

@[hott] def quotient {A : Type u} (R : A → A → Type v) : Type (max u v) :=
quotient_impl R

namespace quotient

  @[hott] def class_of {A : Type u} (R : A → A → Type v) (a : A) : quotient R :=
  quotient_impl.mk R a

  @[hott] axiom eq_of_rel {A : Type u} (R : A → A → Type v) ⦃a a' : A⦄ (H : R a a')
    : class_of R a = class_of R a'

  @[hott, induction, priority 1000] protected def rec {A : Type u} {R : A → A → Type v} {P : quotient R → Type w}
    (Pc : Π(a : A), P (class_of R a)) (Pp : Π⦃a a' : A⦄ (H : R a a'), Pc a =[eq_of_rel R H] Pc a')
    (x : quotient R) : P x :=
  (match x with ⟨_, a⟩ := ⟨Pp, Pc a⟩ end : _ × P x).snd

  attribute [nothott] quotient_impl.rec
  attribute [irreducible] quotient

  @[hott, hsimp, reducible, elab_as_eliminator] protected def rec_on {A : Type u} {R : A → A → Type v} {P : quotient R → Type w}
    (x : quotient R) (Pc : Π(a : A), P (class_of R a))
    (Pp : Π⦃a a' : A⦄ (H : R a a'), Pc a =[eq_of_rel R H] Pc a') : P x :=
  quotient.rec Pc Pp x

end quotient

namespace trunc
  @[hott, hsimp] def rec_tr {n : ℕ₋₂} {A : Type u} {P : trunc n A → Type v}
    [Pt : Πaa, is_trunc n (P aa)] (H : Πa, P (tr a)) (a : A) : trunc.rec H (tr a) = H a :=
  idp

  -- Make sure that the `Pt` argument is relevant in def-eq comparison
  open tactic
  local attribute [reducible] trunc
  example {n : ℕ₋₂} {A : Type u} {P : trunc n A → Type v} (Pt Pt') (H aa) :
    @trunc.rec _ _ P Pt H aa = @trunc.rec _ _ P Pt' H aa :=
  begin
    success_if_fail { refl },
    cases aa, refl, -- non-HoTT proof so that example doesn't fail
  end
end trunc

namespace quotient
  @[hott, hsimp] def rec_class_of {A : Type u} {R : A → A → Type v} {P : quotient R → Type w}
    (Pc : Π(a : A), P (class_of R a)) (Pp : Π⦃a a' : A⦄ (H : R a a'), Pc a =[eq_of_rel R H] Pc a')
    (a : A) : quotient.rec Pc Pp (class_of R a) = Pc a :=
  idp

  @[hott] constant rec_eq_of_rel {A : Type u} {R : A → A → Type v} {P : quotient R → Type w}
    (Pc : Π(a : A), P (class_of R a)) (Pp : Π⦃a a' : A⦄ (H : R a a'), Pc a =[eq_of_rel R H] Pc a')
    {a a' : A} (H : R a a') : apd (quotient.rec Pc Pp) (eq_of_rel R H) = Pp H

  -- Make sure that the `Pp` argument is relevant in def-eq comparison
  open tactic
  local attribute [reducible] quotient
  example {A : Type u} {R : A → A → Type v} {P : quotient R → Type w}
        (Pc : Π(a : A), P (class_of R a)) (Pp Pp' x) :
    quotient.rec Pc Pp x = quotient.rec Pc Pp' x :=
  begin
    success_if_fail { refl },
    cases x, refl, -- non-HoTT proof so that example doesn't fail
  end
end quotient

end hott
