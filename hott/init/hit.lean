/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn

Declaration of the primitive hits in Lean
-/
import hott.init.trunc hott.init.pathover

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
  We add the computation rule for point constructors judgmentally to the kernel of Lean.
  The computation rules for the path constructors are added (propositionally) as axioms

  In this file we only define the dependent recursor. For the nondependent recursor and all other
  uses of these hits, see the folder ../hit/
-/

constant trunc (n : ℕ₋₂) (A : Type u) : Type u

namespace trunc
  constant tr {n : ℕ₋₂} {A : Type u} (a : A) : trunc n A
  axiom is_trunc_trunc (n : ℕ₋₂) (A : Type u) : is_trunc n (trunc n A)

  attribute [instance] is_trunc_trunc

  protected constant rec {n : ℕ₋₂} {A : Type u} {P : trunc n A → Type v}
    [Pt : Πaa, is_trunc n (P aa)] (H : Πa, P (tr a)) : Πaa, P aa

  computation_rule trunc.comp_rule {n : ℕ₋₂} {A : Type u} {P : trunc n A → Type v}
      [Pt : Πaa, is_trunc n (P aa)] (H : Πa, P (tr a)) (a : A) :
    @trunc.rec n A P Pt H (@tr n A a) = H a

  private def trunc.impl (n : ℕ₋₂) (A : Type u) : Type u := A
  private def trunc.impl.tr {n : ℕ₋₂} {A : Type u} (a : A) : trunc.impl n A := a
  private def trunc.impl.rec {n : ℕ₋₂} {A : Type u} {P : trunc.impl n A → Type v}
    [Pt : Πaa, is_trunc n (P aa)] (H : Πa, P (trunc.impl.tr a)) : Πaa, P aa := H
  unsafe_make_computable trunc.tr trunc.impl.tr
  unsafe_make_computable trunc.rec trunc.impl.rec

  protected definition rec_on {n : ℕ₋₂} {A : Type}
    {P : trunc n A → Type} (aa : trunc n A) [Pt : Πaa, is_trunc n (P aa)] (H : Πa, P (tr a))
    : P aa :=
  trunc.rec H aa
end trunc

constant quotient {A : Type.{u}} (R : A → A → Type.{v}) : Type.{max u v}

namespace quotient

  constant class_of {A : Type u} (R : A → A → Type v) (a : A) : quotient R

  constant eq_of_rel {A : Type u} (R : A → A → Type v) ⦃a a' : A⦄ (H : R a a')
    : class_of R a = class_of R a'

  protected constant rec {A : Type u} {R : A → A → Type v} {P : quotient R → Type w}
    (Pc : Π(a : A), P (class_of R a)) (Pp : Π⦃a a' : A⦄ (H : R a a'), Pc a =[eq_of_rel R H] Pc a')
    (x : quotient R) : P x

  computation_rule quotient.rec {A : Type u} {R : A → A → Type v} {P : quotient R → Type w}
    (Pc : Π(a : A), P (class_of R a)) (Pp) (a : A) :
    @quotient.rec A R P Pc Pp (@quotient.class_of A R a) = Pc a

  private def quotient.impl {A : Type.{u}} (R : A → A → Type.{v}) : Type.{max u v} := ulift A
  private def quotient.impl.class_of {A : Type u} (R : A → A → Type v) (a : A) : quotient.impl R := ulift.up a
  private def quotient.impl.rec {A : Type u} {R : A → A → Type v} {P : quotient.impl R → Type w}
    (Pc : Π(a : A), P (quotient.impl.class_of R a)) (Pp : Π⦃a a' : A⦄ (H : R a a'), Pc a == Pc a')
    (x : quotient.impl R) : P x := _root_.cast (congr_arg _ (ulift.up_down _)) $ Pc (ulift.down x)
  unsafe_make_computable class_of quotient.impl.class_of
  unsafe_make_computable quotient.rec quotient.impl.rec

  protected definition rec_on {A : Type u} {R : A → A → Type v} {P : quotient R → Type w}
    (x : quotient R) (Pc : Π(a : A), P (class_of R a))
    (Pp : Π⦃a a' : A⦄ (H : R a a'), Pc a =[eq_of_rel R H] Pc a') : P x :=
  quotient.rec Pc Pp x

end quotient

namespace trunc
  definition rec_tr {n : ℕ₋₂} {A : Type u} {P : trunc n A → Type v}
    [Pt : Πaa, is_trunc n (P aa)] (H : Πa, P (tr a)) (a : A) : trunc.rec H (tr a) = H a :=
  idp
end trunc

namespace quotient
  definition rec_class_of {A : Type u} {R : A → A → Type v} {P : quotient R → Type w}
    (Pc : Π(a : A), P (class_of R a)) (Pp : Π⦃a a' : A⦄ (H : R a a'), Pc a =[eq_of_rel R H] Pc a')
    (a : A) : quotient.rec Pc Pp (class_of R a) = Pc a :=
  idp

  constant rec_eq_of_rel {A : Type u} {R : A → A → Type v} {P : quotient R → Type w}
    (Pc : Π(a : A), P (class_of R a)) (Pp : Π⦃a a' : A⦄ (H : R a a'), Pc a =[eq_of_rel R H] Pc a')
    {a a' : A} (H : R a a') : apd (quotient.rec Pc Pp) (eq_of_rel R H) = Pp H
end quotient

-- attribute quotient.class_of trunc.tr [constructor]
-- attribute quotient.rec_on trunc.rec_on [unfold 4]

end hott
