/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Jakob von Raumer, Floris van Doorn

Ported from Coq HoTT
-/
import .meta.support

universes u v w
hott_theory

namespace hott
open function

/- Path equality -/

inductive eq {A : Type u} (a : A) : A → Type u
| refl : eq a

hott_theory_cmd "open hott.eq"
hott_theory_cmd "local infix ` = ` := hott.eq"

@[hott, reducible] def rfl {A : Type u} {a : A} := eq.refl a

end hott