/-
Copyright (c) 2017 Gabriel Ebner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner
-/
open expr tactic

local postfix `?`:9001 := optional

namespace tactic.interactive
open interactive interactive.types lean.parser lean 
/--
A version of `intro` which will never insert `id_locked` in the proof term. 

The `intro` tactic will add `id_locked` to the proof term if the goal is not a Pi or a let (but reduces to one).

See issue lean#1260.
-/
meta def hintro : parse ident_? → tactic unit
| none     := intro_core `_ >> skip
| (some h) := intro_core h >> skip

end tactic.interactive