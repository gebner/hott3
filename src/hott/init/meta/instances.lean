/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
open lean
open lean.parser

local postfix `?`:9001 := optional
local postfix *:9001 := many

namespace tactic

/-- Reset the instance cache for the main goal. -/
meta def reset_instance_cache : tactic unit :=
unfreeze_local_instances

namespace interactive
open interactive interactive.types expr

/-- Reset the instance cache. This allows any new instances
  added to the context to be used in typeclass inference. -/
meta def resetI := reset_instance_cache

/-- Unfreeze local instances, which allows us to revert
  instances in the context. -/
meta def unfreezeI := tactic.unfreeze_local_instances

/-- Like `intro`, but uses the introduced variable
  in typeclass inference. -/
meta def introI (p : parse ident_?) : tactic unit :=
intro p >> reset_instance_cache

/-- Like `intros`, but uses the introduced variable(s)
  in typeclass inference. -/
meta def introsI (p : parse ident_*) : tactic unit :=
intros p >> reset_instance_cache

/-- Used to add typeclasses to the context so that they can
  be used in typeclass inference. The syntax is the same as `have`. -/
meta def haveI (h : parse ident?) (q₁ : parse (tk ":" *> texpr)?) (q₂ : parse $ (tk ":=" *> texpr)?) : tactic unit :=
do h ← match h with
  | none   := get_unused_name "_inst"
  | some a := return a
  end,
  «have» (some h) q₁ q₂,
  match q₁ with
  | none    := swap >> reset_instance_cache >> swap
  | some p₂ := reset_instance_cache
  end

/-- Used to add typeclasses to the context so that they can
  be used in typeclass inference. The syntax is the same as `let`. -/
meta def letI (h : parse ident?) (q₁ : parse (tk ":" *> texpr)?) (q₂ : parse $ (tk ":=" *> texpr)?) : tactic unit :=
do h ← match h with
  | none   := get_unused_name "_inst"
  | some a := return a
  end,
  «let» (some h) q₁ q₂,
  match q₁ with
  | none    := swap >> reset_instance_cache >> swap
  | some p₂ := reset_instance_cache
  end

/-- Like `exact`, but uses all variables in the context
  for typeclass inference. -/
meta def exactI (q : parse texpr) : tactic unit :=
reset_instance_cache >> exact q

/-- Like `apply`, but uses all variables in the context
  for typeclass inference. -/
meta def applyI (q : parse texpr) : tactic unit :=
reset_instance_cache >> apply q

/-- Try to close the goal using type class inference without using the cache. -/
meta def infer : tactic unit :=
reset_instance_cache >> apply_instance

/-- Like `apply`, but doesn't use type class inference. -/
meta def napply (q : parse texpr) : tactic unit :=
concat_tags (do h ← i_to_expr_for_apply q, tactic.apply h {instances := ff})

/-- Like `apply`, but doesn't use type class inference and doesn't reorder goals. -/
meta def nfapply (q : parse texpr) : tactic unit :=
concat_tags (do h ← i_to_expr_for_apply q, tactic.apply h 
 {instances := ff, new_goals := new_goals.all})



end interactive
end tactic
