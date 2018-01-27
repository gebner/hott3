/-
Copyright (c) 2017 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
import ..path0

universes u v w
namespace list
open tactic
meta def mmap_filter {α : Type u} {β : Type v} (f : α → tactic (option β)) : list α → tactic (list β)
| []       := return []
| (x :: xs) := do oy ← f x, ys ← mmap_filter xs, some y ← return oy | return ys, return $ y :: ys

end list
namespace option

/-- The mmap for options. -/
def mmap {m : Type u → Type v} [monad m] {α : Type w} {β : Type u} (f : α → m β) : option α → m (option β)
| none     := return none
| (some x) := do y ← f x, return $ some y

def iget {α : Type u} [inhabited α] : option α → α
| none     := default α
| (some x) := x
end option

namespace expr

variable {elab : bool}
/-- returns a list of names, binder_info's and domains and the conclusion of the expression -/
meta def destruct_pis : expr elab → list name × list binder_info × list (expr elab) × expr elab
| (pi n bi a b) := let (ns, bis, es, e) := destruct_pis b in (n::ns, bi::bis, a::es, e)
| a             := ([], [], [], a)

instance inhabited_binder_info : inhabited binder_info :=
⟨binder_info.default⟩

end expr

hott_theory

namespace tactic
open expr

open interaction_monad interaction_monad.result

/-- executes t₂ when tactic t₁ fails. After t₂ is executed, do_on_failure fails with the error message given by t₂ -/
meta def do_on_failure {α : Type _} (t₁ : tactic α) (t₂ : format → tactic format) : tactic α :=
λ s, match t₁ s with
| (exception (some f) pos s') := (t₂ (f ()) >>= λx, exception (some $ λ_, x) pos) s'
| (exception none pos s') := exception none pos s'
| (interaction_monad.result.success a s') := interaction_monad.result.success a s'
end

/-- change the error message on failure of t₁ -/
meta def change_failure {α : Type _} (t₁ : tactic α) (t₂ : format → format) : tactic α :=
do_on_failure t₁ $ return ∘ t₂

/-- If t₁ fails, also trace the failure -/
meta def trace_failure {α : Type _} (t₁ : tactic α) : tactic α :=
do_on_failure t₁ $ λfmt, trace fmt >> return fmt

meta def hgeneralize (h : option name) (p : pexpr) (x : name) : tactic unit :=
do e ← i_to_expr p,
   some h ← pure h | tactic.generalize e x >> intro1 >> skip,
   tgt ← target,
   -- if generalizing fails, fall back to not replacing anything
   tgt' ← do {
     ⟨tgt', _⟩ ← solve_aux tgt (tactic.generalize e x >> target),
     to_expr ``(Π x, %%e = x → %%(tgt'.binding_body.lift_vars 0 1))
   } <|> to_expr ``(Π x, %%e = x → %%tgt),
   t ← assert h tgt',
   swap,
   interactive.exact ``(%%t %%e rfl),
   interactive.intro x,
   interactive.intro h

namespace interactive

open lean lean.parser interactive
local postfix `?`:9001 := optional

meta def fconstructor : tactic unit :=
tactic.fconstructor >> skip

meta def infer : tactic unit := apply_instance

private meta def generalize_arg_p_aux : pexpr → parser (pexpr × name)
| (app (app (macro _ [const ``hott.eq _ ]) h) (local_const x _ _ _)) := pure (h, x)
| _ := fail "parse error"

private meta def generalize_arg_p : parser (pexpr × name) :=
with_desc "expr = id" $ parser.pexpr 0 >>= generalize_arg_p_aux

/--
`hgeneralize : e = x` replaces all occurrences of `e` in the target with a new hypothesis `x` of the same type.

`hgeneralize h : e = x` in addition registers the hypothesis `h : e = x`.
-/
meta def hgeneralize (h : parse ident?) (_ : parse $ tk ":") (p : parse generalize_arg_p) : tactic unit :=
propagate_tags $ let (p, x) := p in tactic.hgeneralize h p x

meta def trace_failure : itactic → tactic unit :=
tactic.trace_failure

end interactive
end tactic
