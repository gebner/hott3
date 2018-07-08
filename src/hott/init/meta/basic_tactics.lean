/-
Copyright (c) 2017 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
import ..path0 .instances

universes u v w

namespace name

meta def append_postfix : name → string → name
| (mk_string s p) s' := mk_string (s ++ s') p
| x               s' := x

end name

namespace expr

variable {elab : bool}
/-- returns a list of names, binder_info's and domains and the conclusion of the expression -/
meta def destruct_pis : expr elab → list name × list binder_info × list (expr elab) × expr elab
| (pi n bi a b) := let (ns, bis, es, e) := destruct_pis b in (n::ns, bi::bis, a::es, e)
| a             := ([], [], [], a)

instance inhabited_binder_info : inhabited binder_info :=
⟨binder_info.default⟩

open pexpr
meta def to_raw_pexpr : expr → pexpr
| (var n)                     := var n
| (sort l)                    := sort l
| (const nm ls)               := mk_explicit $ const nm ls
| (mvar n n' e)               := mvar n n' (to_raw_pexpr e)
| (local_const nm ppnm bi tp) := mk_explicit $ local_const nm ppnm bi (to_raw_pexpr tp)
| (app f a)                   := app (to_raw_pexpr f) (to_raw_pexpr a)
| (lam nm bi tp bd)           := lam nm bi (to_raw_pexpr tp) (to_raw_pexpr bd)
| (pi nm bi tp bd)            := pi nm bi (to_raw_pexpr tp) (to_raw_pexpr bd)
| (elet nm tp df bd)          := elet nm (to_raw_pexpr tp) (to_raw_pexpr df) (to_raw_pexpr bd)
| (macro md l)                := macro md (l.map to_raw_pexpr)

end expr open expr
namespace pexpr
meta def to_raw_expr : pexpr → expr
| (var n)                     := var n
| (sort l)                    := sort l
| (const nm ls)               := const nm ls
| (mvar n n' e)               := mvar n n' (to_raw_expr e)
| (local_const nm ppnm bi tp) := local_const nm ppnm bi (to_raw_expr tp)
| (app f a)                   := app (to_raw_expr f) (to_raw_expr a)
| (lam nm bi tp bd)           := lam nm bi (to_raw_expr tp) (to_raw_expr bd)
| (pi nm bi tp bd)            := pi nm bi (to_raw_expr tp) (to_raw_expr bd)
| (elet nm tp df bd)          := elet nm (to_raw_expr tp) (to_raw_expr df) (to_raw_expr bd)
| (macro md l)                := macro md (l.map to_raw_expr)

end pexpr

hott_theory

namespace tactic
open interaction_monad interaction_monad.result sum

/-- Executes t, on failure the tactic try_core_msg succeeds with the error message -/
meta def try_core_msg {α : Type _} (t : tactic α) : tactic (α ⊕ option (unit → format)) :=
λ s, result.cases_on (t s)
 (λ a, success $ inl a)
 (λ e ref s', success (inr e) s)

/-- Returns a if t returns (inl a), otherwise fails with message returned by t -/
meta def extract {α : Type _} (t : tactic $ α ⊕ option (unit → format)) : tactic α :=
do u ← t,
match u with
| inl a        := return a
| inr (some m) := fail $ m ()
| inr none     := failed
end


/-- executes t₂ when tactic t₁ fails. After t₂ is executed, do_on_failure fails with the error message given by t₂ -/
meta def do_on_failure {α : Type _} (t₁ : tactic α) (t₂ : format → tactic format) : tactic α :=
do r ← try_core_msg t₁,
match r with
| (inl a)        := return a
| (inr none)     := do u ← t₂ "", fail u
| (inr (some m)) := do u ← t₂ (m ()), fail u
end

/-- almost the same as t₁ <|> t₂. If t₂ returns value none, the tactic fails with error message from t₁ -/
meta def orelse_plus {α : Type _} (t₁ : tactic α) (t₂ : tactic $ option α) : tactic α :=
do r ← try_core_msg t₁,
match r with
| (inl a) := return a
| (inr e) := do u ← t₂, some a ← return u | (do some u ← return e, fail $ u ()), return a
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

/-- Binds local constant l in expression e. Infers the type of l for the binder type.
    Note: Does not instantiate metavariables, which might cause an incomplete abstraction. -/
meta def bind_lambda (l e : expr) : tactic expr :=
do t ← infer_type l,
local_const un ppn bi _ ← return l | fail $ to_fmt l ++ " is not a local constant.",
return $ lam (ppn.append_postfix "'") bi t (abstract_local e un)

/- Binds local constants in expression e. Instantiates metavariables of e. -/
meta def bind_lambdas : list expr → expr → tactic expr
| []      e := instantiate_mvars e
| (l::ls) e := do e' ← bind_lambdas ls e, bind_lambda l e'

constant suppress_bytecode_constant : unit

meta def suppress_bytecode : tactic unit :=
do u ← assertv `_ `(unit) `(suppress_bytecode_constant),
   refine ``((λ_xkcd, _) %%u),
   clear u, get_local `_xkcd >>= clear

namespace interactive

open lean lean.parser interactive interactive.types
local postfix `?`:9001 := optional

meta def fconstructor : tactic unit :=
tactic.fconstructor >> skip

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

meta def iapply (q : parse texpr) : tactic unit :=
i_to_expr_for_apply q >>= (λe, tactic.apply e {instances := ff}) >> all_goals (try apply_instance)

meta def suppress_bytecode : tactic unit :=
tactic.suppress_bytecode

end interactive
end tactic

namespace list
open tactic sum option
meta def mmap_filter {α : Type u} {β : Type v} (f : α → tactic (option β)) : list α → tactic (list β)
| []       := return []
| (x :: xs) := do oy ← f x, ys ← mmap_filter xs, some y ← return oy | return ys, return $ y :: ys

/-- Applies f to all elements of the list, until one of them returns (inl _). If f only returns (inr _) or fails this raises an error message which concatenates the returned messages. Discards messages of errors. Assumes that f always succeeds. -/
meta def mfirst_msg_core {α : Type w} {β : Type} (f : α → tactic (β ⊕ option (unit → format))) :
  list α → list (unit → format) → tactic β
| []      m := fail $ m.reverse.foldl (λm t, t () ++ "\n" ++ m) ""
| (a::as) m := (do x ← f a,
  match x with
  | inl b := return b
  | inr f := do some x' ← return f | mfirst_msg_core as m, mfirst_msg_core as (x'::m)
  end) <|> mfirst_msg_core as m

meta def mfirst_msg {α : Type w} {β : Type} (f : α → tactic (β ⊕ option (unit → format))) (l : list α) : tactic β :=
mfirst_msg_core f l []

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
