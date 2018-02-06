/-
Copyright (c) 2017 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Floris van Doorn

A tactic to infer truncatedness better than type-class inference.
-/
import .basic_tactics

namespace expr

/-- gives the arity of the type, i.e. the number of pi's in the expression -/
meta def arity : expr → ℕ
| (pi _ _ _ b) := arity b + 1
| e            := 0

end expr

namespace list
universes u v
variables {α : Type u} {β : Type v}

def replace_position : list α → ℕ → α → list α
| []       n     x := []
| (_::xs)  0     x := x::xs
| (x'::xs) (k+1) x := x'::replace_position xs k x

def position_aux : list α → (ℕ → α → bool) → ℕ → list ℕ
| []      f n := []
| (x::xs) f n := let ps := position_aux xs f (n+1) in if f n x then n::ps else ps

/-- gives a list of positions where f returns true. f is applied to the position and the element in that position -/
def position (l : list α) (f : ℕ → α → bool) : list ℕ :=
list.position_aux l f 0

def gen_position_aux : list α → (ℕ → α → list α → bool) → ℕ → list ℕ
| []      f n := []
| (x::xs) f n := let ps := gen_position_aux xs f (n+1) in if f n x xs then n::ps else ps

/-- gives a list of positions where f returns true. f is applied to the position, the element in that position, and the tail of the list -/
def gen_position (l : list α) (f : ℕ → α → list α → bool) : list ℕ :=
list.gen_position_aux l f 0

def any_indexed_aux : list α → (ℕ → α → bool) → ℕ → bool
| []      f n := ff
| (x::xs) f n := f n x || any_indexed_aux xs f (n+1)

def any_indexed : list α → (ℕ → α → bool) → bool :=
λxs f, any_indexed_aux xs f 0

def all_indexed_aux : list α → (ℕ → α → bool) → ℕ → bool
| []      f n := tt
| (x::xs) f n := f n x && all_indexed_aux xs f (n+1)

def all_indexed : list α → (ℕ → α → bool) → bool :=
λxs f, all_indexed_aux xs f 0

def map_indexed_aux : list α → (ℕ → α → β) → ℕ → list β
| []      f n := []
| (x::xs) f n := f n x::map_indexed_aux xs f (n+1)

/-- maps the function to both the position and the element in that position -/
def map_indexed : list α → (ℕ → α → β) → list β :=
λxs f, map_indexed_aux xs f 0

/-- Splits the list at position n. Pads the first output list by x₀'s to ensure it has length n. -/
def split_pad (x₀ : α) : ℕ → list α → list α × list α
| 0     xs      := ([], xs)
| (n+1) []      := (repeat x₀ (n+1), [])
| (n+1) (x::xs) := let (ys, zs) := split_pad n xs in (x::ys, zs)

/-- Splits the first list into a list of lists with lengths indicated by the second list.
  If the first list is too long, the remainder is ignored.
  If the list is too short, the result is padded by the element `x₀`  -/
def splits_pad (x₀ : α) : list α → list ℕ → list (list α)
| xs []      := []
| xs (n::ns) := let (ys, zs) := split_pad x₀ n xs in ys::splits_pad zs ns

end list

namespace option
universes u v w
variables {α : Type u} {β : Type v}

def any : option α → (α → bool) → bool
| (some x) f := f x
| none f     := ff

def all : option α → (α → bool) → bool
| (some x) f := f x
| none f     := tt

end option

namespace tactic

open environment lean.parser expr pexpr sum

variable {elab : bool}

declare_trace hinduction
private meta def mtac (t : tactic unit) : tactic unit :=
when_tracing `hinduction t
private meta def mtrace (msg : format) : tactic unit :=
mtac $ trace msg
private meta def mfail {α : Type _} (msg : format) : tactic α :=
mtrace msg >> fail msg

structure induction_info :=
  (nargs : ℕ) /- the number of arguments of the recursor -/
  (motive : ℕ) /- the head of the conclusion of the recursor -/
  (minor_premises : list ℕ)
    /- the hypotheses depending on the motive which are not type class instances -/
  (minor_premise_arity : list ℕ) /- the arity of these -/
  (type_class_premises : list ℕ)
    /- the hypotheses depending on the motive which are type class instances -/
  (major_premise : ℕ)
  (target : name) /- the head of the major premise -/
  (dependent : bool) /- whether the major premise occurs in the conclusion -/
  (indices : list ℕ) /- The indices are the variables to which the motive is applied in the
    conclusion, excluding the major premise -/
  (indices_in_major_premise : list ℕ)
    /- Position where the indices occur in the type of the major premise.
    If a index occurs more than once, then only the first occurrence is recorded.
    In this case, when applying the recursor, we don't check that the same variable occurs in
    these places, if that is not the case, we might get a confusing error message -/
  (params : list ℕ)  /- the parameters are the other arguments of the induction principle -/
  (params_in_major_premise : list ℕ) /- Position where the parameters occurs in the type of the
    major premise. See remarks from indices -/

meta def get_induction_info (nm : name) : tactic expr :=
do let info_name := mk_str_name nm "_ind_info",
env ← get_env,
if env.contains info_name then declaration.value <$> env.get info_name >>= return else do
t ← mk_const nm >>= infer_type,
let (_, binders, args, c) := destruct_pis t,
let len_args : ℕ := args.length,
var mot ← return $ get_app_fn c | fail "Conclusion doesn't have a variable as head",
let motive := len_args - mot - 1,
/- the minor premises are all arguments whose type depends on the motive -/
let pre_min_prem := args.position $ λn e, to_bool (n > motive) && e.has_var_idx (n - motive - 1),
let (type_class_prem, min_prem) :=
  pre_min_prem.partition (λk, (binders.nth k).iget = binder_info.inst_implicit),
let min_prem_arity := min_prem.map $ λk, (args.nth k).iget.arity,
/- l₁ is the list of arguments where minor premises are replaced by none -/
let l₁ := args.map_indexed $ λn e, if min_prem.mem n then none else some e,
/- l₂ is the list of "major premises": the list of non-minor premises which do not occur in a later
  argument which is not a minor premise, which are not the motive and do not occur in the motive -/
let l₂ := l₁.gen_position $ λn' oe' es,
  to_bool (oe' ≠ none ∧ n' ≠ motive ∧
    (n' < motive ∨ (oe'.any $ λe', bnot $ e'.has_var_idx (n' - motive - 1)))) &&
    (es.all_indexed $ λn oe, bnot $ oe.any $ λe, e.has_var_idx n),
[maj_prem] ← return l₂ |
  (if l₂ = [] then fail $ to_fmt "No major premise found. Positions of minor premises: " ++
    to_fmt (min_prem.map (+1)) else
  fail $ to_fmt "Multiple major premises found at positions " ++ to_fmt (l₂.map (+1)) ++
    ". Side conditions or mutual induction is not supported. Positions of minor premises: " ++
    to_fmt min_prem),
tmaj ← args.nth maj_prem,
const tgt _ ← return $ get_app_fn tmaj | fail $
  to_fmt "Invalid type of major premise (at position " ++ to_fmt (maj_prem+1) ++
  "). The head is not a constant or definition.",
when (min_prem.any $ λk, to_bool (k > maj_prem) &&
  (args.nth k).iget.has_var_idx (k - maj_prem - 1)) $
    fail $ to_fmt "Some minor premises depend on major premise. Minor premises: " ++
      to_fmt (min_prem.map (+1)) ++ ", major premise: " ++ to_fmt (maj_prem+1),
let dep := c.has_var_idx (len_args - maj_prem - 1),
let mot_args := get_app_args c,
indices_or_maj_prem ← mot_args.mmap (λe, do var ve ← return e |
  fail "Motive is applied to arguments which are not variables.",
  return $ len_args - ve - 1),
maj_prem_arg_vars ← (get_app_args tmaj).mmap (λe, try_core $ do var ve ← head_eta e, return ve),
mtrace $ to_fmt maj_prem_arg_vars,
let indices := if dep then indices_or_maj_prem.init else indices_or_maj_prem,
indices_in_major_premise ← indices.mmap (λn, do
  let l := maj_prem_arg_vars.position $ λpos var, to_bool $ var = some (maj_prem - n - 1),
  mpos::_ ← return l | fail $
    to_fmt "The index at position " ++ to_fmt (n+1) ++ " is not an argument of the major premise.",
  return $ mpos),
let params := (list.range len_args).filter $
  λk, k ≠ motive ∧ k ≠ maj_prem ∧ ¬pre_min_prem.mem k ∧ ¬indices.mem k,
params_in_major_premise ← params.mmap (λn, do
  let l := maj_prem_arg_vars.position $ λpos var, to_bool $ var = some (maj_prem - n - 1),
  mpos::_ ← return l | fail $ to_fmt "The parameter at position " ++ to_fmt (n+1) ++
    " is not an argument of the major premise.",
  return $ mpos),
let e := `(induction_info.mk %%(reflect len_args) %%(reflect motive) %%(reflect min_prem)
  %%(reflect min_prem_arity) %%(reflect type_class_prem) %%(reflect maj_prem) %%(reflect tgt)
  %%(reflect dep) %%(reflect indices) %%(reflect indices_in_major_premise) %%(reflect params)
  %%(reflect params_in_major_premise)),
add_decl $ mk_definition info_name [] `(induction_info) e,
return e

@[user_attribute] meta def induction_attribute : user_attribute :=
{ name      := `induction,
  descr     := "HoTT attribute for induction principles",
  after_set := some $ λ n _ _, get_induction_info n >> skip }

meta def get_rec_info (nm : name) : expr :=
expr.const (mk_str_name nm "_ind_info") []

/- to do: [later] add support for let-expressions (in revert_kdeps) -/
/- t is the type of h, possiby unfolded -/
meta def hinduction_core (h t : expr) (rec : name) (ns : list name) (info : expr) : tactic unit :=
focus1 $ do
induction_info.mk nargs motive_pos _/-minor_premise position-/ mp_ar _/-type class premises-/
  maj_prem_pos _/-target-/ dep index_pos index_pos_maj params_pos params_pos_maj ←
    eval_expr induction_info info,
let t_args := get_app_args t,
indices : list expr ← index_pos_maj.mmap $ λk, (do
  e ← whnf (t_args.nth k).iget,
  local_const _ _ _ _ ← return e | pp e >>= λmsg, mfail
  (to_fmt "Invalid recursor application with indices. There is an index which doesn't occur as variable in the type of major premise.\nSolution: generalize expression\n" ++ msg),
  return e),
mtrace $ to_fmt "indices: " ++ to_fmt indices,
let params : list expr := params_pos_maj.map $ λk, (t_args.nth k).iget,
reverts : list ℕ ← indices.mmap $ λe, (do
  revs ← kdependencies e,
  revert_lst $ revs.filter (λx, x ≠ h ∧ ¬indices.mem x)),
mtrace $ to_fmt "reverts: " ++ to_fmt (list.foldr nat.add 0 reverts),
t ← target,
crec ← mk_explicit <$> to_pexpr <$> mk_const rec,
let indices_plus := if dep then indices.append [h] else indices,
mot ← bind_lambdas indices_plus t,
pp t >>= λm, mtrace $ to_fmt "target: " ++ m,
pp mot >>= λm, mtrace $ to_fmt "motive: " ++ m,
let mot' := to_pexpr mot,
/- a list with placeholders, with the major premise and motive filled in-/
let flist : list pexpr :=
  ((list.repeat mk_placeholder nargs).replace_position maj_prem_pos (to_pexpr h)).replace_position
    motive_pos mot',
/- also fill in the indices -/
let flist₂ : list pexpr :=
  (list.zip index_pos indices).foldl (λe ⟨n, e'⟩, e.replace_position n $ to_pexpr e') flist,
/- also fill in the parameters -/
let flist₃ : list pexpr :=
  (list.zip params_pos params).foldl (λe ⟨n, e'⟩, e.replace_position n $ to_pexpr e') flist,
mtrace $ to_fmt "List of arguments: " ++ to_fmt flist₃,
let fapp : pexpr := flist₃.foldl app crec,
-- mtrace $ to_fmt "Raw format of the application: " ++ to_raw_fmt fapp,
efapp ← (to_expr ``(%%fapp : %%t)).do_on_failure $
  λmsg, (let msg' : format := "Induction tactic failed. Recursor is not applicable.\n" ++ msg in
    mtrace msg' >> return msg'),
type_check efapp <|> pp efapp >>= λm, mfail $
  to_fmt "Incorrect recursor application.\nRecursors with indices might still be buggy.\n" ++
    "Possible solution: reduce the type of indices with dsimp.\n" ++ m,
mtrace $ to_fmt "Elaborated application: " ++ to_fmt efapp,
exact efapp,
(all_goals $ clear h) <|> mfail
  ("Couldn't clear major premise from context after applying the induction principle.\n" ++
   "Possible solution: generalize all let-expressions where the major premise occurs."),
(all_goals $ indices.reverse.mmap' clear) <|> mfail
  "Couldn't clear indices from context after applying the induction principle.",
ng ← num_goals,
guard (mp_ar.length = ng) <|> mfail "Unreachable(?) code: wrong number of minor premises",
let names := ns.splits_pad `_ mp_ar,
focus $ names.map $ λnms, intro_lst nms >> skip,
(all_goals $ reverts.mmap' intron) <|> mfail
  "Couldn't reintroduce hypotheses which depend on indices."
  -- to do: only do this if minor premise has as conclusion the motive

/- t is the type of h, possiby unfolded, ht is the head of t, dept is whether the target depends
   on h -/
meta def hinduction_using (h t : expr) (ht : name) (dept : bool) (nm : name) (ns' : list name) :
  tactic (unit ⊕ option (unit → format)) :=
do rec_info ← get_induction_info nm <|> mfail (to_fmt "Invalid recursor " ++ to_fmt nm),
tgt ← eval_expr name $ expr.app `(induction_info.target) rec_info,
is_dept_rec ← eval_expr bool $ expr.app `(induction_info.dependent) rec_info,
guard (tgt = ht) <|> mfail (to_fmt "Recursor " ++ to_fmt nm ++
  " is not applicable. The head of the induction variable is " ++ to_fmt ht ++
  ", but the target of the induction principle is " ++ to_fmt tgt),
if bnot dept || is_dept_rec then skip else mfail
  (to_fmt "Invalid recursor. " ++ to_fmt nm ++ " is not recursive"),
try_core_msg $ hinduction_core h t nm ns' rec_info

/- t is the type of h, possiby unfolded -/
meta def hinduction (h t : expr) (rec : option name) (ns' : list name) : tactic unit :=
do const ht _ ← return $ get_app_fn t | mfail $ to_fmt "Invalid major premise " ++ to_fmt h ++
  ". The head of its type is not a constant or definition.",
dept ← target >>= λtgt, kdepends_on tgt h,
match rec with
| some nm := extract $ hinduction_using h t ht dept nm ns'
| none    := do
  ns₂ ← attribute.get_instances `induction,
  -- to do: use rb_map to filter induction principles more quickly!?
  let hrec := mk_str_name ht "rec",
  env ← get_env,
  ns ← if env.contains hrec
       then (has_attribute `induction hrec >> return ns₂) <|> return (ns₂ ++ [hrec])
       else return ns₂,
  ns.mfirst_msg $ λnm, mtrace (to_fmt "Trying " ++ to_fmt nm) >> hinduction_using h t ht dept nm ns'
end

/-- tries to apply hinduction, but if it fails, applies whnf to the type of h and tries again -/
meta def hinduction_whnf (h : expr) (rec : option name) (ns' : list name) : tactic unit :=
do t ← infer_type h,
(hinduction h t rec ns').orelse_plus $
do t' ← whnf t, if t = t' then return none
else mtrace "Applying whnf to major premsie" >> some <$> hinduction h t' rec ns'

meta def hinduction_or_induction (h : expr) (rec : option name) (ns : list name) : tactic unit :=
hinduction_whnf h rec ns <|> induction' h ns rec

/- If h is a local constant, reverts all local constants which have h in their type.
   Otherwise, generalizes h to local constant h' and adds equality H : h' = h, where H is the head
   of ns (if non-empty). Then applies tactic tac. tac is only applied to a local constant which
   doesn't occur in the type of other local constants.
   After tac is executed, introduces generalized hypotheses.
-/
meta def ind_generalize (h : expr) (ns : list name := []) (tac : expr → list name → tactic unit) : tactic unit :=
match h with
| (local_const _ _ _ _) :=
  do n ← revert_kdeps h,
     tac h ns,
     all_goals $ try $ intron n -- to do: only do this if minor premise has as conclusion the motive
| _ := /- The block "generalize major premise args" in the induction tactic is for inductive
  families only(?) and only rarely useful -/
  do x ← mk_fresh_name, /- to do: let the user decide whether to use ginduction or induction here -/
  let (nm, nms) := (match ns with
  | []        := (`_h, [])
  | nm :: nms := (nm, nms)
  end : name × list name),
  hgeneralize (some nm) (to_pexpr h) x,
  t ← get_local x,
  pt ← get_local nm,
  revert pt,
  tac t nms,
  all_goals $ try $ intro1
end

namespace interactive

open expr interactive.types lean.parser tactic interactive
local postfix `?`:9001 := optional
local postfix *:9001 := many

/- To do: allow hinduction 1 and maybe hinduction to a variable yet to be intro'd -/
/- to do: eta-reduce (and maybe more reductions) to variables, so that `(λx, B x)`
   is recognized as parameter `B` -/

/-- Applies induction to p. Works also for HoTT-induction principles which may not eliminate into
    Prop.
    -/
meta def hinduction (p : parse texpr) (rec_name : parse using_ident) (ids : parse with_ident_list)
  (revert : parse $ (tk "generalizing" *> ident*)?) : tactic unit :=
focus1 $ do e ← i_to_expr p,
rec : option name ← rec_name.mmap resolve_constant,
n ← mmap tactic.get_local (revert.get_or_else []) >>= revert_lst,
ind_generalize e ids $ λe' ns', tactic.hinduction_whnf e' rec ns',
all_goals $ intron n -- to do: only do this if minor premise has as conclusion the motive

/-- Similar to hinduction, but tries the usual induction principle first if hinduction fails -/
meta def hinduction_plus (p : parse texpr) (rec_name : parse using_ident) (ids : parse with_ident_list)
  (revert : parse $ (tk "generalizing" *> ident*)?) : tactic unit :=
focus1 $ do e ← i_to_expr p,
rec : option name ← rec_name.mmap resolve_constant,
n ← mmap tactic.get_local (revert.get_or_else []) >>= revert_lst,
ind_generalize e ids $ λe' ns', tactic.hinduction_or_induction e' rec ns',
all_goals $ intron n -- to do: only do this if minor premise has as conclusion the motive

end interactive

end tactic
