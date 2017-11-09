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

open environment lean.parser expr pexpr

variable {elab : bool}

/- this doesn't work -/
-- meta def check_consistency : tactic unit :=
-- do r ← result, type_check r

structure induction_info :=
  (nargs : ℕ) /- the number of arguments of the recursor -/
  (motive : ℕ) /- the head of the conclusion of the recursor -/
  (minor_premises : list ℕ) /- the hypotheses depending on the motive which are not type class instances -/
  (minor_premise_arity : list ℕ) /- the arity of these -/
  (type_class_premises : list ℕ) /- the hypotheses depending on the motive which are type class instances -/
  (major_premise : ℕ)
  (target : name) /- the head of the major premise -/
  (dependent : bool) /- whether the major premise occurs in the conclusion -/
  (indices : list ℕ) /- The indices are the variables to which the motive is applied in the conclusion, other than the major premise -/
  (indices_in_major_premise : list ℕ) /- Position where the indices occur in the type of the major premise. 
    If a index occurs more than once, then only the first occurrence is recorded. 
    In this case, when applying the recursor, we don't check that the same variable occurs in these places, 
    if that is not the case, we might get a confusing error message -/

-- meta instance : has_to_format induction_info :=
-- ⟨λH, to_fmt "#args: " ++ to_fmt H.nargs ++ "; pos. motive:  " ++ H.motive ++ "; and more."⟩

/- To do: allow hinduction 1 and maybe hinduction to a variable yet to be intro'd -/
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
let (type_class_prem, min_prem) := pre_min_prem.partition (λk, (binders.nth k).iget = binder_info.inst_implicit),
let min_prem_arity := min_prem.map $ λk, (args.nth k).iget.arity,
/- l₁ is the list of arguments where minor premises are replaced by none -/
let l₁ := args.map_indexed $ λn e, if min_prem.mem n then none else some e,
/- l₂ is the list of "major premises": the list of non-minor premises which do not occur in a later argument which is not a minor premise, 
  which are not the motive and do not occur in the motive -/
let l₂ := l₁.gen_position $ λn' oe' es, 
  to_bool (oe' ≠ none ∧ n' ≠ motive ∧ (n' < motive ∨ (oe'.any $ λe', bnot $ e'.has_var_idx (n' - motive - 1)))) && 
  (es.all_indexed $ λn oe, bnot $ oe.any $ λe, e.has_var_idx n),
[maj_prem] ← return l₂ | 
  (if l₂ = [] then fail $ to_fmt "No major premise found. Positions of minor premises: " ++ to_fmt (min_prem.map (+1)) else 
  fail $ to_fmt "Multiple major premises found at positions " ++ to_fmt (l₂.map (+1)) ++ 
    ". Side conditions or mutual induction is not supported. Positions of minor premises: " ++ to_fmt min_prem), 
tmaj ← args.nth maj_prem,
const tgt _ ← return $ get_app_fn tmaj | fail $ to_fmt "Invalid type of major premise (at position " ++ to_fmt (maj_prem+1) ++ 
  "). The head is not a constant or definition.",
if min_prem.any $ λk, to_bool (k > maj_prem) && (args.nth k).iget.has_var_idx (k - maj_prem - 1) 
  then fail $ to_fmt "Some minor premises depend on major premise. Minor premises: " ++ to_fmt (min_prem.map (+1)) ++ 
    ", major premise: " ++ to_fmt (maj_prem+1) 
  else skip,
let dep := c.has_var_idx (len_args - maj_prem - 1),
let mot_args := get_app_args c,
indices_or_maj_prem ← mot_args.mmap (λe, do var ve ← return e | fail "Motive is applied to arguments which are not variables.", 
  return $ len_args - ve - 1),
maj_prem_args ← return $ get_app_args tmaj,
maj_prem_arg_vars ← maj_prem_args.mmap (λe, try_core $ do var ve ← return e, return ve),
let indices := if dep then indices_or_maj_prem.init else indices_or_maj_prem,
indices_in_major_premise ← indices.mmap (λn, do
  let l := maj_prem_arg_vars.position $ λpos var, to_bool $ var = some (maj_prem - n - 1),
  mpos::_ ← return l | fail $ to_fmt "The index at position " ++ to_fmt (n+1) ++ " is not an argument of " ++ to_fmt tgt,
  return $ mpos),
let e := `(induction_info.mk %%(reflect len_args) %%(reflect motive) %%(reflect min_prem) %%(reflect min_prem_arity)
  %%(reflect type_class_prem) %%(reflect maj_prem) %%(reflect tgt) %%(reflect dep) %%(reflect indices) %%(reflect indices_in_major_premise)),
add_decl $ mk_definition info_name [] `(induction_info) e,
return e

declare_trace hinduction
private meta def mtrace (msg : format) : tactic unit := 
when_tracing `hinduction $ trace msg
private meta def mfail {α : Type _} (msg : format) : tactic α := 
mtrace msg >> fail msg

@[user_attribute] meta def induction_attribute : user_attribute :=
{ name      := `induction,
  descr     := "HoTT attribute for induction principles",
  after_set := some $ λ n _ _, get_induction_info n >> return () }

meta def get_rec_info (nm : name) : expr :=
expr.const (mk_str_name nm "_ind_info") []

-- meta def pexpr_bind_lambda (e : expr) : expr → pexpr
-- | (local_const n pp_n bi _) := lam pp_n bi mk_placeholder $ to_pexpr $ e.abstract_local n
-- | _                         := to_pexpr e

/- TODO: [later] add support for let-expressions (in revert_kdeps) -/
meta def hinduction_core (h : expr) (rec : name) (ns : list name) (info : expr) : tactic unit :=
focus1 $ do 
nargs ← eval_expr ℕ `(induction_info.nargs %%info),
maj_prem_pos ← eval_expr ℕ `(induction_info.major_premise %%info),
motive_pos ← eval_expr ℕ `(induction_info.motive %%info),
mp_ar ← eval_expr (list ℕ) `(induction_info.minor_premise_arity %%info),
--indices ← eval_expr (list ℕ) `(induction_info.indices %%info),
index_pos ← eval_expr (list ℕ) `(induction_info.indices_in_major_premise %%info),
th ← infer_type h,
let th_args := get_app_args th,
(indices, reverts) ← list.unzip.{0 0} <$> (index_pos.mmap $ λk, (do 
  let e := (th_args.nth k).iget,
  local_const _ _ _ _ ← return e | mfail "Invalid recursor application with indices. There is an index which doesn't occur as variable in the type of major premise.", 
  revs ← kdependencies e, 
  k ← revert_lst $ revs.filter (≠ h),
  return (e, k))),
t ← target,
crec ← mk_explicit <$> to_pexpr <$> mk_const rec,
-- let mot := to_pexpr $ indices.reverse.foldl bind_lambda t,
-- trace mot,
let flist : list pexpr := ((list.repeat mk_placeholder nargs).replace_position maj_prem_pos (to_pexpr h)).replace_position motive_pos mk_placeholder,
let fapp : pexpr := flist.foldl app crec,
-- trace fapp,
efapp ← (to_expr ``(%%fapp : %%t) tt).do_on_failure $
  λmsg, let msg' : format := "Induction tactic failed. Recursor is not applicable.\n" ++ msg in mtrace msg' >> return msg',
-- trace "foo",
type_check efapp <|> mfail (to_fmt "Incorrect recursor application.\nRecursors with indices are not yet supported.\n" ++ to_fmt efapp),
exact efapp,
/- to do[indices]: clear indices -/
(all_goals $ clear h) <|> mfail "Couldn't clear major premise from context after applying the induction principle.\nPossible solution: generalize all let-expressions where the major premise occurs.",
(all_goals $ indices.mmap' clear) <|> mfail "Couldn't clear indices from context after applying the induction principle.",
reverts.mmap' intron,
ng ← num_goals,
guard (mp_ar.length = ng) <|> mfail "Unreachable(?) code: wrong number of minor premises",
let names := ns.splits_pad `_ mp_ar,
focus $ names.map $ λnms, intro_lst nms >> return ()

meta def hinduction_using (h : expr) (nm : name) (ns' : list name) : tactic unit :=
do t ← infer_type h,
const ht _ ← return $ get_app_fn t | mfail $ to_fmt "Invalid major premise " ++ to_fmt h ++ ". The head of its type is not a constant or definition.",
dept ← target >>= λtgt, kdepends_on tgt h,
rec_info ← get_induction_info nm,
tgt ← eval_expr name $ expr.app `(induction_info.target) rec_info,
is_dept_rec ← eval_expr bool $ expr.app `(induction_info.dependent) rec_info,
guard $ tgt = ht,
if dept && bnot is_dept_rec then mfail $ to_fmt "Invalid recursor. " ++ to_fmt nm ++ " is not recursive" else hinduction_core h nm ns' rec_info

meta def hinduction (h : expr) (rec : option name) (ns' : list name) : tactic unit :=
match rec with
| (some nm) := hinduction_using h nm ns'
| none        := do
  t ← infer_type h,
  const ht _ ← return $ get_app_fn t | fail $ to_fmt "Invalid major premise " ++ to_fmt h ++ ". The head of its type is not a constant or definition.",
  dept ← target >>= λtgt, kdepends_on tgt h,
  ns ← attribute.get_instances `induction, -- to do: use rb_map to filter induction principles more quickly!?
  env ← get_env,
  (ns.mfirst $ λnm, do { mtrace $ to_fmt "Trying " ++ to_fmt nm,
    let info := get_rec_info nm,
    tgt ← eval_expr name `(induction_info.target %%info),
    guard (tgt = ht) <|> mfail "Wrong major premise.",
    is_dept_rec ← eval_expr bool `(induction_info.dependent %%info),
    guard (bnot dept || is_dept_rec) <|> mfail "Recursor is not dependent.",
    hinduction_core h nm ns' info }) <|> 
  (let hrec := mk_str_name ht "rec" in 
    if env.contains $ hrec then mtrace (to_fmt "Trying default rec " ++ to_fmt hrec) >> hinduction_using h hrec ns' 
    else mfail $ to_fmt hrec ++ " doesn't exist.") <|> 
  fail "No induction principle found for this major premise."
end

meta def hinduction_or_induction (h : expr) (rec : option name) (ns : list name) : tactic unit :=
induction' h ns rec -- >> (check_consistency <|> trace "normal induction failed" >> failed) 
<|> hinduction h rec ns

/- If h is a local constant, reverts all local constants which have h in their type. 
   Otherwise, generalizes h to local constant h' and adds equality H : h' = h, where H is the head of ns (if non-empty).
   Then applies tactic tac. tac is only applied to a local constant which doesn't occur in the type of other local constants.
   After tac is executed, introduces generalized hypotheses.
-/
meta def ind_generalize (h : expr) (ns : list name := []) (tac : expr → list name → tactic unit) : tactic unit :=
match h with
| (local_const _ _ _ _) := 
  do n ← revert_kdeps h,
     tac h ns,
     all_goals $ try $ intron n /- to do: maybe do something better here: it depends on the type of the minor premise whether we can introduce reverted hypotheses -/
| _ := /- The block "generalize major premise args" in the induction tactic is for inductive families only(?) and only rarely useful -/
  do x ← mk_fresh_name, /- to do: let the user decide whether to use ginduction or induction here -/
  let (nm, nms) := (match ns with
  | []        := (`_h, [])
  | (nm :: nms) := (nm, nms)
  end : name × list name),
  interactive.generalize (some nm) (to_pexpr h, x),
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

/-- Applies induction to p. Works also for HoTT-induction principles which may not eliminate into Prop. 
    First tries the usual induction principle, and if that fails (or produces a type incorrect result)
    tries the new induction principle, which relaxes many conditions of the usual induction principle.
    -/
meta def hinduction (p : parse texpr) (rec_name : parse using_ident) (ids : parse with_ident_list)
  (revert : parse $ (tk "generalizing" *> ident*)?) : tactic unit :=
focus1 $ do e ← i_to_expr p,
rec : option name ← rec_name.mmap resolve_constant,
n ← mmap tactic.get_local (revert.get_or_else []) >>= revert_lst,
ind_generalize e ids $ λe' ns', tactic.hinduction_or_induction e' rec ns',
all_goals $ intron n

/-- Similar to hinduction, but doesn't try the usual induction principle first -/
meta def hinduction_only (p : parse texpr) (rec_name : parse using_ident) (ids : parse with_ident_list)
  (revert : parse $ (tk "generalizing" *> ident*)?) : tactic unit :=
focus1 $ do e ← i_to_expr p,
rec : option name ← rec_name.mmap resolve_constant,
n ← mmap tactic.get_local (revert.get_or_else []) >>= revert_lst,
ind_generalize e ids $ λe' ns', tactic.hinduction e' rec ns',
all_goals $ intron n

end interactive

end tactic


