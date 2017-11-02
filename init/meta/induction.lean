/-
Copyright (c) 2017 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Floris van Doorn

A tactic to infer truncatedness better than type-class inference.
-/
import .basic_tactics

namespace expr

/-- gives the arity of the type, i.e. the number of pi's in the expression -/
meta def arity : expr → nat
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

/-- Splits the list at position n. Pads the first output list by x's to ensure it has length n. -/
def split_pad (x₀ : α) : ℕ → list α → list α × list α
| 0     xs      := ([], xs)
| (n+1) []      := (repeat x₀ (n+1), [])
| (n+1) (x::xs) := let (ys, zs) := split_pad n xs in (x::ys, zs)

/-- Splits the first list into a list of lists with lengths indicated by the second list. 
  If the first list is too long, the remainder is ignored. 
  If the list is too short, the result is padded by the element `x`  -/
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
  (nargs : ℕ)
  (motive : ℕ)
  (minor_premises : list ℕ)
  (minor_premise_arity : list ℕ)
  (major_premise : ℕ)
  (target : name) /- the head of the major premise -/
  (dependent : bool) /- whether the major premise occurs in the conclusion -/

meta instance : has_to_format induction_info :=
⟨λH, to_fmt "#args: " ++ to_fmt H.nargs ++ "; pos. motive:  " ++ H.motive ++ "; etc."⟩

/- To do: allow hinduction 1 and maybe hinduction to a variable yet to be intro'd -/
meta def get_induction_info (nm : name) : tactic expr :=
do let info_name := mk_str_name nm "_ind_info",
env ← get_env,
if env.contains info_name then declaration.value <$> env.get info_name >>= return else do
t ← mk_const nm >>= infer_type,
let (args, c) := destruct_pis t,
let len_args : ℕ := args.length,
var mot ← return $ get_app_fn c | fail "Conclusion doesn't have a variable as head",
let motive := len_args - mot - 1,
-- NTS: don't check for indices this way, but check how the motive is applied to arguments other than the major premise
-- if motive_arity > 1 then fail $ "induction principles with indices are currently not supported" else skip,
/- the minor premises are all arguments whose type depends on the motive -/
let min_prem := args.position $ λn e, to_bool (n > motive) && e.has_var_idx (n - motive - 1),
let min_prem_arity := min_prem.map $ λk, ((args.nth k).get_or_else (default expr)).arity,
/- l₁ is the list of arguments where minor premises are replaced by none -/
let l₁ := args.map_indexed $ λn e, if min_prem.mem n then none else some e,
/- l₂ is the list of "major premises": the list of non-minor premises which do not occur in a later argument which is not a minor premise, 
  which are not the motive and do not occur in the motive -/
let l₂ := l₁.gen_position $ λn' oe' es, 
  to_bool (oe' ≠ none ∧ n' ≠ motive ∧ (n' < motive ∨ (oe'.any $ λe', bnot $ e'.has_var_idx (n' - motive - 1)))) && 
  (es.all_indexed $ λn oe, bnot $ oe.any $ λe, e.has_var_idx n),
[maj_prem] ← return l₂ | 
  (do [] ← return l₂ | 
    fail $ to_fmt "Multiple major premises found at positions " ++ to_fmt (l₂.map (+1)) ++ 
      ". This is currently not supported. Positions of minor premises: " ++ to_fmt min_prem, 
    fail $ to_fmt "No major premise found. Positions of minor premises: " ++ to_fmt (min_prem.map (+1))), 
tmaj ← args.nth maj_prem,
const tgt _ ← return $ get_app_fn tmaj | fail $ to_fmt "Invalid type of major premise (at position " ++ to_fmt (maj_prem+1) ++ 
  "). The head is not a constant or definition.",
if min_prem.any $ λk, to_bool (k > maj_prem) && ((args.nth k).get_or_else (default expr)).has_var_idx (k - maj_prem - 1) 
  then fail $ to_fmt "Some minor premises depend on major premise. Minor premises: " ++ to_fmt (min_prem.map (+1)) ++ 
    ", major premise: " ++ to_fmt (maj_prem+1) 
  else skip,
let dep := c.has_var_idx (len_args - maj_prem - 1),
let e := `(induction_info.mk %%(reflect len_args) %%(reflect motive) %%(reflect min_prem) %%(reflect min_prem_arity)
  %%(reflect maj_prem) %%(reflect tgt) %%(reflect dep)),
add_decl $ mk_definition info_name [] `(induction_info) e,
return e

@[user_attribute] meta def induction_attribute : user_attribute :=
{ name      := `induction,
  descr     := "HoTT attribute for induction principles",
  after_set := some $ λ n _ _, get_induction_info n >> return () }

meta def get_rec_info (nm : name) : expr :=
expr.const (mk_str_name nm "_ind_info") []

/- TODO: [later] add support for let-expressions (in revert_kdeps) -/
meta def hinduction_core (h : expr) (rec : name) (ns : list name) (info : expr) : tactic unit :=
focus1 $ 
do 
-- eval_expr induction_info info >>= trace,
nargs ← eval_expr nat `(induction_info.nargs %%info),
maj_prem_pos ← eval_expr nat `(induction_info.major_premise %%info),
motive_pos ← eval_expr nat `(induction_info.motive %%info),
mp_ar ← eval_expr (list nat) `(induction_info.minor_premise_arity %%info),
t ← target,
crec : pexpr ← mk_explicit <$> to_pexpr <$> mk_const rec,
/- to do: replace motive -/
let flist : list pexpr := ((list.repeat mk_placeholder nargs).replace_position maj_prem_pos (to_pexpr h)).replace_position motive_pos mk_placeholder,
let fapp : pexpr := flist.foldl app crec,
efapp ← change_failure (to_expr ``(%%fapp : %%t) tt) (λmsg, "Induction tactic failed. Recursor is not applicable.\n" ++ msg),
type_check efapp <|> (fail $ "Incorrect recursor application.\nRecursors with indices are not yet supported."),
exact efapp,
/- to do[indices]: clear indices -/
(all_goals $ clear h) <|> fail "Couldn't clear major premise from context after applying the induction principle.\nPossible solution: generalize all let-expressions where the major premise occurs.",
ng ← num_goals,
guard (mp_ar.length = ng) <|> fail "error: wrong number of minor premises",
let names := ns.splits_pad `_ mp_ar,
focus $ names.map $ λnms, intro_lst nms >> return ()

meta def hinduction_using (h : expr) (nm : name) (ns' : list name) : tactic unit :=
do 
t ← infer_type h,
const ht _ ← return $ get_app_fn t | fail $ to_fmt "Invalid major premise " ++ to_fmt h ++ ". The head of its type is not a constant or definition.",
dept ← target >>= λtgt, kdepends_on tgt h,
rec_info ← get_induction_info nm,
tgt ← eval_expr name $ expr.app `(induction_info.target) rec_info,
is_dept_rec ← eval_expr bool $ expr.app `(induction_info.dependent) rec_info,
guard $ tgt = ht,
if dept && bnot is_dept_rec then fail $ to_fmt "Invalid recursor. " ++ to_fmt nm ++ " is not recursive" else hinduction_core h nm ns' rec_info

meta def hinduction (h : expr) (rec : option name) (ns' : list name) : tactic unit :=
do 
match rec with
| (some nm) := hinduction_using h nm ns'
| none        := do
  t ← infer_type h,
  const ht _ ← return $ get_app_fn t | fail $ to_fmt "Invalid major premise " ++ to_fmt h ++ ". The head of its type is not a constant or definition.",
  dept ← target >>= λtgt, kdepends_on tgt h,
  ns ← attribute.get_instances `induction, -- to do: use rb_map to filter induction principles more quickly!?
  env ← get_env,
  (if env.contains $ mk_str_name ht "rec" then hinduction_using h (mk_str_name ht "rec") ns' else skip) <|>
  (ns.mfirst $ λnm, do {
    let info := get_rec_info nm,
    tgt ← eval_expr name `(induction_info.target %%info),
    guard $ tgt = ht,
    is_dept_rec ← eval_expr bool `(induction_info.dependent %%info),
    guard $ bnot dept || is_dept_rec,
    hinduction_core h nm ns' info }) <|> fail "No induction principle found for this major premise"
    /- to do: try ht.rec if it exists -/
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
  do x ← mk_fresh_name,
  let (nm, nms) := (match ns with
  | []        := (`_h, [])
  | (nm :: nms) := (nm, nms)
  end : name × list name),
  interactive.generalize nm (to_pexpr h, x),
  t ← get_local x,
  tac t nms
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


