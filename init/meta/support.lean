/-
Copyright (c) 2017 Gabriel Ebner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner
-/
open expr tactic

@[inline] instance (α) [decidable_eq α] (a b : α): decidable (a == b) :=
if h : a = b then is_true (heq_of_eq h) else is_false (h ∘ eq_of_heq)

meta def expr.constants_core (e : expr) (ns : rb_set name) : rb_set name :=
e.fold ns $ λ e _ ns, match e with
| (expr.const n _) := ns.insert n
| _ := ns
end

meta def expr.constants (e : expr) : list name :=
(e.constants_core (rb_map.mk _ _)).keys

namespace hott

private meta def inst_args : expr → tactic expr | e := do
t ← infer_type e >>= whnf,
if ¬ t.is_pi then return e else do
x ← mk_local' t.binding_name t.binding_info t.binding_domain,
inst_args $ e.app x

meta def has_large_elim (ind : name) : tactic bool := do
type_former_is_prop ← mk_const ind >>= inst_args >>= is_prop,
elim_is_prop ← mk_const (ind <.> "rec") >>= inst_args >>= is_proof,
return (type_former_is_prop ∧ ¬ elim_is_prop)

meta def is_large_elim (n : name) : tactic bool := do
env ← get_env,
match env.recursor_of n with
| some ind := has_large_elim ind
| none := return ff
end

run_cmd
let unsafe := [`eq.rec, `heq.rec, `false.rec] in
unsafe.mmap' $ λ n, is_large_elim n >>= guardb

meta def has_attr (attr decl : name) : tactic bool :=
option.is_some <$> try_core (has_attribute attr decl)

private meta def check_not_nothott (n : name) : tactic unit := do
is_nothott ← has_attr `nothott n,
when is_nothott $ fail $ "not hott: marked as [nothott]: " ++ n.to_string

private meta def check_not_large_elim (n : name) : tactic unit := do
n_is_large_elim ← is_large_elim n,
when n_is_large_elim $ fail $ "not hott: uses large eliminator " ++ n.to_string

private meta def check_decl (n : name) := do
check_not_nothott n,
check_not_large_elim n,
-- TODO(gabriel): can't use unfold_all_macros since it throws an exception...
d ← get_decl n, return (d.type.constants ++ d.value.constants)

private meta def check_hott_core : ∀ (to_do : list name) (done : rb_set name), tactic unit
| [] done := return ()
| (n::to_do) done :=
    if done.contains n then
        check_hott_core to_do done
    else do
        let done := done.insert n,
        is_hott ← has_attr `hott n,
        if is_hott then
            check_hott_core to_do done
        else do
            refd_consts ← check_decl n,
            check_hott_core (refd_consts ++ to_do) done

meta def check_hott (ns : list name) : tactic unit :=
check_hott_core ns (rb_map.mk _ _)

@[user_attribute]
meta def hott_attribute : user_attribute := {
    name := `hott,
    descr := "Marks a definition that can be safely used in HoTT",
    after_set := some (λ n _ _, check_decl n >>= check_hott),
    before_unset := some $ λ _ _, skip,
}

@[user_attribute]
meta def nothott_attribute : user_attribute := {
    name := `nothott,
    descr := "Permanently marks a definition as unsafe for HoTT",
    after_set := some (λ _ _ _, skip), -- make [nothott] non-removable
}

attribute [nothott] classical.choice

open lean lean.parser interactive

private meta def exec_cmd (cmd : string) : parser unit :=
with_input command_like cmd >> return ()

@[user_attribute]
private meta def hott_theory_cmd_attr : user_attribute := {
    name := `_hott_theory_cmd,
    descr := "(internal) command that is automatically executed with hott_theory",
}

private meta def get_hott_theory_cmds : tactic (list string) := do
decls ← attribute.get_instances hott_theory_cmd_attr.name,
decls.mmap $ λ d, mk_const d >>= eval_expr string

@[user_command]
private meta def hott_theory (meta_info : decl_meta_info) (_ : parse $ tk "hott_theory") : parser unit := do
exec_cmd "noncomputable theory",
cmds ← get_hott_theory_cmds, cmds.mmap' exec_cmd

private def string_hash (s : string) : ℕ :=
s.fold 1 (λ h c, (33*h + c.val) % unsigned_sz)

@[user_command]
private meta def hott_theory_cmd (meta_info : decl_meta_info) (_ : parse $ tk "hott_theory_cmd") : parser unit := do
cmd ← lean.parser.pexpr, cmd ← i_to_expr cmd, cmd ← eval_expr string cmd,
exec_cmd cmd,
let dummy_decl_name := mk_num_name `_hott_theory_cmd_decl (string_hash cmd),
add_decl (declaration.defn dummy_decl_name [] `(string) (reflect cmd) (reducibility_hints.regular 1 tt) ff),
set_basic_attribute hott_theory_cmd_attr.name dummy_decl_name tt -- TODO(gabriel): remove this line
    <|> hott_theory_cmd_attr.set_param dummy_decl_name () tt

end hott