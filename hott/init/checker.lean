/-
Copyright (c) 2017 Gabriel Ebner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner
-/
open expr tactic

meta def expr.constants (e : expr) : list name :=
e.fold [] $ λ e _ ns, match e with
| (expr.const n _) := n::ns
| _ := ns
end

private meta def is_large_elim : name → bool
| `eq.rec := tt
| `heq.rec := tt
| `acc.rec := tt
| `false.rec := tt
| _ := ff

private meta def check_hott_core : ∀ (to_do : list name) (done : rb_set name), tactic unit
| [] done := return ()
| (n::to_do) done :=
if done.contains n then check_hott_core to_do done
else (has_attribute `hott n >> skip) <|> do
    d ← get_decl n,
    when (is_large_elim n) $ fail $ "not hott: uses large eliminator " ++ n.to_string,
    check_hott_core (d.value.constants ++ to_do) (done.insert n)

meta def check_hott (e : expr) : tactic unit :=
check_hott_core e.constants (rb_map.mk _ _)

@[user_attribute]
meta def hott_attribute : user_attribute := {
    name := `hott,
    descr := "Marks a definition that does not use large elimination for props",
    after_set := some $ λ n _ _, (do d ← get_decl n, check_hott d.value),
    before_unset := some $ λ _ _, skip,
}
