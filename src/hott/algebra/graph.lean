/-
Copyright (c) 2016 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Floris van Doorn

Graphs and operations on graphs

Currently we only define the notion of a path in a graph, and prove properties and operations on
paths.
-/
import ..arity ..eq2 .relation ..cubical.pathover2
universes u v w

namespace hott
hott_theory

/-
  A path is a list of vertexes which are adjacent. We maybe use a weird ordering of cons, because
  the major example where we use this is a category where this ordering makes more sense.
  For the operations on paths we use the names from the corresponding operations on lists. Opening
  both the list and the paths namespace will lead to many name clashes, so that is not advised.
-/

inductive paths {A : Type u} (R : A → A → Type v) : A → A → Type (max u v)
| nil {} : Π{a : A}, paths a a
| cons   : Π{a₁ a₂ a₃ : A} (r : R a₂ a₃), paths a₁ a₂ → paths a₁ a₃

namespace graph
  export paths

  local notation h :: t  := cons h t
  local notation `[` l:(foldr `, ` (h t, cons h t) nil `]`) := l

  variables {A : Type _} {R : A → A → Type _} {a a' a₁ a₂ a₃ a₄ : A}

  @[hott] def concat (r : R a₁ a₂) (l : paths R a₂ a₃) : paths R a₁ a₃ :=
  begin
    hinduction l with a a₂ a₃ a₄ r' l IH,
    { exact [r]},
    { exact r' :: IH r}
  end

  @[hott] theorem concat_nil (r : R a₁ a₂) : concat r (@nil A R a₂) = [r] := idp

  @[hott] theorem concat_cons (r : R a₁ a₂) (r' : R a₃ a₄) (l : paths R a₂ a₃)
    : concat r (r'::l)  = r'::(concat r l) := idp

  @[hott] def append (l₂ : paths R a₂ a₃) (l₁ : paths R a₁ a₂) :
    paths R a₁ a₃ :=
  begin
    hinduction l₂ with a₂ a₂ a₃ a₄ r l₂ IH,
    { exact l₁ },
    { exact cons r (IH l₁) }
  end

  local infix ` ++ ` := append

  @[hott] def nil_append (l : paths R a₁ a₂) : nil ++ l = l := idp
  @[hott] def cons_append (r : R a₃ a₄) (l₂ : paths R a₂ a₃) (l₁ : paths R a₁ a₂) :
    (r :: l₂) ++ l₁ = r :: (l₂ ++ l₁) := idp

  @[hott] def singleton_append (r : R a₂ a₃) (l : paths R a₁ a₂) : [r] ++ l = r :: l := idp
  @[hott] def append_singleton (l : paths R a₂ a₃) (r : R a₁ a₂) : l ++ [r] = concat r l :=
  begin
    hinduction l with a₁ a₁ a₂ a₃ r l IH,
    { refl },
    { exact ap (cons r) (IH _) }
  end

  @[hott] def append_nil (l : paths R a₁ a₂) : l ++ nil = l :=
  begin
    hinduction l with a₁ a₁ a₂ a₃ r l IH,
    { refl },
    { exact ap (cons r) IH }
  end

  @[hott] def append_assoc (l₃ : paths R a₃ a₄) (l₂ : paths R a₂ a₃)
    (l₁ : paths R a₁ a₂) : (l₃ ++ l₂) ++ l₁ = l₃ ++ (l₂ ++ l₁) :=
  begin
    hinduction l₃ with a₃ a₃ a₄ a₅ r l₃ IH,
    { refl },
    { refine ap (cons r) (IH _) }
  end

  @[hott] theorem append_concat (l₂ : paths R a₃ a₄) (l₁ : paths R a₂ a₃) (r : R a₁ a₂) :
    l₂ ++ concat r l₁ = concat r (l₂ ++ l₁) :=
  begin
    hinduction l₂ with a₂ a₂ a₃ a₄ r' l₂ IH,
    { refl },
    { exact ap (cons r') (IH _) }
  end

  @[hott] def concat_append (l₂ : paths R a₃ a₄) (r : R a₂ a₃) (l₁ : paths R a₁ a₂) :
    concat r l₂ ++ l₁ = l₂ ++ r :: l₁ :=
  begin
    hinduction l₂ with a₂ a₂ a₃ a₄ r' l₂ IH,
    { refl },
    { exact ap (cons r') (IH _) }
  end

  @[hott] def paths.rec_tail {C : Π⦃a a' : A⦄, paths R a a' → Type _}
  (H0 : Π {a : A}, @C a a nil)
  (H1 : Π {a₁ a₂ a₃ : A} (r : R a₁ a₂) (l : paths R a₂ a₃), C l → C (concat r l)) :
  Π{a a' : A} (l : paths R a a'), C l :=
  begin
    have : Π{a₁ a₂ a₃ : A} (l₂ : paths R a₂ a₃) (l₁ : paths R a₁ a₂) (c : C l₂),
      C (l₂ ++ l₁),
    begin
      intros, revert a₃ l₂ c, hinduction l₁ with a₁ a₁ a₂ a₄ r l₁ IH; intros a₃ l₂ c,
      { rwr append_nil, exact c },
      { rwr [←concat_append], apply IH, apply H1, exact c }
    end,
    intros, rwr [←nil_append l], apply this, apply H0
  end

  @[hott] def cons_eq_concat (r : R a₂ a₃) (l : paths R a₁ a₂) :
    Σa (r' : R a₁ a) (l' : paths R a a₃), r :: l = concat r' l' :=
  begin
    revert a₃ r, hinduction l with a₁ a₁ a₂ a₃ r l IH; intros a₃' r',
    { exact ⟨a₃', r', nil, idp⟩ },
    { cases (IH r) with a₄ w, cases w with r₂ w, cases w with l p, clear IH,
      exact ⟨a₄, r₂, r' :: l, ap (cons r') p⟩ }
  end

  @[hott] def length (l : paths R a₁ a₂) : ℕ :=
  begin
    hinduction l with a₁ a₁ a₂ a₃ r l IH,
    { exact 0 },
    { exact IH.succ }
  end

  /- If we can reverse edges in the graph we can reverse paths -/

  @[hott] def reverse (rev : Π⦃a a'⦄, R a a' → R a' a) (l : paths R a₁ a₂) :
    paths R a₂ a₁ :=
  begin
    hinduction l with a₁ a₁ a₂ a₃ r l IH,
    { exact nil},
    { exact concat (rev r) IH}
  end

  @[hott] theorem reverse_nil (rev : Π⦃a a'⦄, R a a' → R a' a) : reverse rev (@nil A R a₁) = [] := idp

  @[hott] theorem reverse_cons (rev : Π⦃a a'⦄, R a a' → R a' a) (r : R a₂ a₃) (l : paths R a₁ a₂) :
    reverse rev (r::l) = concat (rev r) (reverse rev l) := idp

  @[hott] theorem reverse_singleton (rev : Π⦃a a'⦄, R a a' → R a' a) (r : R a₁ a₂) :
    reverse rev [r] = [rev r] := idp

  @[hott] theorem reverse_pair (rev : Π⦃a a'⦄, R a a' → R a' a) (r₂ : R a₂ a₃) (r₁ : R a₁ a₂) :
    reverse rev [r₂, r₁] = [rev r₁, rev r₂] := idp

  @[hott] theorem reverse_concat (rev : Π⦃a a'⦄, R a a' → R a' a) (r : R a₁ a₂) (l : paths R a₂ a₃) :
    reverse rev (concat r l) = rev r :: (reverse rev l) :=
  begin
    hinduction l with a₁ a₁ a₂ a₃ r l IH,
    { refl },
    { rwr [concat_cons, reverse_cons, IH]}
  end

  @[hott] theorem reverse_append (rev : Π⦃a a'⦄, R a a' → R a' a) (l₂ : paths R a₂ a₃)
    (l₁ : paths R a₁ a₂) : reverse rev (l₂ ++ l₁) = reverse rev l₁ ++ reverse rev l₂ :=
  begin
    hinduction l₂ with a₂ a₂ a₃ a₄ r l₂ IH,
    { exact (append_nil _)⁻¹ },
    { rwr [cons_append, reverse_cons, reverse_cons, append_concat, IH] }
  end

  @[hott] def realize (P : A → A → Type _) (f : Π⦃a a'⦄, R a a' → P a a') (ρ : Πa, P a a)
    (c : Π⦃a₁ a₂ a₃⦄, P a₁ a₂ → P a₂ a₃ → P a₁ a₃)
    ⦃a a' : A⦄ (l : paths R a a') : P a a' :=
  begin
    hinduction l with a a₁ a₂ a₃ r l IH,
    { exact ρ a },
    { exact c IH (f r) }
  end

  @[hott, hsimp] def realize_nil (P : A → A → Type _) (f : Π⦃a a'⦄, R a a' → P a a') 
    (ρ : Πa, P a a) (c : Π⦃a₁ a₂ a₃⦄, P a₁ a₂ → P a₂ a₃ → P a₁ a₃) (a : A) :
    realize P f ρ c nil = ρ a :=
  by refl

  @[hott, hsimp] def realize_cons (P : A → A → Type _) (f : Π⦃a a'⦄, R a a' → P a a') (ρ : Πa, P a a)
    (c : Π⦃a₁ a₂ a₃⦄, P a₁ a₂ → P a₂ a₃ → P a₁ a₃)
    ⦃a₁ a₂ a₃ : A⦄ (r : R a₂ a₃) (l : paths R a₁ a₂) :
    realize P f ρ c (r :: l) = c (realize P f ρ c l) (f r) :=
  by refl

  @[hott] theorem realize_singleton {P : A → A → Type _} {f : Π⦃a a'⦄, R a a' → P a a'} {ρ : Πa, P a a}
    {c : Π⦃a₁ a₂ a₃⦄, P a₁ a₂ → P a₂ a₃ → P a₁ a₃}
    (id_left : Π⦃a₁ a₂⦄ (p : P a₁ a₂), c (ρ a₁) p = p)
    ⦃a₁ a₂ : A⦄ (r : R a₁ a₂) :
    realize P f ρ c [r] = f r :=
  id_left (f r)

  @[hott] theorem realize_pair {P : A → A → Type _} {f : Π⦃a a'⦄, R a a' → P a a'} {ρ : Πa, P a a}
    {c : Π⦃a₁ a₂ a₃⦄, P a₁ a₂ → P a₂ a₃ → P a₁ a₃}
    (id_left : Π⦃a₁ a₂⦄ (p : P a₁ a₂), c (ρ a₁) p = p)
    ⦃a₁ a₂ a₃ : A⦄ (r₂ : R a₂ a₃) (r₁ : R a₁ a₂) :
    realize P f ρ c [r₂, r₁] = c (f r₁) (f r₂) :=
  ap (λx, c x (f r₂)) (realize_singleton id_left r₁)

  @[hott] def realize_append {P : A → A → Type _} {f : Π⦃a a'⦄, R a a' → P a a'} {ρ : Πa, P a a}
    {c : Π⦃a₁ a₂ a₃⦄, P a₁ a₂ → P a₂ a₃ → P a₁ a₃}
    (assoc : Π⦃a₁ a₂ a₃ a₄⦄ (p : P a₁ a₂) (q : P a₂ a₃) (r : P a₃ a₄), c (c p q) r = c p (c q r))
    (id_right : Π⦃a₁ a₂⦄ (p : P a₁ a₂), c p (ρ a₂) = p)
    ⦃a₁ a₂ a₃ : A⦄ (l₂ : paths R a₂ a₃) (l₁ : paths R a₁ a₂) :
    realize P f ρ c (l₂ ++ l₁) = c (realize P f ρ c l₁) (realize P f ρ c l₂) :=
  begin
    hinduction l₂ with a₂ a₂ a₃ a₄ r l₂ IH,
    { exact (id_right _)⁻¹ },
    { rwr [cons_append, realize_cons, realize_cons, IH, assoc] }
  end

  /-
    We sometimes want to take quotients of paths (this library was developed to define the pushout of
    categories). The definition paths_rel will - given some basic reduction rules codified by Q -
    extend the reduction to a reflexive transitive relation respecting concatenation of paths.
  -/

  inductive paths_rel {A : Type u} {R : A → A → Type v}
    (Q : Π⦃a a' : A⦄, paths R a a' → paths R a a' → Type w)
    : Π⦃a a' : A⦄, paths R a a' → paths R a a' → Type (max u v w)
  | rrefl  : Π{a a' : A} (l : paths R a a'), paths_rel l l
  | rel    : Π{a₁ a₂ a₃ : A} {l₂ l₃ : paths R a₂ a₃} (l : paths R a₁ a₂) (q : Q l₂ l₃),
      paths_rel (l₂ ++ l) (l₃ ++ l)
  | rcons  : Π{a₁ a₂ a₃ : A} {l₁ l₂ : paths R a₁ a₂} (r : R a₂ a₃),
      paths_rel l₁ l₂ → paths_rel (cons r l₁) (cons r l₂)
  | rtrans : Π{a₁ a₂ : A} {l₁ l₂ l₃ : paths R a₁ a₂},
      paths_rel l₁ l₂ → paths_rel l₂ l₃ → paths_rel l₁ l₃

  open paths_rel
  attribute [refl] rrefl
  attribute [trans] rtrans
  variables {Q : Π⦃a a' : A⦄, paths R a a' → paths R a a' → Type _}

  @[hott] def paths_rel_of_Q {l₁ l₂ : paths R a₁ a₂} (q : Q l₁ l₂) :
    paths_rel Q l₁ l₂ :=
  begin
    rwr [←append_nil l₁, ←append_nil l₂], exact rel nil q,
  end

  @[hott] theorem rel_respect_append_left (l : paths R a₂ a₃) {l₃ l₄ : paths R a₁ a₂}
    (H : paths_rel Q l₃ l₄) : paths_rel Q (l ++ l₃) (l ++ l₄) :=
  begin
    hinduction l with a₁ a₁ a₂ a₃ r l IH,
    { exact H },
    { exact rcons r (IH H) }
  end

  @[hott] theorem rel_respect_append_right {l₁ l₂ : paths R a₂ a₃} (l : paths R a₁ a₂)
    (H₁ : paths_rel Q l₁ l₂) : paths_rel Q (l₁ ++ l) (l₂ ++ l) :=
  begin
    hinduction H₁ with a₁ a₂ l₁
                      a₂ a₃ a₄ l₂ l₂' l₁ q
                      a₂ a₃ a₄ l₁ l₂ r H₁ IH
                      a₂ a₃ l₁ l₂ l₂' H₁ H₁' IH IH',
    { refl },
    { rwr [append_assoc, append_assoc], exact rel _ q},
    { exact rcons r (IH l) },
    { exact rtrans (IH l) (IH' l)}
  end

  @[hott] theorem rel_respect_append {l₁ l₂ : paths R a₂ a₃} {l₃ l₄ : paths R a₁ a₂}
    (H₁ : paths_rel Q l₁ l₂) (H₂ : paths_rel Q l₃ l₄) :
    paths_rel Q (l₁ ++ l₃) (l₂ ++ l₄) :=
  begin
    hinduction H₁ with a₁ a₂ l
                       a₂ a₃ a₄ l₂ l₂' l q
                       a₂ a₃ a₄ l₁ l₂ r H₁ IH
                       a₂ a₃ l₁ l₂ l₂' H₁ H₁' IH IH',
    { exact rel_respect_append_left _ H₂},
    { rwr [append_assoc, append_assoc], transitivity _, exact rel _ q,
      apply rel_respect_append_left, apply rel_respect_append_left, exact H₂},
    { exact rcons r (IH H₂) },
    { refine rtrans (IH H₂) _, apply rel_respect_append_right, exact H₁'}
  end

  /- assuming some extra properties the relation respects reversing -/

  @[hott] theorem rel_respect_reverse (rev : Π⦃a a'⦄, R a a' → R a' a) {l₁ l₂ : paths R a₁ a₂}
    (H : paths_rel Q l₁ l₂)
    (rev_rel : Π⦃a a' : A⦄ {l l' : paths R a a'},
      Q l l' → paths_rel Q (reverse rev l) (reverse rev l')) :
    paths_rel Q (reverse rev l₁) (reverse rev l₂) :=
  begin
    hinduction H with a₁ a₂ l
                      a₂ a₃ a₄ l₂ l₂' l q
                      a₂ a₃ a₄ l₁ l₂ r H₁ IH
                      a₂ a₃ l₁ l₂ l₂' H₁ H₁' IH IH',
    { refl },
    { rwr [reverse_append, reverse_append], apply rel_respect_append_left, apply rev_rel q },
    { rwr [reverse_cons, reverse_cons,←append_singleton, ←append_singleton], 
      apply rel_respect_append_right, exact IH },
    { exact rtrans IH IH' }
  end

  @[hott] theorem rel_left_inv (rev : Π⦃a a'⦄, R a a' → R a' a) (l : paths R a₁ a₂)
    (li : Π⦃a a' : A⦄ (r : R a a'), paths_rel Q [rev r, r] nil) :
    paths_rel Q (reverse rev l ++ l) nil :=
  begin
    hinduction l with a₁ a₁ a₂ a₃ r l IH,
    { refl },
    { rwr [reverse_cons, concat_append],
      refine rtrans _ IH, apply rel_respect_append_left,
      exact rel_respect_append_right _ (li r)}
  end

  @[hott] theorem rel_right_inv (rev : Π⦃a a'⦄, R a a' → R a' a) (l : paths R a₁ a₂)
    (ri : Π⦃a a' : A⦄ (r : R a a'), paths_rel Q [r, rev r] nil) :
    paths_rel Q (l ++ reverse rev l) nil :=
  begin
    hinduction l using paths.rec_tail,
    { refl },
    { rwr [reverse_concat, concat_append],
      refine rtrans _ a, apply rel_respect_append_left,
      exact rel_respect_append_right _ (ri r)}
  end

  @[hott] def realize_eq {P : A → A → Type _} {f : Π⦃a a'⦄, R a a' → P a a'} {ρ : Πa, P a a}
    {c : Π⦃a₁ a₂ a₃⦄, P a₁ a₂ → P a₂ a₃ → P a₁ a₃}
    (assoc : Π⦃a₁ a₂ a₃ a₄⦄ (p : P a₁ a₂) (q : P a₂ a₃) (r : P a₃ a₄), c (c p q) r = c p (c q r))
    (id_right : Π⦃a₁ a₂⦄ (p : P a₁ a₂), c p (ρ a₂) = p)
    (resp_rel : Π⦃a₁ a₂⦄ {l₁ l₂ : paths R a₁ a₂}, Q l₁ l₂ →
      realize P f ρ c l₁ = realize P f ρ c l₂)
    ⦃a a' : A⦄ {l l' : paths R a a'} (H : paths_rel Q l l') :
    realize P f ρ c l = realize P f ρ c l' :=
  begin
    hinduction H with a₁ a₂ l
                      a₂ a₃ a₄ l₂ l₂' l q
                      a₂ a₃ a₄ l₁ l₂ r H₁ IH
                      a₂ a₃ l₁ l₂ l₂' H₁ H₁' IH IH',
    { refl },
    { rwr [realize_append assoc id_right, realize_append assoc id_right], 
      apply ap (c _), exact resp_rel q },
    { exact ap (λx, c x (f r)) IH },
    { exact IH ⬝ IH' }
  end


end graph

/- the following are words of paths in a graph, which means that for example
   (p ++ q) ++ r and p ++ (q ++ r) are different words. Furthermore, the paths can be reversed.
   This is used to represent 2-constructors in hit.two_quotient  -/
inductive pwords {A : Type u} (R : A → A → Type v) : A → A → Type (max u v)
| of_rel : Π{a a'} (r : R a a'), pwords a a'
| of_path : Π{a a'} (pp : a = a'), pwords a a'
| symm : Π{a a'} (r : pwords a a'), pwords a' a
| trans : Π{a a' a''} (r : pwords a a') (r' : pwords a' a''), pwords a a''

namespace graph
  export pwords
  infix ` ⬝r `:75 := pwords.trans
  postfix `⁻¹ʳ`:(max+10) := pwords.symm
  notation `[`:max a `]`:0 := pwords.of_rel a
  notation `<`:max p `>`:0 := pwords.of_path _ p
  abbreviation rfl {A : Type _} {R : A → A → Type _} {a : A} := of_path R (idpath a)
end graph

namespace graph

section
parameters {A : Type _}
            {R : A → A → Type _}
private abbreviation T := pwords R

variables ⦃a a' a'' : A⦄ {s : R a a'} {r : T a a} {B : Type _} {C : Type _}

@[hott] protected def pwords.elim {f : A → B}
  (e : Π⦃a a' : A⦄, R a a' → f a = f a') (t : T a a') : f a = f a' :=
begin
  induction t with a a' r a a' pp a a' r IH a a' a'' r r' IH₁ IH₂,
    exact e r,
    exact ap f pp,
    exact IH⁻¹,
    exact IH₁ ⬝ IH₂
end

@[hott, hsimp] protected def pwords.elim_symm {f : A → B}
  (e : Π⦃a a' : A⦄, R a a' → f a = f a') (t : T a a') : 
    pwords.elim e t⁻¹ʳ = (pwords.elim e t)⁻¹ :=
by refl

@[hott, hsimp] protected def pwords.elim_trans {f : A → B}
  (e : Π⦃a a' : A⦄, R a a' → f a = f a') (t : T a a') (t' : T a' a'') : 
    pwords.elim e (t ⬝r t') = pwords.elim e t ⬝ pwords.elim e t' :=
by refl

@[hott] def ap_pwords_elim_h {B C : Type _} {f : A → B} {g : B → C}
  (e : Π⦃a a' : A⦄, R a a' → f a = f a')
  {e' : Π⦃a a' : A⦄, R a a' → g (f a) = g (f a')}
  (p : Π⦃a a' : A⦄ (s : R a a'), ap g (e s) = e' s) (t : T a a')
  : ap g (pwords.elim e t) = pwords.elim e' t :=
begin
  induction t with a a' r a a' pp a a' r IH a a' a'' r r' IH₁ IH₂,
    apply p,
    induction pp, refl,
    exact ap_inv g (pwords.elim e r) ⬝ inverse2 IH,
    exact ap_con g (pwords.elim e r) (pwords.elim e r') ⬝ (IH₁ ◾ IH₂)
end

@[hott, hsimp] def ap_pwords_elim_h_symm {B C : Type _} {f : A → B} {g : B → C}
  (e : Π⦃a a' : A⦄, R a a' → f a = f a')
  {e' : Π⦃a a' : A⦄, R a a' → g (f a) = g (f a')}
  (p : Π⦃a a' : A⦄ (s : R a a'), ap g (e s) = e' s) (t : T a a') : 
  ap_pwords_elim_h e p t⁻¹ʳ = ap_inv g (pwords.elim e t) ⬝ (ap_pwords_elim_h e p t)⁻² :=
by refl

@[hott, hsimp] def ap_pwords_elim_h_trans {B C : Type _} {f : A → B} {g : B → C}
  (e : Π⦃a a' : A⦄, R a a' → f a = f a')
  {e' : Π⦃a a' : A⦄, R a a' → g (f a) = g (f a')}
  (p : Π⦃a a' : A⦄ (s : R a a'), ap g (e s) = e' s) (t₁ : T a a') (t₂ : T a' a'') : 
  ap_pwords_elim_h e p (t₁ ⬝r t₂) = ap_con g (pwords.elim e t₁) (pwords.elim e t₂) ⬝ 
    ap_pwords_elim_h e p t₁ ◾ ap_pwords_elim_h e p t₂ :=
by refl

@[hott] def ap_pwords_elim {B C : Type _} {f : A → B} (g : B → C)
  (e : Π⦃a a' : A⦄, R a a' → f a = f a') (t : T a a')
  : ap g (pwords.elim e t) = pwords.elim (λa a' r, ap g (e r)) t :=
ap_pwords_elim_h e (λa a' s, idp) t

@[hott, hsimp] def ap_pwords_elim_symm {B C : Type _} {f : A → B} (g : B → C)
  (e : Π⦃a a' : A⦄, R a a' → f a = f a') (t : T a a')
  : ap_pwords_elim g e t⁻¹ʳ = ap_inv g (pwords.elim e t) ⬝ (ap_pwords_elim g e t)⁻² :=
by refl

@[hott, hsimp] def ap_pwords_elim_trans {B C : Type _} {f : A → B} (g : B → C)
  (e : Π⦃a a' : A⦄, R a a' → f a = f a') (t : T a a') (t' : T a' a'')
  : ap_pwords_elim g e (t ⬝r t') = ap_con g (pwords.elim e t) (pwords.elim e t') ⬝
    (ap_pwords_elim g e t ◾ ap_pwords_elim g e t') :=
by refl

@[hott] def pwords_elim_eq {f : A → B}
  {e e' : Π⦃a a' : A⦄, R a a' → f a = f a'} (p : e ~3 e') (t : T a a')
  : pwords.elim e t = pwords.elim e' t :=
begin
  induction t with a a' r a a' pp a a' r IH a a' a'' r r' IH₁ IH₂,
    apply p,
    refl,
    exact IH⁻²,
    exact IH₁ ◾ IH₂
end

-- TODO: formulate and prove this without using function extensionality,
-- and modify the proofs using this to also not use function extensionality
-- strategy: use `pwords_elim_eq` instead of `ap ... (eq_of_homotopy3 p)`
@[hott] def ap_pwords_elim_h_eq {B C : Type _} {f : A → B} {g : B → C}
  (e : Π⦃a a' : A⦄, R a a' → f a = f a')
  {e' : Π⦃a a' : A⦄, R a a' → g (f a) = g (f a')}
  (p : Π⦃a a' : A⦄ (s : R a a'), ap g (e s) = e' s) (t : T a a')
  : ap_pwords_elim_h e p t =
    ap_pwords_elim g e t ⬝ ap (λx, pwords.elim x t) (eq_of_homotopy3 p) :=
begin
  fapply homotopy3.rec_on p,
  intro q, dsimp at q, hinduction q,
  dsimp [ap_pwords_elim], 
  symmetry, refine whisker_left _ (ap02 _ (by exact eq_of_homotopy3_id _)) ⬝ _,
  refl
end

@[hott] def ap_ap_pwords_elim_h {B C D : Type _} {f : A → B}
  {g : B → C} (h : C → D)
  (e : Π⦃a a' : A⦄, R a a' → f a = f a')
  {e' : Π⦃a a' : A⦄, R a a' → g (f a) = g (f a')}
  (p : Π⦃a a' : A⦄ (s : R a a'), ap g (e s) = e' s) (t : T a a')
  : square (ap (ap h) (ap_pwords_elim_h e p t))
            (ap_pwords_elim_h e (λa a' s, ap_compose h g (e s)) t)
            (ap_compose h g (pwords.elim e t))⁻¹
            (ap_pwords_elim_h e' (λa a' s, (ap (ap h) (p s))⁻¹) t) :=
begin
  induction t with a a' r a a' pp a a' r IH a a' a'' r r' IH₁ IH₂,
  { dsimp,
    apply square_of_eq, exact con.right_inv _ ⬝ (con.left_inv _)⁻¹ },
  { induction pp, apply ids},
  { dsimp, rwr [ap_con (ap h)],
    refine (transpose (ap_compose_inv _ _ _))⁻¹ᵛ ⬝h _,
    rwr [con_inv, eq.inv_inv, ←inv2_inv],
    exact ap_inv2 _ ⬝v square_inv2 IH },
  { dsimp, rwr [ap_con (ap h)],
    refine (transpose (ap_compose_con _ _ _ _))⁻¹ᵛ ⬝h _,
    rwr [con_inv, eq.inv_inv, con2_inv],
    refine ap_con2 _ _ ⬝v square_con2 IH₁ IH₂ },
end

@[hott] def ap_ap_pwords_elim {B C D : Type _} {f : A → B}
  (g : B → C) (h : C → D)
  (e : Π⦃a a' : A⦄, R a a' → f a = f a') (t : T a a')
  : square (ap (ap h) (ap_pwords_elim g e t))
            (ap_pwords_elim_h e (λa a' s, ap_compose h g (e s)) t)
            (ap_compose h g (pwords.elim e t))⁻¹
            (ap_pwords_elim h (λa a' r, ap g (e r)) t) :=
ap_ap_pwords_elim_h _ _ _ _

@[hott] def ap_pwords_elim_h_compose {B C D : Type _} {f : A → B}
  {g : B → C} (h : C → D)
  (e : Π⦃a a' : A⦄, R a a' → f a = f a')
  {e' : Π⦃a a' : A⦄, R a a' → h (g (f a)) = h (g (f a'))}
  (p : Π⦃a a' : A⦄ (s : R a a'), ap (h ∘ g) (e s) = e' s) (t : T a a') : 
    square (ap02 h (ap_pwords_elim g e t)) 
           (ap_pwords_elim_h e p t)
           (ap_compose h g (pwords.elim e t))⁻¹ 
           (ap_pwords_elim_h (λa a' s, ap g (e s)) (λa a' s, (ap_compose h g (e s))⁻¹ ⬝ p s) t) :=
begin
  induction t with a a' r a a' pp a a' r IH a a' a'' r r' IH₁ IH₂,
  { dsimp [ap_pwords_elim_h, ap_pwords_elim, ap02, pwords.elim], 
    apply square_of_eq, apply idp_con },
  { induction pp, apply ids },
  -- the rest of the proof is almost the same as the proof of ap_ap_pwords_elim[_h].
  -- Is there a connection between these theorems?
  { dsimp [ap02], rwr [ap_con (ap h)],
    refine (transpose (ap_compose_inv _ _ _))⁻¹ᵛ ⬝h _,
    rwr [con_inv, eq.inv_inv, ←inv2_inv],
    exact ap_inv2 _ ⬝v square_inv2 IH },
  { dsimp [ap02], rwr [ap_con (ap h)],
    refine (transpose (ap_compose_con _ _ _ _))⁻¹ᵛ ⬝h _,
    rwr [con_inv, eq.inv_inv, con2_inv],
    refine ap_con2 _ _ ⬝v square_con2 IH₁ IH₂ },
end

@[hott] def ap_pwords_elim_h_zigzag {B C D : Type _} {f : A → B}
  {g : B → C} (h : C → D)
  (e : Π⦃a a' : A⦄, R a a' → f a = f a')
  {e' : Π⦃a a' : A⦄, R a a' → h (g (f a)) = h (g (f a'))}
  (p : Π⦃a a' : A⦄ (s : R a a'), ap (h ∘ g) (e s) = e' s) (t : T a a')
  : ap_pwords_elim   h (λa a' s, ap g (e s)) t ⬝
    (ap_pwords_elim_h e (λa a' s, ap_compose h g (e s)) t)⁻¹ ⬝
    ap_pwords_elim_h e p t =
    ap_pwords_elim_h (λa a' s, ap g (e s)) (λa a' s, (ap_compose h g (e s))⁻¹ ⬝ p s) t :=
begin
  refine whisker_right _ (eq_of_square (ap_ap_pwords_elim g h e t)⁻¹ʰ)⁻¹ ⬝ _,
  refine con.assoc _ _ _ ⬝ _, apply inv_con_eq_of_eq_con, apply eq_of_square,
  apply transpose,
  -- the rest of the proof is almost the same as the proof of ap_ap_pwords_elim[_h].
  -- Is there a connection between these theorems?
  induction t with a a' r a a' pp a a' r IH a a' a'' r r' IH₁ IH₂,
  { dsimp, apply square_of_eq, apply idp_con },
  { induction pp, apply ids },
  { dsimp, rwr [ap_con (ap h)],
    refine (transpose (ap_compose_inv _ _ _))⁻¹ᵛ ⬝h _,
    rwr [con_inv, eq.inv_inv, ←inv2_inv],
    exact ap_inv2 _ ⬝v square_inv2 IH },
  { dsimp, rwr [ap_con (ap h)],
    refine (transpose (ap_compose_con _ _ _ _))⁻¹ᵛ ⬝h _,
    rwr [con_inv, eq.inv_inv, con2_inv],
    refine ap_con2 _ _ ⬝v square_con2 IH₁ IH₂ },
end

open hott.relation
@[hott] def is_equivalence_pwords : is_equivalence T :=
begin
  constructor,
    intro a, exact rfl,
    intros a a' t, exact t⁻¹ʳ,
    intros a a' a'' t t', exact t ⬝r t',
end

/- dependent elimination -/

variables {P : B → Type _} {Q : C → Type _} {f : A → B} {g : B → C} {f' : Π(a : A), P (f a)}
@[hott] protected def pwords.elimo (p : Π⦃a a' : A⦄, R a a' → f a = f a')
  (po : Π⦃a a' : A⦄ (s : R a a'), f' a =[p s] f' a') (t : T a a')
  : f' a =[pwords.elim p t] f' a' :=
begin
  induction t with a a' r a a' pp a a' r IH a a' a'' r r' IH₁ IH₂,
    exact po r,
    induction pp, constructor,
    exact IH⁻¹ᵒ,
    exact IH₁ ⬝o IH₂
end

@[hott, hsimp] def elimo_symm (p : Π⦃a a' : A⦄, R a a' → f a = f a')
  (po : Π⦃a a' : A⦄ (s : R a a'), f' a =[p s] f' a') (t : T a a')
  : pwords.elimo p po t⁻¹ʳ = (pwords.elimo p po t)⁻¹ᵒ :=
by refl

@[hott, hsimp] def elimo_trans (p : Π⦃a a' : A⦄, R a a' → f a = f a')
  (po : Π⦃a a' : A⦄ (s : R a a'), f' a =[p s] f' a') (t : T a a') (t' : T a' a'')
  : pwords.elimo p po (t ⬝r t') = pwords.elimo p po t ⬝o pwords.elimo p po t' :=
by refl

@[hott] def ap_pwords_elimo_h  {g' : Πb, Q (g b)}
  (p : Π⦃a a' : A⦄, R a a' → f a = f a')
  (po : Π⦃a a' : A⦄ (s : R a a'), g' (f a) =[p s; Q ∘ g] g' (f a'))
  (q : Π⦃a a' : A⦄ (s : R a a'), apd g' (p s) = po s)
  (t : T a a') : apd g' (pwords.elim p t) = pwords.elimo p po t :=
begin
  induction t with a a' r a a' pp a a' r IH a a' a'' r r' IH₁ IH₂,
    apply q,
    induction pp, refl,
    exact apd_inv g' (pwords.elim p r) ⬝ IH⁻²ᵒ,
    exact apd_con g' (pwords.elim p r) (pwords.elim p r') ⬝ (IH₁ ◾o IH₂)
end

@[hott] theorem pwords_elimo_ap {g' : Π(a : A), Q (g (f a))}
  (p : Π⦃a a' : A⦄, R a a' → f a = f a')
  (po : Π⦃a a' : A⦄ (s : R a a'), g' a =[ap g (p s)] g' a')
  (t : T a a') : pwords.elimo p (λa a' s, pathover_of_pathover_ap Q g (po s)) t =
    pathover_of_pathover_ap Q g (change_path (ap_pwords_elim g p t)⁻¹
      (pwords.elimo (λa a' r, ap g (p r)) po t)) :=
begin
  induction t with a a' r a a' pp a a' r IH a a' a'' r r' IH₁ IH₂,
  { refl },
  { induction pp; refl },
  { rwr [elimo_symm, ap_pwords_elim_symm, IH, con_inv, change_path_con, ←inv2_inv], dsimp,
    rwr [change_path_invo, pathover_of_pathover_ap_invo] },
  { rwr [elimo_trans, elimo_trans, ap_pwords_elim_trans, IH₁, IH₂, con_inv, change_path_con], 
    dsimp, rwr [con2_inv, change_path_cono, pathover_of_pathover_ap_cono] },
end

end
end graph
end hott