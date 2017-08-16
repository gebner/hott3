/-
Copyright (c) 2014-15 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Floris van Doorn

Partially ported from Coq HoTT
Theorems about sigma-types (dependent sums)
-/
import hott.types.prod

universes u v w
hott_theory

namespace hott

open eq sigma equiv is_equiv function is_trunc sum unit

@[reducible, hott]
def dpair {α β} := @sigma.mk α β

infix ` + ` := sum

namespace sigma
  variables {A : Type _} {A' : Type _} {B : A → Type _} {B' : A' → Type _} {C : Πa, B a → Type _}
            {D : Πa b, C a b → Type _}
            {a a' a'' : A} {b b₁ b₂ : B a} {b' : B a'} {b'' : B a''} {u v w : Σa, B a}

  @[hott] def destruct := @sigma.cases_on

  /- Paths in a sigma-type -/

  @[hott] protected def eta : Π (u : Σa, B a), (⟨u.1 , u.2⟩: sigma _) = u
  | ⟨u₁, u₂⟩ := idp

  @[hott] def eta2 : Π (u : Σa b, C a b), (⟨u.1, u.2.1, u.2.2⟩: Σ _ _, _) = u
  | ⟨u₁, u₂, u₃⟩ := idp

  @[hott] def eta3 : Π (u : Σa b c, D a b c), (⟨u.1, u.2.1, u.2.2.1, u.2.2.2⟩: Σ _ _ _, _) = u
  | ⟨u₁, u₂, u₃, u₄⟩ := idp

  @[hott] def dpair_eq_dpair (p : a = a') (q : b =[p] b') : (⟨a, b⟩: Σ _, _) = ⟨a', b'⟩ :=
  apd011 sigma.mk p q

  @[hott] def sigma_eq (p : u.1 = v.1) (q : u.2 =[p] v.2) : u = v :=
  by induction u; induction v; exact (dpair_eq_dpair p q)

  @[hott] def sigma_eq_right (q : b₁ = b₂) : (⟨a, b₁⟩: Σ _, _) = ⟨a, b₂⟩ :=
  ap (dpair a) q

  @[hott] def eq_pr1 (p : u = v) : u.1 = v.1 :=
  ap fst p

  postfix `..1`:(max+1) := eq_pr1

  @[hott] def eq_pr2 (p : u = v) : u.2 =[p..1] v.2 :=
  by induction p; exact idpo

  postfix `..2`:(max+1) := eq_pr2

  @[hott] def dpair_sigma_eq (p : u.1 = v.1) (q : u.2 =[p] v.2)
    : (⟨(sigma_eq p q)..1, (sigma_eq p q)..2⟩: Σ p, u.2 =[p] v.2) = ⟨p, q⟩ :=
  by induction u; induction v;dsimp at *;induction q;refl

  @[hott] def sigma_eq_pr1 (p : u.1 = v.1) (q : u.2 =[p] v.2) : (sigma_eq p q)..1 = p :=
  (dpair_sigma_eq p q)..1

  @[hott] def sigma_eq_pr2 (p : u.1 = v.1) (q : u.2 =[p] v.2)
    : (sigma_eq p q)..2 =[sigma_eq_pr1 p q; λ p, u.2 =[p] v.2] q :=
  (dpair_sigma_eq p q)..2

  @[hott] def sigma_eq_eta (p : u = v) : sigma_eq (p..1) (p..2) = p :=
  by induction p; induction u; reflexivity

  @[hott] def eq2_pr1 {p q : u = v} (r : p = q) : p..1 = q..1 :=
  ap eq_pr1 r

  @[hott] def eq2_pr2 {p q : u = v} (r : p = q) : (p..2: _) =[eq2_pr1 r; λ x, u.2 =[x] v.2] (q..2: _) :=
  by apply pathover_ap; apply (apd eq_pr2 r)

  @[hott] def tr_pr1_sigma_eq {B' : A → Type _} (p : u.1 = v.1) (q : u.2 =[p] v.2)
    : transport (λx : sigma _, B' x.1) (sigma_eq p q) = transport B' p :=
  by induction u; induction v; dsimp at *;induction q; reflexivity

  @[hott] protected def ap_pr1 (p : u = v) : ap (λx : sigma B, x.1) p = p..1 := idp

  /- the uncurried version of sigma_eq. We will prove that this is an equivalence -/

  @[hott] def sigma_eq_unc : Π (pq : Σ(p : u.1 = v.1), u.2 =[p] v.2), u = v
  | ⟨pq₁, pq₂⟩ := sigma_eq pq₁ pq₂

  @[hott] def dpair_sigma_eq_unc : Π (pq : Σ(p : u.1 = v.1), u.2 =[p] v.2),
    (⟨(sigma_eq_unc pq)..1, (sigma_eq_unc pq)..2⟩: Σ p, u.2 =[p] v.2) = pq
  | ⟨pq₁, pq₂⟩ := dpair_sigma_eq pq₁ pq₂

  @[hott] def sigma_eq_pr1_unc (pq : Σ(p : u.1 = v.1), u.2 =[p] v.2)
    : (sigma_eq_unc pq)..1 = pq.1 :=
  (dpair_sigma_eq_unc pq)..1

  @[hott] def sigma_eq_pr2_unc (pq : Σ(p : u.1 = v.1), u.2 =[p] v.2) :
    (sigma_eq_unc pq)..2 =[sigma_eq_pr1_unc pq; λ p, u.2 =[p] v.2] pq.2 :=
  (dpair_sigma_eq_unc pq)..2

  @[hott] def sigma_eq_eta_unc (p : u = v) : sigma_eq_unc ⟨p..1, p..2⟩ = p :=
  sigma_eq_eta p

  @[hott] def tr_sigma_eq_pr1_unc {B' : A → Type _}
    (pq : Σ(p : u.1 = v.1), u.2 =[p] v.2)
      : transport (λx:sigma _, B' x.1) (@sigma_eq_unc A B u v pq) = transport B' pq.1 :=
  by apply destruct pq; apply tr_pr1_sigma_eq

  @[hott, instance] def is_equiv_sigma_eq (u v : Σa, B a)
      : is_equiv (@sigma_eq_unc A B u v) :=
  adjointify sigma_eq_unc
             (λp, ⟨p..1, p..2⟩)
             sigma_eq_eta_unc
             dpair_sigma_eq_unc

  @[hott] def sigma_eq_equiv (u v : Σa, B a)
    : (u = v) ≃ (Σ(p : u.1 = v.1),  u.2 =[p] v.2) :=
  (equiv.mk sigma_eq_unc (by apply_instance))⁻¹ᵉ

  @[hott] def dpair_eq_dpair_con (p1 : a  = a' ) (q1 : b  =[p1] b' )
                                (p2 : a' = a'') (q2 : b' =[p2] b'') :
    dpair_eq_dpair (p1 ⬝ p2) (q1 ⬝o q2) = dpair_eq_dpair p1 q1 ⬝ dpair_eq_dpair  p2 q2 :=
  by induction q1; induction q2; reflexivity

  @[hott] def sigma_eq_con (p1 : u.1 = v.1) (q1 : u.2 =[p1] v.2)
                          (p2 : v.1 = w.1) (q2 : v.2 =[p2] w.2) :
    sigma_eq (p1 ⬝ p2) (q1 ⬝o q2) = sigma_eq p1 q1 ⬝ sigma_eq p2 q2 :=
  by induction u; induction v; induction w; apply dpair_eq_dpair_con

  @[hott] def dpair_eq_dpair_con_idp (p : a = a') (q : b =[p] b') :
    dpair_eq_dpair p q = dpair_eq_dpair p (pathover_tr _ _) ⬝
    dpair_eq_dpair idp (pathover_idp_of_eq (tr_eq_of_pathover q)) :=
  by induction q; reflexivity

  /- eq_pr1 commutes with the groupoid structure. -/

  @[hott] def eq_pr1_idp (u : Σa, B a)           : (idpath u) ..1 = refl (u.1)      := idp
  @[hott] def eq_pr1_con (p : u = v) (q : v = w) : (p ⬝ q)  ..1 = (p..1) ⬝ (q..1) := ap_con _ _ _
  @[hott] def eq_pr1_inv (p : u = v)             : p⁻¹      ..1 = (p..1)⁻¹        := ap_inv _ _

  /- Applying dpair to one argument is the same as dpair_eq_dpair with reflexivity in the first place. -/

  @[hott] def ap_dpair (q : b₁ = b₂) :
    ap (sigma.mk a) q = dpair_eq_dpair idp (pathover_idp_of_eq q) :=
  by induction q; reflexivity

  /- Dependent transport is the same as transport along a sigma_eq. -/

  @[hott] def transportD_eq_transport (p : a = a') (c : C a b) :
      p ▸D c = (transport (λu : sigma _, C (u.1) (u.2)) (dpair_eq_dpair p (pathover_tr _ _)) c: _) :=
  by induction p; reflexivity

  @[hott] def sigma_eq_eq_sigma_eq {p1 q1 : a = a'} {p2 : b =[p1] b'} {q2 : b =[q1] b'}
      (r : p1 = q1) (s : p2 =[r; λ p, b =[p] b'] q2) : @sigma_eq _ _ ⟨a,b⟩ ⟨a',b'⟩ p1 p2 = sigma_eq q1 q2 :=
  by induction s; reflexivity

  /- A path between paths in a total space is commonly shown component wise. -/
  @[hott] def sigma_eq2 {p q : u = v} (r : p..1 = q..1) (s : p..2 =[r; λ p, u.2 =[p] v.2] q..2)
    : p = q :=
  begin
    induction p, induction u with u1 u2,
    transitivity sigma_eq q..1 q..2,
      apply sigma_eq_eq_sigma_eq r s,
      apply sigma_eq_eta,
  end

  @[hott] def sigma_eq2_unc {p q : u = v} (rs : Σ(r : p..1 = q..1), p..2 =[r; λ p, u.2 =[p] v.2] q..2) : p = q :=
  by apply destruct rs; apply sigma_eq2

  @[hott] def ap_dpair_eq_dpair (f : Πa, B a → A') (p : a = a') (q : b =[p] b')
    : @ap _ A' (@sigma.rec _ _ (λ _, A') f) _ _ (dpair_eq_dpair p q) = apd011 f p q :=
  by induction q; reflexivity

  /- Transport -/

  /- The concrete description of transport in sigmas (and also pis) is rather trickier than in the other types.  In particular, these cannot be described just in terms of transport in simpler types; they require also the dependent transport [transportD].

  In particular, this indicates why `transport` alone cannot be fully defined by induction on the structure of types, although Id-elim/transportD can be (cf. Observational Type _ Theory).  A more thorough set of lemmas, along the lines of the present ones but dealing with Id-elim rather than just transport, might be nice to have eventually? -/

  @[hott] def sigma_transport (p : a = a') (bc : Σ(b : B a), C a b)
    : p ▸ bc = ⟨p ▸ bc.1, p ▸D bc.2⟩ :=
  by induction p; induction bc; reflexivity

  /- The special case when the second variable doesn't depend on the first is simpler. -/
  @[hott] def sigma_transport_nondep {B : Type _} {C : A → B → Type _} (p : a = a')
    (bc : Σ(b : B), C a b) : p ▸ bc = ⟨bc.1, (transport (λ a, C a bc.1) p bc.2: _)⟩ :=
  by induction p; induction bc; reflexivity

  /- Or if the second variable contains a first component that doesn't depend on the first. -/

  @[hott] def sigma_transport2_nondep {C : A → Type _} {D : Π a:A, B a → C a → Type _} (p : a = a')
      (bcd : Σ(b : B a) (c : C a), D a b c) : p ▸ bcd = ⟨p ▸ bcd.1, p ▸ bcd.2.1, p ▸D2 bcd.2.2⟩ :=
  begin
    induction p, induction bcd with b cd, induction cd, reflexivity
  end

  /- Pathovers -/

  @[hott] def etao (p : a = a') (bc : Σ(b : B a), C a b)
    : bc =[p; λ a, Σ b, C a b] ⟨p ▸ bc.1, p ▸D bc.2⟩ :=
  by induction p; induction bc; apply idpo

  -- TODO: interchange sigma_pathover and sigma_pathover'
  @[hott] def sigma_pathover (p : a = a') (u : Σ(b : B a), C a b) (v : Σ(b : B a'), C a' b)
    (r : u.1 =[p] v.1) (s : u.2 =[apd011 C p r; id] v.2) : u =[p; λ a, Σ b, C a b] v :=
  begin
    induction u, induction v, dsimp at *, induction r,
    dsimp [apd011] at s, apply idp_rec_on s, apply idpo
  end

  @[hott] def sigma_pathover' (p : a = a') (u : Σ(b : B a), C a b) (v : Σ(b : B a'), C a' b)
    (r : u.1 =[p] v.1) (s : @pathover (sigma _) ⟨a,u.1⟩ (λ x, C x.1 x.2) u.2 ⟨a',v.1⟩ (sigma_eq p r) v.2) :
    u =[p; λ a, Σ b, C a b] v :=
  begin
    induction u, induction v, dsimp at *, induction r,
    apply idp_rec_on s, apply idpo
  end

  @[hott] def sigma_pathover_nondep {B : Type _} {C : A → B → Type _} (p : a = a')
    (u : Σ(b : B), C a b) (v : Σ(b : B), C a' b)
    (r : u.1 = v.1) (s : @pathover (prod _ _) (a,u.1) (λx, C x.1 x.2) u.2 (a',v.1) (prod.prod_eq p r) v.2) :
    u =[p; λ a, Σ b, C a b] v :=
  begin
    induction p, induction u, induction v, dsimp at *, induction r,
    apply idp_rec_on s, apply idpo
  end

  @[hott] def pathover_pr1 {A : Type _} {B : A → Type _} {C : Πa, B a → Type _}
    {a a' : A} {p : a = a'} {x : Σb, C a b} {x' : Σb', C a' b'}
    (q : x =[p; λ a, Σb, C a b] x') : x.1 =[p] x'.1 :=
  begin induction q, constructor end

  @[hott] def sigma_pathover_equiv_of_is_prop {A : Type _} {B : A → Type _} (C : Πa, B a → Type _)
    {a a' : A} (p : a = a') (x : Σb, C a b) (x' : Σb', C a' b')
    [Πa b, is_prop (C a b)] : x =[p; λa, Σb, C a b] x' ≃ x.1 =[p] x'.1 :=
  begin
    fapply equiv.MK,
    { exact pathover_pr1 },
    { intro q, induction x with b c, induction x' with b' c', dsimp at q, induction q,
      apply pathover_idp_of_eq, exact sigma_eq idp (is_prop.elimo _ _ _) },
    { intro q, induction x with b c, induction x' with b' c', dsimp at q, induction q,
      have: c = c', by apply is_prop.elim, induction this,
      delta id_locked; dsimp, rwr is_prop_elimo_self, },
    { intro q, induction q, induction x with b c,
      delta id_locked; dsimp [pathover_pr1], rwr is_prop_elimo_self }
  end

  /-
    TODO:
    * define the projections from the type u =[p] v
    * show that the uncurried version of sigma_pathover is an equivalence
  -/
  /- Squares in a sigma type are characterized in cubical.squareover (to avoid circular imports) -/

  /- Functorial action -/
  variables (f : A → A') (g : Πa, B a → B' (f a))

  @[hott] def sigma_functor (u : Σa, B a) : Σa', B' a' :=
  ⟨f u.1, g u.1 u.2⟩

  @[hott] def total {B' : A → Type _} (g : Πa, B a → B' a) : (Σa, B a) → (Σa, B' a) :=
  sigma_functor id g

  /- Equivalences -/
  @[hott] def is_equiv_sigma_functor [H1 : is_equiv f] [H2 : Π a, is_equiv (g a)]
      : is_equiv (sigma_functor f g) :=
  adjointify (sigma_functor f g)
             (sigma_functor f⁻¹ (λ(a' : A') (b' : B' a'),
               ((g (f⁻¹ a'))⁻¹ (transport B' (right_inv f a')⁻¹ b'))))
  begin abstract {
    intro u', induction u' with a' b', fapply sigma_eq,
    {apply right_inv f},
    {dsimp [sigma_functor], rwr right_inv (g (f⁻¹ a')), apply tr_pathover}
  } end
  begin abstract {
    intro u, induction u with a b, fapply sigma_eq,
    {apply left_inv f},
    {apply pathover_of_tr_eq, dsimp [sigma_functor],
      rwr [adj f, (fn_tr_eq_tr_fn (left_inv f a) (λ a, (g a)⁻¹) _).inverse,
        tr_compose B', tr_inv_tr], dsimp, rwr left_inv }
  } end

  @[hott] def sigma_equiv_sigma_of_is_equiv
    [H1 : is_equiv f] [H2 : Π a, is_equiv (g a)] : (Σa, B a) ≃ (Σa', B' a') :=
  equiv.mk (sigma_functor f g) (is_equiv_sigma_functor _ _)

  @[hott] def sigma_equiv_sigma (Hf : A ≃ A') (Hg : Π a, B a ≃ B' (to_fun Hf a)) :
      (Σa, B a) ≃ (Σa', B' a') :=
  sigma_equiv_sigma_of_is_equiv (to_fun Hf) (λ a, to_fun (Hg a))

  @[hott] def sigma_equiv_sigma_right {B' : A → Type _} (Hg : Π a, B a ≃ B' a)
    : (Σa, B a) ≃ Σa, B' a :=
  sigma_equiv_sigma equiv.rfl Hg

  @[hott] def sigma_equiv_sigma_left (Hf : A ≃ A') :
    (Σa, B a) ≃ (Σa', B (to_inv Hf a')) :=
  sigma_equiv_sigma Hf (λ a, equiv_ap B (right_inv Hf.to_inv a)⁻¹ᵖ)

  @[hott] def sigma_equiv_sigma_left' (Hf : A' ≃ A) : (Σa, B (Hf a)) ≃ (Σa', B a') :=
  sigma_equiv_sigma Hf (λa, erfl)

  @[hott] def ap_sigma_functor_eq_dpair (p : a = a') (q : b =[p] b') :
    ap (sigma_functor f g) (@sigma_eq _ _ ⟨a,b⟩ ⟨a',b'⟩ p q) =
      sigma_eq (ap f p: _) (by exact pathover.rec_on q idpo) :=
  by induction q; reflexivity

  @[hott] def sigma_ua {A B : Type _} (C : A ≃ B → Type _) :
    (Σ(p : A = B), C (equiv_of_eq p)) ≃ Σ(e : A ≃ B), C e :=
  sigma_equiv_sigma_left' (eq_equiv_equiv _ _)

  -- @[hott] def ap_sigma_functor_eq (p : u.1 = v.1) (q : u.2 =[p] v.2)
  --   : ap (sigma_functor f g) (sigma_eq p q) =
  --     sigma_eq (ap f p)
  --      ((tr_compose B' f p (g u.1 u.2))⁻¹ ⬝ (fn_tr_eq_tr_fn p g u.2)⁻¹ ⬝ ap (g v.1) q) :=
  -- by induction u; induction v; apply ap_sigma_functor_eq_dpair

  /- definition 3.11.9(i): Summing up a contractible family of types does nothing. -/

  @[hott, instance] def is_equiv_pr1 (B : A → Type _) [H : Π a, is_contr (B a)]
      : is_equiv (@fst A B) :=
  adjointify fst
             (λa, ⟨a, center _⟩)
             (λa, idp)
             (λu, sigma_eq idp (pathover_idp_of_eq (center_eq _)))

  @[hott] def sigma_equiv_of_is_contr_right [H : Π a, is_contr (B a)]
    : (Σa, B a) ≃ A :=
  equiv.mk fst (by apply_instance)

  /- definition 3.11.9(ii): Dually, summing up over a contractible type does nothing. -/

  @[hott] def sigma_equiv_of_is_contr_left (B : A → Type _) [H : is_contr A]
    : (Σa, B a) ≃ B (center A) :=
  equiv.MK
    (λu, (center_eq u.1)⁻¹ ▸ u.2)
    (λb, ⟨center _, b⟩)
    begin abstract { intro b, change _ = idpath (center A) ▸ b,
      apply ap (λx, x ▸ b), apply prop_eq_of_is_contr, } end
    begin abstract { exact λu, sigma_eq (center_eq _) (tr_pathover _ _) } end

  /- Associativity -/

  --this proof is harder than in Coq because we don't have eta definitionally for sigma
  @[hott] def sigma_assoc_equiv (C : (Σa, B a) → Type _)
    : (Σa b, C ⟨a, b⟩) ≃ (Σu, C u) :=
  equiv.mk _ (adjointify
    (λav, ⟨⟨av.1, av.2.1⟩, av.2.2⟩)
    (λuc, ⟨uc.1.1, uc.1.2, (sigma.eta _)⁻¹ᵖ ▸ uc.2⟩)
    begin abstract { intro uc, induction uc with u c, induction u, reflexivity } end
    begin abstract { intro av, induction av with a v, induction v, reflexivity } end)

  open prod prod.ops
  @[hott] def assoc_equiv_prod (C : (A × A') → Type _) : (Σa a', C (a,a')) ≃ (Σu, C u) :=
  equiv.mk _ (adjointify
    (λav, ⟨(av.1, av.2.1), av.2.2⟩)
    (λuc, ⟨(uc.1).1, (uc.1).2, (prod.eta _)⁻¹ ▸ uc.2⟩)
    (λ ⟨⟨a,b⟩,c⟩, idp) (λ ⟨a,⟨b,c⟩⟩, idp))

  /- Symmetry -/

  @[hott] def comm_equiv_unc (C : A × A' → Type _) : (Σa a', C (a, a')) ≃ (Σa' a, C (a, a')) :=
  calc
    (Σa a', C (a, a')) ≃ Σu, C u          : assoc_equiv_prod _
                   ... ≃ Σv, C (flip v)   : sigma_equiv_sigma (prod.prod_comm_equiv _ _)
                                              (λ ⟨a,a'⟩, equiv.rfl)
                   ... ≃ Σa' a, C (a, a') : by symmetry; exact assoc_equiv_prod (C ∘ prod.flip)

  @[hott] def sigma_comm_equiv (C : A → A' → Type _)
    : (Σa a', C a a') ≃ (Σa' a, C a a') :=
  comm_equiv_unc (λu, C (fst u) (snd u))

  @[hott] def equiv_prod (A B : Type _) : (Σ(a : A), B) ≃ A × B :=
  equiv.mk _ (adjointify
    (λs, (s.1, s.2))
    (λp, ⟨fst p, snd p⟩)
    (λ⟨a,b⟩, idp) (λ⟨a,b⟩, idp))

  @[hott] def comm_equiv_nondep (A B : Type _) : (Σ(a : A), B) ≃ Σ(b : B), A :=
  calc
    (Σ(a : A), B) ≃ A × B       : by apply equiv_prod
              ... ≃ B × A       : by apply prod.prod_comm_equiv
              ... ≃ Σ(b : B), A : by symmetry; apply equiv_prod

  @[hott] def sigma_assoc_comm_equiv {A : Type _} (B C : A → Type _)
    : (Σ(v : Σa, B a), C v.1) ≃ (Σ(u : Σa, C a), B u.1) :=
  calc    (Σ(v : Σa, B a), C v.1)
        ≃ (Σa (b : B a), C a)     : by symmetry; apply sigma_assoc_equiv (C ∘ fst)
    ... ≃ (Σa (c : C a), B a)     : by apply sigma_equiv_sigma_right; intro a; apply comm_equiv_nondep
    ... ≃ (Σ(u : Σa, C a), B u.1) : by apply sigma_assoc_equiv (B ∘ fst)

  /- Interaction with other type constructors -/

  @[hott] def sigma_empty_left (B : empty → Type _) : (Σx, B x) ≃ empty :=
  begin
    fapply equiv.MK,
    { intro v, induction v, cases fst},
    { intro x, cases x},
    { intro x, cases x},
    { intro v, induction v, cases fst},
  end

  @[hott] def sigma_empty_right (A : Type _) : (Σ(a : A), empty) ≃ empty :=
  begin
    fapply equiv.MK,
    { intro v, induction v, cases snd},
    { intro x, cases x},
    { intro x, cases x},
    { intro v, induction v, cases snd},
  end

  @[hott] def sigma_unit_left (B : unit → Type _) : (Σx, B x) ≃ B star :=
  sigma_equiv_of_is_contr_left _

  @[hott] def sigma_unit_right (A : Type _) : (Σ(a : A), unit) ≃ A :=
  sigma_equiv_of_is_contr_right

  @[hott] def sigma_sum_left (B : A + A' → Type _)
    : (Σp, B p) ≃ (Σa, B (inl a)) + (Σa, B (inr a)) :=
  begin
    fapply equiv.MK,
    { intro v,
      induction v with p b,
      induction p,
      { apply inl, constructor, assumption },
      { apply inr, constructor, assumption }},
    { intro p, induction p with v v; induction v; constructor; assumption},
    { intro p, induction p with v v; induction v; reflexivity},
    { intro v, induction v with p b, induction p; reflexivity},
  end

  @[hott] def sigma_sum_right (B C : A → Type _)
    : (Σa, B a + C a) ≃ (Σa, B a) + (Σa, C a) :=
  begin
    fapply equiv.MK,
    { intro v,
      induction v with a p,
      induction p,
      { apply inl, constructor, assumption},
      { apply inr, constructor, assumption}},
    { intro p,
      induction p with v v,
      { induction v, constructor, apply inl, assumption },
      { induction v, constructor, apply inr, assumption }},
    { intro p, induction p with v v; induction v; reflexivity},
    { intro v, induction v with a p, induction p; reflexivity},
  end

  @[hott] def sigma_sigma_eq_right {A : Type _} (a : A) (P : Π(b : A), a = b → Type _)
    : (Σ(b : A) (p : a = b), P b p) ≃ P a idp :=
  calc
    (Σ(b : A) (p : a = b), P b p) ≃ (Σ(v : Σ(b : A), a = b), P v.1 v.2) : by apply sigma_assoc_equiv (λ u, P u.fst u.snd)
      ... ≃ P a idp : by apply sigma_equiv_of_is_contr_left (λ v : Σ b, a=b, P v.fst v.snd)

  @[hott] def sigma_sigma_eq_left {A : Type _} (a : A) (P : Π(b : A), b = a → Type _)
    : (Σ(b : A) (p : b = a), P b p) ≃ P a idp :=
  calc
    (Σ(b : A) (p : b = a), P b p) ≃ (Σ(v : Σ(b : A), b = a), P v.1 v.2) : by apply sigma_assoc_equiv (λ u : Σ b, b=a, P u.fst u.snd)
      ... ≃ P a idp : by apply sigma_equiv_of_is_contr_left (λ v : Σ b, b=a, P v.fst v.snd)

  /- ** Universal mapping properties -/
  /- *** The positive universal property. -/

  section
  @[hott, instance] def is_equiv_sigma_rec (C : (Σa, B a) → Type _)
    : is_equiv (sigma.rec : (Πa b, C ⟨a, b⟩) → Πab, C ab) :=
  adjointify _ (λ g a b, g ⟨a, b⟩)
               (λ g, eq_of_homotopy (λ⟨a,b⟩, idp))
               (λ f, refl f)

  @[hott] def equiv_sigma_rec (C : (Σa, B a) → Type _)
    : (Π(a : A) (b: B a), C ⟨a, b⟩) ≃ (Πxy, C xy) :=
  equiv.mk sigma.rec (by apply_instance)

  /- *** The negative universal property. -/

  @[hott] protected def coind_unc (fg : Σ(f : Πa, B a), Πa, C a (f a)) (a : A)
    : Σ(b : B a), C a b :=
  ⟨fg.1 a, fg.2 a⟩

  @[hott] protected def coind (f : Π a, B a) (g : Π a, C a (f a)) (a : A) : Σ(b : B a), C a b :=
  sigma.coind_unc ⟨f, g⟩ a

  --is the instance below dangerous?
  --in Coq this can be done without function extensionality
  @[hott, instance] def is_equiv_coind (C : Πa, B a → Type _)
    : is_equiv (@sigma.coind_unc _ _ C) :=
  adjointify _ (λ h, ⟨λa, (h a).1, λa, (h a).2⟩)
               (λ h, eq_of_homotopy (λu, sigma.eta _))
               (λ⟨f,g⟩, idp)

  @[hott] def sigma_pi_equiv_pi_sigma : (Σ(f : Πa, B a), Πa, C a (f a)) ≃ (Πa, Σb, C a b) :=
  equiv.mk sigma.coind_unc (by apply_instance)
  end

  /- Subtypes (sigma types whose second components are props) -/

  @[hott] def subtype {A : Type _} (P : A → Type _) [H : Πa, is_prop (P a)] :=
  Σ(a : A), P a
  notation [parsing_only] `{` binder `|` r:(scoped:1 P, subtype P) `}` := r

  /- To prove equality in a subtype, we only need equality of the first component. -/
  @[hott] def subtype_eq [H : Πa, is_prop (B a)] {u v : {a | B a}} :
    u.1 = v.1 → u = v :=
  sigma_eq_unc ∘ inv fst

  @[hott] def is_equiv_subtype_eq [H : Πa, is_prop (B a)] (u v : {a | B a})
      : is_equiv (subtype_eq : u.1 = v.1 → u = v) :=
  is_equiv_compose _ _
  local attribute [instance] is_equiv_subtype_eq

  @[hott] def equiv_subtype [H : Πa, is_prop (B a)] (u v : {a | B a}) :
    (u.1 = v.1) ≃ (u = v) :=
  equiv.mk subtype_eq (by apply_instance)

  @[hott] def subtype_eq_equiv [H : Πa, is_prop (B a)] (u v : {a | B a}) :
    (u = v) ≃ (u.1 = v.1) :=
  (equiv_subtype u v)⁻¹ᵉ

  @[hott] def subtype_eq_inv {A : Type _} {B : A → Type _} [H : Πa, is_prop (B a)] (u v : Σa, B a)
    : u = v → u.1 = v.1 :=
  subtype_eq⁻¹ᶠ

  @[hott] def is_equiv_subtype_eq_inv {A : Type _} {B : A → Type _} [H : Πa, is_prop (B a)]
    (u v : Σa, B a) : is_equiv (subtype_eq_inv u v) :=
  by delta subtype_eq_inv; apply_instance

  /- truncatedness -/
  @[hott] def is_trunc_sigma (B : A → Type _) (n : trunc_index)
      [HA : is_trunc n A] [HB : Πa, is_trunc n (B a)] : is_trunc n (Σa, B a) :=
  begin
  revert A B HA HB,
  induction n with n IH,
  { intros A B HA HB, fapply is_trunc_equiv_closed_rev _ _, apply B (center _), apply sigma_equiv_of_is_contr_left, apply_instance},
  { intros A B HA HB, fapply is_trunc_succ_intro _ _, intros u v,
    apply @is_trunc_equiv_closed_rev _ _ _ (sigma_eq_equiv _ _) (@IH _ _ _ _);
    apply_instance}
  end

  @[hott] theorem is_trunc_subtype (B : A → Prop) (n : trunc_index)
      [HA : is_trunc (n.+1) A] : is_trunc (n.+1) (Σa, (B a).carrier) :=
  @is_trunc_sigma _ (λ a, (B a).carrier) (n.+1) _ (λa, is_trunc_succ_of_is_prop _ _)

  /- if the total space is a mere proposition, you can equate two points in the base type by
     finding points in their fibers -/
  @[hott] def eq_base_of_is_prop_sigma {A : Type _} (B : A → Type _) (H : is_prop (Σa, B a)) {a a' : A}
    (b : B a) (b' : B a') : a = a' :=
  (@is_prop.elim (Σa, B a) _ ⟨a, b⟩ ⟨a', b'⟩)..1

end sigma

attribute [instance] sigma.is_trunc_sigma
attribute [instance] sigma.is_trunc_subtype

namespace sigma

  /- pointed sigma type -/
  open pointed

  @[hott, instance] def pointed_sigma {A : Type _} (P : A → Type _) [G : pointed A]
      [H : pointed (P pt)] : pointed (Σx, P x) :=
  pointed.mk ⟨pt,pt⟩

  @[hott] def psigma {A : Type*} (P : A → Type*) : Type* :=
  pointed.mk' (Σa, (P a).carrier)

  notation `Σ*` binders `, ` r:(scoped P, psigma P) := r

  @[hott] def ppr1 {A : Type*} {B : A → Type*} : (Σ*(x : A), B x) →* A :=
  pmap.mk fst idp

  @[hott] def ppr2 {A : Type*} {B : A → Type*} (v : (Σ*(x : A), B x)) : B (ppr1.to_fun v) :=
  snd v

  @[hott] def ptsigma {n : ℕ₋₂} {A : n-Type*} (P : A.carrier → (n-Type*)) : n-Type* :=
  ptrunctype.mk' n (Σa, (P a).carrier)

end sigma

end hott