/-
Copyright (c) 2014-15 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Floris van Doorn

Partially ported from Coq HoTT
Theorems about pi-types (dependent function spaces)
-/

import .sigma hott.arity hott.cubical.square

universe u
hott_theory

namespace hott
open hott.eq hott.equiv hott.is_equiv hott.funext hott.sigma hott.is_trunc unit

namespace pi
  variables {A : Type _} {A' : Type _} {B : A → Type _} {B' : A' → Type _} {C : Πa, B a → Type _}
            {D : Πa b, C a b → Type _}
            {a a' a'' : A} {b b₁ b₂ : B a} {b' : B a'} {b'' : B a''} {f g : Πa, B a}

  /- Paths -/

  /-
    Paths [p : f ≈ g] in a function type [Πx:X, P x] are equivalent to functions taking values
    in path types, [H : Πx:X, f x = g x], or concisely, [H : f ~ g].

    This is developed in init.funext.
  -/

  /- homotopy.symm is an equivalence -/
  @[hott] def is_equiv_homotopy_symm : is_equiv (homotopy.symm : f ~ g → g ~ f) :=
  begin
    apply adjointify homotopy.symm homotopy.symm,
    { intro p, apply eq_of_homotopy, intro a, apply eq.inv_inv },
    { intro p, apply eq_of_homotopy, intro a, apply eq.inv_inv }
  end

  /-
    The identification of the path space of a dependent function space,
    up to equivalence, is of course just funext.
  -/

  @[hott] def pi_eq_equiv (f g : Πx, B x) : (f = g) ≃ (f ~ g) := eq_equiv_homotopy f g

  @[hott,instance] def is_equiv_eq_of_homotopy (f g : Πx, B x)
    : is_equiv (eq_of_homotopy : f ~ g → f = g) :=
  is_equiv_inv _

  @[hott] def homotopy_equiv_eq (f g : Πx, B x) : (f ~ g) ≃ (f = g) :=
  equiv.mk eq_of_homotopy (by apply_instance)


  /- Transport -/

  @[hott] def pi_transport (p : a = a') (f : Π(b : B a), C a b)
    : (transport (λa, Π(b : B a), C a b) p f) ~ (λb, tr_inv_tr p b ▸ (p ▸D f (p⁻¹ ▸ b))) :=
  by induction p; reflexivity

  /- A special case of [transport_pi] where the type [B] does not depend on [A],
      and so it is just a fixed type [B]. -/
  @[hott] def pi_transport_constant {C : A → A' → Type _} (p : a = a') (f : Π(b : A'), C a b) (b : A')
    : (transport _ p f) b = @transport A (λa, C a b) _ _ p (f b) := --fix
  by induction p; reflexivity

  /- Pathovers -/

  @[hott] def pi_pathover' {f : Πb, C a b} {g : Πb', C a' b'} {p : a = a'}
    (r : Π(b : B a) (b' : B a') (q : b =[p] b'), f b =[apd011 C p q; λX, X] g b') : f =[p; λa, Πb, C a b] g :=
  begin
    induction p, apply pathover_idp_of_eq,
    apply eq_of_homotopy, intro b,
    let z := eq_of_pathover_idp (r b b idpo), exact z --fix
  end

  @[hott] def pi_pathover_left' {f : Πb, C a b} {g : Πb', C a' b'} {p : a = a'}
    (r : Π(b : B a), f b =[apd011 C p (pathover_tr _ _); λX, X] g (p ▸ b)) : f =[p; λa, Πb, C a b] g :=
  begin
    induction p, apply pathover_idp_of_eq,
    apply eq_of_homotopy, hintro b,
    let z := eq_of_pathover_idp (r b), exact z --fix
  end

  @[hott] def pi_pathover_right' {f : Πb, C a b} {g : Πb', C a' b'} {p : a = a'}
    (r : Π(b' : B a'), f (p⁻¹ ▸ b') =[apd011 C p (tr_pathover _ _); λX, X] g b') : f =[p; λa, Πb, C a b] g :=
  begin
    induction p, apply pathover_idp_of_eq,
    apply eq_of_homotopy, hintro b,
    dsimp [apd011, tr_pathover] at r,
    let z := eq_of_pathover_idp (r b), exact z --fix
  end

  @[hott] def pi_pathover_constant {C : A → A' → Type _} {f : Π(b : A'), C a b}
    {g : Π(b : A'), C a' b} {p : a = a'}
    (r : Π(b : A'), f b =[p; λa, C a b] g b) : f =[p; λa, Πb, C a b] g :=
  begin
    induction p, apply pathover_idp_of_eq,
    apply eq_of_homotopy, hintro b,
    let z := eq_of_pathover_idp (r b), exact z --fix
  end

  -- a version where C is uncurried, but where the conclusion of r is still a proper pathover
  -- instead of a heterogenous equality
  @[hott] def pi_pathover {C : (Σa, B a) → Type _} {f : Πb, C ⟨a, b⟩} {g : Πb', C ⟨a', b'⟩}
    {p : a = a'} (r : Π(b : B a) (b' : B a') (q : b =[p] b'), f b =[dpair_eq_dpair p q] g b')
    : f =[p; λa, Πb, C ⟨a, b⟩] g :=
  begin
    induction p, apply pathover_idp_of_eq,
    apply eq_of_homotopy, hintro b,
    apply (@eq_of_pathover_idp _ C), exact (r b b (pathover.idpatho b)),
  end

  @[hott] def pi_pathover_left {C : (Σa, B a) → Type _} {f : Πb, C ⟨a, b⟩} {g : Πb', C ⟨a', b'⟩}
    {p : a = a'} (r : Π(b : B a), f b =[dpair_eq_dpair p (pathover_tr _ _)] g (p ▸ b))
    : f =[p; λa, Πb, C ⟨a, b⟩] g :=
  begin
    induction p, apply pathover_idp_of_eq,
    apply eq_of_homotopy, hintro b,
    apply eq_of_pathover_idp, exact pathover_ap _ _ (r b)
  end

  @[hott] def pi_pathover_right {C : (Σa, B a) → Type _} {f : Πb, C ⟨a, b⟩} {g : Πb', C ⟨a', b'⟩}
    {p : a = a'} (r : Π(b' : B a'), f (p⁻¹ ▸ b') =[dpair_eq_dpair p (tr_pathover _ _)] g b')
    : f =[p; λa, Πb, C ⟨a, b⟩] g :=
  begin
    induction p, apply pathover_idp_of_eq,
    apply eq_of_homotopy, hintro b,
    apply eq_of_pathover_idp, exact pathover_ap _ _ (r b)
  end

  /- Maps on paths -/

  /- The action of maps given by lambda. -/
  @[hott] def ap_lambdaD {C : A' → Type _} (p : a = a') (f : Πa b, C b) :
    ap (λa b, f a b) p = eq_of_homotopy (λb, ap (λa, f a b) p) :=
  begin
    apply (eq.rec_on p),
    apply inverse,
    apply eq_of_homotopy_idp
  end

  /- Dependent paths -/

  /- with more implicit arguments the conclusion of the following theorem is
     (Π(b : B a), transportD B C p b (f b) = g (transport B p b)) ≃
     (transport (λa, Π(b : B a), C a b) p f = g) -/
  @[hott] def heq_piD (p : a = a') (f : Π(b : B a), C a b)
    (g : Π(b' : B a'), C a' b') : (Π(b : B a), p ▸D (f b) = g (p ▸ b)) ≃ (p ▸ f = g) :=
  eq.rec_on p (λg, homotopy_equiv_eq _ _) g

  @[hott] def heq_pi {C : A → Type _} (p : a = a') (f : Π(b : B a), C a)
    (g : Π(b' : B a'), C a') : (Π(b : B a), p ▸ (f b) = g (p ▸ b)) ≃ (p ▸ f = g) :=
  eq.rec_on p (λg, homotopy_equiv_eq _ _) g


  section
  /- more implicit arguments:
  (Π(b : B a), transport C (sigma_eq p idp) (f b) = g (p ▸ b)) ≃
  (Π(b : B a), transportD B (λ(a : A) (b : B a), C ⟨a, b⟩) p b (f b) = g (transport B p b)) -/
  @[hott] def heq_pi_sigma {C : (Σa, B a) → Type _} (p : a = a')
    (f : Π(b : B a), C ⟨a, b⟩) (g : Π(b' : B a'), C ⟨a', b'⟩) :
    (Π(b : B a), (dpair_eq_dpair p (pathover_tr p b)) ▸ (f b) = g (p ▸ b)) ≃
    (Π(b : B a), transportD (λa b, C ⟨a, b⟩) p _ (f b) = g (p ▸ b)) :=
  by induction p; refl
  end

  /- Functorial action -/
  variables (f0 : A' → A) (f1 : Π(a':A'), B (f0 a') → B' a')

  /- The functoriality of [forall] is slightly subtle: it is contravariant in the domain type and covariant in the codomain, but the codomain is dependent on the domain. -/

  @[hott] def pi_functor : (Π(a:A), B a) → (Π(a':A'), B' a') :=
  λg a', f1 a' (g (f0 a'))

  @[hott] def pi_functor_left (B : A → Type _) : (Π(a:A), B a) → (Π(a':A'), B (f0 a')) :=
  pi_functor f0 (λa, id)

  @[hott] def pi_functor_right {B' : A → Type _} (f1 : Π(a:A), B a → B' a)
    : (Π(a:A), B a) → (Π(a:A), B' a) :=
  pi_functor id f1

  @[hott] def pi_iff_pi {B' : A → Type _} (f : Πa, B a ↔ B' a) : (Π(a:A), B a) ↔ (Π(a:A), B' a) :=
  ⟨pi_functor id (λa, (f a).1), pi_functor id (λa, (f a).2)⟩

  @[hott,hsimp] def pi_functor_eq (g : Πa, B a) (a' : A') : pi_functor f0 f1 g a' = f1 a' (g (f0 a')) :=
  by refl
  @[hott] def ap_pi_functor {g g' : Π(a:A), B a} (h : g ~ g')
    : ap (pi_functor f0 f1) (eq_of_homotopy h)
      = eq_of_homotopy (λ(a' : A'), (ap (f1 a') (h (f0 a')))) :=
  begin
  apply is_equiv_rect
    (@apd10 A B g g') (λh, ap (pi_functor f0 f1) (eq_of_homotopy h) =
     eq_of_homotopy (λa':A', (ap (f1 a') (h (f0 a'))))), intro p, clear h,
  induction p,
  refine (ap (ap (pi_functor f0 f1)) (eq_of_homotopy_idp g)) ⬝ _,
  symmetry, apply eq_of_homotopy_idp
  end

  /- Equivalences -/

  /-@[hott] def pi_equiv_pi (f0 : A' ≃ A) (f1 : Πa', (B (to_fun f0 a') ≃ B' a'))
    : (Πa, B a) ≃ (Πa', B' a') :=
  begin
    fapply equiv.MK,
    exact pi_functor f0 f1,
          (pi_functor f0⁻¹ᶠ
          (λ(a : A) (b' : B' (f0⁻¹ᶠ a)), transport B (right_inv f0 a) ((f1 (f0⁻¹ᶠ a))⁻¹ᶠ b')))
  end-/
  @[hott, instance] def is_equiv_pi_functor [H0 : is_equiv f0]
    [H1 : Πa', is_equiv (f1 a')] : is_equiv (pi_functor f0 f1) :=
  adjointify (pi_functor f0 f1) (pi_functor f0⁻¹ᶠ
          (λ(a : A) (b' : B' (f0⁻¹ᶠ a)), transport B (right_inv f0 a) ((f1 (f0⁻¹ᶠ a))⁻¹ᶠ b')))
    begin
      intro h, apply eq_of_homotopy, intro a', dsimp,
      rwr [adj f0 a', hott.eq.inverse (tr_compose B f0 (left_inv f0 a') _), fn_tr_eq_tr_fn _ f1 _, right_inv (f1 _)], --fix
      apply apdt
    end
    begin
      intro h, apply eq_of_homotopy, intro a, dsimp,
      rwr [left_inv (f1 _)],
      apply apdt
    end

  @[hott] def pi_equiv_pi_of_is_equiv [H : is_equiv f0]
    [H1 : Πa', is_equiv (f1 a')] : (Πa, B a) ≃ (Πa', B' a') :=
  equiv.mk (pi_functor f0 f1) (by apply_instance)

  @[hott] def pi_equiv_pi (f0 : A' ≃ A) (f1 : Πa', (B (f0 a') ≃ B' a'))
    : (Πa, B a) ≃ (Πa', B' a') :=
  pi_equiv_pi_of_is_equiv f0 (λa', f1 a')

  @[hott] def pi_equiv_pi_right {P Q : A → Type _} (g : Πa, P a ≃ Q a)
    : (Πa, P a) ≃ (Πa, Q a) :=
  pi_equiv_pi equiv.rfl g

  /- Equivalence if one of the types is contractible -/
  variable (B)
  @[hott] def pi_equiv_of_is_contr_left [H : is_contr A]
    : (Πa, B a) ≃ B (center A) :=
  begin
    fapply equiv.MK,
    { intro f, exact f (center A)},
    { intros b a, exact center_eq a ▸ b},
    { intro b, dsimp, rwr [prop_eq_of_is_contr (center_eq (center A)) idp]},
    { intro f, apply eq_of_homotopy, intro a, dsimp, induction (center_eq a),
      refl }
  end

  @[hott] def pi_equiv_of_is_contr_right [H : Πa, is_contr (B a)]
    : (Πa, B a) ≃ unit :=
  begin
    fapply equiv.MK,
    { intro f, exact star },
    { intros u a, exact center _ },
    { intro u, induction u, reflexivity },
    { intro f, apply eq_of_homotopy, intro a, apply is_prop.elim }
  end
  variable {B}

  /- Interaction with other type constructors -/

  -- most of these are in the file of the other type constructor

  @[hott] def pi_empty_left (B : empty → Type _) : (Πx, B x) ≃ unit :=
  begin
    fapply equiv.MK,
    { intro f, exact star },
    { intros x y, exact empty.elim y },
    { intro x, induction x, reflexivity },
    { intro f, apply eq_of_homotopy, intro y, exact empty.elim y }
  end

  @[hott] def pi_unit_left (B : unit → Type _) : (Πx, B x) ≃ B star :=
  pi_equiv_of_is_contr_left _

  @[hott] def pi_bool_left (B : bool → Type _) : (Πx, B x) ≃ B ff × B tt :=
  begin
    fapply equiv.MK,
    { intro f, exact (f ff, f tt) },
    { intros x b, induction x, induction b, all_goals {assumption}},
    { intro x, induction x, reflexivity },
    { intro f, apply eq_of_homotopy, intro b, induction b, all_goals {reflexivity}},
  end

  /- Truncatedness: any dependent product of n-types is an n-type -/

  @[hott, instance, priority 1520] theorem is_trunc_pi (B : A → Type _) (n : trunc_index)
      [H : ∀a, is_trunc n (B a)] : is_trunc n (Πa, B a) :=
  begin
    unfreezeI, induction n with n IH generalizing B H; resetI,
      { fapply is_contr.mk,
          intro a, apply center,
          intro f, apply eq_of_homotopy,
            intro x, apply (center_eq (f x)) },
      { apply is_trunc_succ_intro, intros f g,
          exact is_trunc_equiv_closed_rev n (eq_equiv_homotopy f g) (by apply_instance) }
  end

  @[hott] theorem is_trunc_pi_eq (n : trunc_index) (f g : Πa, B a)
      [H : ∀a, is_trunc n (f a = g a)] : is_trunc n (f = g) :=
  is_trunc_equiv_closed_rev n (eq_equiv_homotopy f g) (by apply_instance)

  @[hott, instance] theorem is_trunc_not (n : trunc_index) (A : Type _) : is_trunc (n.+1) ¬A :=
  by dsimp [not]; apply_instance

  @[hott] theorem is_prop_pi_eq (a : A) : is_prop (Π(a' : A), a = a') :=
  is_prop_of_imp_is_contr
  ( assume (f : Πa', a = a'),
    have is_contr A, from is_contr.mk a f,
    by unfreezeI; apply_instance)

  @[hott] theorem is_prop_neg (A : Type _) : is_prop (¬A) := by apply_instance
  @[hott] theorem is_prop_ne {A : Type _} (a b : A) : is_prop (a ≠ b) := by apply_instance

  @[hott] def is_contr_pi_of_neg {A : Type _} (B : A → Type _) (H : ¬ A) : is_contr (Πa, B a) :=
  begin
    apply is_contr.mk (λa, empty.elim (H a)), intro f, apply eq_of_homotopy, intro x, exact empty.elim (H x)
  end

  /- Symmetry of Π -/
  @[hott] def pi_flip {P : A → A' → Type _} (f : Πa b, P a b) (b : A') (a : A) : P a b := f a b
  @[hott, instance] def is_equiv_flip {P : A → A' → Type _}
    : is_equiv (@pi_flip A A' P) :=
  begin
    fapply is_equiv.mk,
    exact (@pi_flip _ _ (pi_flip P)),
    all_goals {intro f; refl}
  end

  @[hott] def pi_comm_equiv {P : A → A' → Type _} : (Πa b, P a b) ≃ (Πb a, P a b) :=
  equiv.mk (@pi_flip _ _ P) (by apply_instance)

  /- Dependent functions are equivalent to nondependent functions into the total space together
     with a homotopy -/
  @[hott] def pi_equiv_arrow_sigma_right {A : Type _} {B : A → Type _} (f : Πa, B a) :
    Σ(f : A → Σa, B a), sigma.fst ∘ f ~ id :=
  ⟨λa, ⟨a, f a⟩, λa, idp⟩

  @[hott] def pi_equiv_arrow_sigma_left
    (v : Σ(f : A → Σa, B a), sigma.fst ∘ f ~ id) (a : A) : B a :=
  transport B (v.2 a) (v.1 a).2

  open funext
  @[hott] def pi_equiv_arrow_sigma : (Πa, B a) ≃ Σ(f : A → Σa, B a), sigma.fst ∘ f ~ id :=
  begin
    fapply equiv.MK,
    { exact pi_equiv_arrow_sigma_right },
    { exact pi_equiv_arrow_sigma_left },
    { intro v, induction v with f p, fapply sigma_eq,
      { apply eq_of_homotopy, intro a, fapply sigma_eq,
        { exact (p a)⁻¹ },
        { apply inverseo, apply pathover_tr }},
      { apply pi_pathover_constant, intro a, apply eq_pathover_constant_right,
        refine ap_compose (λf : A → A, f a) _ _ ⬝ph _,
        refine ap02 _ (compose_eq_of_homotopy (@sigma.fst A B) _) ⬝ph _,
        refine ap_eq_apd10 _ _ ⬝ph _,
        refine apd10 (right_inv apd10 _) a ⬝ph _,
        refine sigma_eq_fst _ _ ⬝ph _, apply square_of_eq, exact (con.left_inv _)⁻¹ }},
    { intro a, reflexivity }
  end

end pi

namespace pi

  /- pointed pi types -/
  open pointed

  @[hott, instance] def pointed_pi {A : Type _} (P : A → Type _) [H : Πx, pointed (P x)]
      : pointed (Πx, P x) :=
  pointed.mk (λx, pt)

end pi
end hott