/-
Copyright (c) 2017 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Ulrik Buchholtz

Quotients. This is a quotient without truncation for an arbitrary type-valued binary relation.
See also .set_quotient
-/

/-
  The hit quotient is primitive, declared in init.hit.
  The constructors are, given {A : Type _} (R : A → A → Type _),
  * class_of : A → quotient R (A implicit, R explicit)
  * eq_of_rel : Π{a a' : A}, R a a' → class_of a = class_of a' (R explicit)
-/

import arity cubical.squareover types.arrow cubical.pathover2 types.pointed
universes u v w
hott_theory

namespace hott
open hott.eq equiv hott.pi is_trunc pointed hott.sigma

namespace quotient

  variables {A : Type _} {R : A → A → Type _}

 @[hott, induction, priority 1500] protected def elim {P : Type _} (Pc : A → P) (Pp : Π⦃a a' : A⦄ (H : R a a'), Pc a = Pc a')
    (x : quotient R) : P :=
  begin hinduction x, exact Pc a, exact pathover_of_eq _ (Pp H) end

  @[hott, reducible] protected def elim_on {P : Type _} (x : quotient R)
    (Pc : A → P) (Pp : Π⦃a a' : A⦄ (H : R a a'), Pc a = Pc a') : P :=
  quotient.elim Pc Pp x

  @[hott] theorem elim_eq_of_rel {P : Type _} (Pc : A → P)
    (Pp : Π⦃a a' : A⦄ (H : R a a'), Pc a = Pc a') {a a' : A} (H : R a a')
    : ap (quotient.elim Pc Pp) (eq_of_rel R H) = Pp H :=
  begin
    apply eq_of_fn_eq_fn_inv ((pathover_constant (eq_of_rel R H)) _ _),
    exact sorry --rwr [▸*,-apd_eq_pathover_of_eq_ap,↑quotient.elim,rec_eq_of_rel],
  end

  @[hott] protected def rec_prop {A : Type _} {R : A → A → Type _} {P : quotient R → Type _}
    [H : Πx, is_prop (P x)] (Pc : Π(a : A), P (class_of R a)) (x : quotient R) : P x :=
  quotient.rec Pc (λa a' H, is_prop.elimo _ _ _) x

  @[hott] protected def elim_prop {P : Type _} [H : is_prop P] (Pc : A → P) (x : quotient R) : P :=
  quotient.elim Pc (λa a' H, is_prop.elim _ _) x

  @[hott] protected def elim_type (Pc : A → Type _)
    (Pp : Π⦃a a' : A⦄ (H : R a a'), Pc a ≃ Pc a') : quotient R → Type _ :=
  quotient.elim Pc (λa a' H, ua (Pp H))

  @[hott, reducible] protected def elim_type_on (x : quotient R) (Pc : A → Type _)
    (Pp : Π⦃a a' : A⦄ (H : R a a'), Pc a ≃ Pc a') : Type _ :=
  quotient.elim_type Pc Pp x

  @[hott] theorem elim_type_eq_of_rel_fn (Pc : A → Type _)
    (Pp : Π⦃a a' : A⦄ (H : R a a'), Pc a ≃ Pc a') {a a' : A} (H : R a a')
    : transport (quotient.elim_type Pc Pp) (eq_of_rel R H) = to_fun (Pp H) :=
  by exact sorry --rewrite [tr_eq_cast_ap_fn, ↑quotient.elim_type, elim_eq_of_rel]; apply cast_ua_fn

  -- rename to elim_type_eq_of_rel_fn_inv
  @[hott] theorem elim_type_eq_of_rel_inv (Pc : A → Type _)
    (Pp : Π⦃a a' : A⦄ (H : R a a'), Pc a ≃ Pc a') {a a' : A} (H : R a a')
    : transport (quotient.elim_type Pc Pp) (eq_of_rel R H)⁻¹ = to_inv (Pp H) :=
  by exact sorry --rewrite [tr_eq_cast_ap_fn, ↑quotient.elim_type, ap_inv, elim_eq_of_rel]; apply cast_ua_inv_fn

  -- remove '
  @[hott] theorem elim_type_eq_of_rel_inv' (Pc : A → Type _)
    (Pp : Π⦃a a' : A⦄ (H : R a a'), Pc a ≃ Pc a') {a a' : A} (H : R a a') (x : Pc a')
    : transport (quotient.elim_type Pc Pp) (eq_of_rel R H)⁻¹ x = to_inv (Pp H) x :=
  ap10 (elim_type_eq_of_rel_inv Pc Pp H) x

  @[hott] theorem elim_type_eq_of_rel (Pc : A → Type u)
    (Pp : Π⦃a a' : A⦄ (H : R a a'), Pc a ≃ Pc a') {a a' : A} (H : R a a') (p : Pc a)
    : transport (quotient.elim_type Pc Pp) (eq_of_rel R H) p = to_fun (Pp H) p :=
  ap10 (elim_type_eq_of_rel_fn Pc Pp H) p

  @[hott] def elim_type_eq_of_rel' (Pc : A → Type _)
    (Pp : Π⦃a a' : A⦄ (H : R a a'), Pc a ≃ Pc a') {a a' : A} (H : R a a') (p : Pc a)
    : @pathover _ (class_of _ a) (quotient.elim_type Pc Pp) p _ (eq_of_rel R H) (to_fun (Pp H) p) :=
  pathover_of_tr_eq (elim_type_eq_of_rel Pc Pp H p)

  @[hott] def elim_type_uncurried (H : Σ(Pc : A → Type _),  Π⦃a a' : A⦄ (H : R a a'), Pc a ≃ Pc a')
    : quotient R → Type _ :=
  quotient.elim_type H.1 H.2
end quotient

namespace quotient

  section
    variables {A : Type _} (R : A → A → Type _)

    /- The dependent universal property -/
    @[hott] def quotient_pi_equiv (C : quotient R → Type _) : (Πx, C x) ≃
      (Σ(f : Π(a : A), C (class_of R a)),  Π⦃a a' : A⦄ (H : R a a'), f a =[eq_of_rel R H] f a') :=
    begin
      fapply equiv.MK,
      { intro f, exact ⟨λa, f (class_of R a), λa a' H, apd f (eq_of_rel R H)⟩},
      { intros v x, induction v with i p, hinduction x,
          exact (i a),
          exact (p H)},
      { intro v, induction v with i p, 
        apply ap (sigma.mk i), apply eq_of_homotopy3, intros a a' H, apply rec_eq_of_rel},
      { intro f, apply eq_of_homotopy, intro x, hinduction x, reflexivity, 
        apply eq_pathover_dep, rwr rec_eq_of_rel, exact hrflo},
    end
  end

  @[hott] def pquotient {A : Type*} (R : A → A → Type _) : Type* :=
  pType.mk (quotient R) (class_of R pt)

  /- the flattening lemma -/

  namespace flattening
  section

    parameters {A : Type u} (R : A → A → Type v) (C : A → Type w) (f : Π⦃a a'⦄, R a a' → C a ≃ C a')
    include f
    variables {a a' : A} {r : R a a'}

    private def P := quotient.elim_type C f

    @[hott] def flattening_type : Type (max u w) := Σa, C a
    private def X := flattening_type
    inductive flattening_rel : X → X → Type (max u v w)
    | mk : Π⦃a a' : A⦄ (r : R a a') (c : C a), flattening_rel ⟨a, c⟩ ⟨a', f r c⟩

    @[hott] def Ppt (c : C a) : sigma P :=
    ⟨class_of R a, c⟩

    @[hott] def Peq (r : R a a') (c : C a) : Ppt c = Ppt (f r c) :=
    begin
      fapply sigma_eq,
      { apply eq_of_rel R r},
      { refine elim_type_eq_of_rel' C f r c}
    end

    @[hott] def rec {Q : sigma P → Type _} (Qpt : Π{a : A} (x : C a), Q (Ppt x))
      (Qeq : Π⦃a a' : A⦄ (r : R a a') (c : C a), Qpt c =[Peq r c] Qpt (f r c))
      (v : sigma P) : Q v :=
    begin
      induction v with q p,
      hinduction q,
      { exact Qpt p},
      { apply pi_pathover_left, intro c,
        refine _ ⬝op apdt Qpt (elim_type_eq_of_rel C f H c)⁻¹ᵖ,
        refine _ ⬝op (tr_compose Q (Ppt R C f) _ _)⁻¹,
        rwr ap_inv,
        refine pathover_cancel_right _ (tr_pathover _ _)⁻¹ᵒ,
        refine change_path _ (Qeq H c),
        symmetry, dsimp [Ppt, Peq],
        refine whisker_left _ (ap_dpair _) ⬝ _,
        refine (dpair_eq_dpair_con _ _ _ _)⁻¹ ⬝ _, 
        apply ap (dpair_eq_dpair _),
        exact sorry
        -- dsimp [elim_type_eq_of_rel',pathover_idp_of_eq],
        -- exact (pathover_of_tr_eq_eq_concato _ _ _)⁻¹
        },
    end

    @[hott] def elim {Q : Type _} (Qpt : Π{a : A}, C a → Q)
      (Qeq : Π⦃a a' : A⦄ (r : R a a') (c : C a), Qpt c = Qpt (f r c))
      (v : sigma P) : Q :=
    begin
      induction v with q p,
      hinduction q,
      { exact Qpt p},
      { apply arrow_pathover_constant_right, 
        intro c, exact Qeq H c ⬝ ap Qpt (elim_type_eq_of_rel C f H c)⁻¹},
    end

    @[hott] theorem elim_Peq {Q : Type _} (Qpt : Π{a : A}, C a → Q)
      (Qeq : Π⦃a a' : A⦄ (r : R a a') (c : C a), Qpt c = Qpt (f r c)) {a a' : A} (r : R a a')
      (c : C a) : ap (elim @Qpt Qeq) (Peq r c) = Qeq r c :=
    begin
      refine ap_dpair_eq_dpair _ _ _ ⬝ _, exact sorry
      -- refine apd011_eq_apo11_apd _ _ _ ⬝ _,
      -- rwr [rec_eq_of_rel],
      -- refine !apo11_arrow_pathover_constant_right ⬝ _,
      -- rwr [↑elim_type_eq_of_rel', to_right_inv !pathover_equiv_tr_eq, ap_inv],
      -- apply inv_con_cancel_right
    end

    open flattening_rel
    @[hott] def flattening_lemma : sigma P ≃ quotient flattening_rel :=
    begin
      fapply equiv.MK,
      { refine elim R C f _ _,
        { intros a c, exact class_of _ ⟨a, c⟩},
        { intros a a' r c, apply eq_of_rel, constructor}},
      { intro q, hinduction q with x x x' H,
        { exact Ppt R C f x.2},
        { induction H, apply Peq}},
      { intro q, hinduction q with x x x' H,
        { induction x with a c, reflexivity},
        { induction H, apply eq_pathover, apply hdeg_square,
          refine ap_compose (elim R C f _ _) (quotient.elim _ _) _ ⬝ _,
          rwr [elim_eq_of_rel, ap_id],
          apply elim_Peq }},
      { refine rec R C f (λa x, idp) _, intros,
        apply eq_pathover, apply hdeg_square,
          refine ap_compose (quotient.elim _ _) (elim R C f _ _) _ ⬝ _,
          rwr [elim_Peq, ap_id],
          apply elim_eq_of_rel }
    end

  end
  end flattening

  section
  open is_equiv equiv prod
  variables {A : Type _} (R : A → A → Type _)
             {B : Type _} (Q : B → B → Type _)
             (f : A → B) (k : Πa a' : A, R a a' → Q (f a) (f a'))
  include f k

  @[hott] protected def functor : quotient R → quotient Q :=
  quotient.elim (λa, class_of Q (f a)) (λa a' r, eq_of_rel Q (k a a' r))

  variables [F : is_equiv f] [K : Πa a', is_equiv (k a a')]
  include F K

  @[hott] protected def functor_inv : quotient Q → quotient R :=
  quotient.elim (λb, class_of R (f⁻¹ᶠ b))
                (λb b' q, eq_of_rel R ((k (f⁻¹ᶠ b) (f⁻¹ᶠ b'))⁻¹ᶠ
                          ((right_inv f b)⁻¹ ▸ (right_inv f b')⁻¹ ▸ q)))

/- To do: redo this proof -/
  @[hott] instance is_equiv : is_equiv (quotient.functor R Q f k) := sorry
  -- begin
  --   fapply adjointify _ (quotient.functor_inv R Q f k),
  --   { intro qb, hinduction qb with b b b' q,
  --     { apply ap (class_of Q), apply right_inv },
  --     { apply eq_pathover, rwr [ap_id,ap_compose' (quotient.elim _ _)],
  --       do 2 krewrite elim_eq_of_rel, rewrite (right_inv (k (f⁻¹ b) (f⁻¹ b'))),
  --       have H1 : pathover (λz : B × B, Q z.1 z.2)
  --         ((right_inv f b)⁻¹ ▸ (right_inv f b')⁻¹ ▸ q)
  --         (prod_eq (right_inv f b) (right_inv f b')) q,
  --       begin apply pathover_of_eq_tr, krewrite [prod_eq_inv,prod_eq_transport] end,
  --       have H2 : square
  --         (ap (λx : (Σz : B × B, Q z.1 z.2), class_of Q x.1.1)
  --           (sigma_eq (prod_eq (right_inv f b) (right_inv f b')) H1))
  --         (ap (λx : (Σz : B × B, Q z.1 z.2), class_of Q x.1.2)
  --           (sigma_eq (prod_eq (right_inv f b) (right_inv f b')) H1))
  --         (eq_of_rel Q ((right_inv f b)⁻¹ ▸ (right_inv f b')⁻¹ ▸ q))
  --         (eq_of_rel Q q),
  --       from
  --         natural_square_tr (λw : (Σz : B × B, Q z.1 z.2), eq_of_rel Q w.2)
  --         (sigma_eq (prod_eq (right_inv f b) (right_inv f b')) H1),
  --       krewrite (ap_compose' (class_of Q)) at H2,
  --       krewrite (ap_compose' (λz : B × B, z.1)) at H2,
  --       rewrite sigma.ap_fst at H2, rewrite sigma_eq_fst at H2,
  --       krewrite prod.ap_fst at H2, krewrite prod_eq_fst at H2,
  --       krewrite (ap_compose' (class_of Q) (λx : (Σz : B × B, Q z.1 z.2), x.1.2)) at H2,
  --       krewrite (ap_compose' (λz : B × B, z.2)) at H2,
  --       rewrite sigma.ap_fst at H2, rewrite sigma_eq_fst at H2,
  --       krewrite prod.ap_snd at H2, krewrite prod_eq_snd at H2,
  --       apply H2 } },
  --   { intro qa, induction qa with a a a' r,
  --     { apply ap (class_of R), apply left_inv },
  --     { apply eq_pathover, rewrite [ap_id,(ap_compose' (quotient.elim _ _))],
  --       do 2 krewrite elim_eq_of_rel,
  --       have H1 : pathover (λz : A × A, R z.1 z.2)
  --         ((left_inv f a)⁻¹ ▸ (left_inv f a')⁻¹ ▸ r)
  --         (prod_eq (left_inv f a) (left_inv f a')) r,
  --       begin apply pathover_of_eq_tr, krewrite [prod_eq_inv,prod_eq_transport] end,
  --       have H2 : square
  --         (ap (λx : (Σz : A × A, R z.1 z.2), class_of R x.1.1)
  --           (sigma_eq (prod_eq (left_inv f a) (left_inv f a')) H1))
  --         (ap (λx : (Σz : A × A, R z.1 z.2), class_of R x.1.2)
  --           (sigma_eq (prod_eq (left_inv f a) (left_inv f a')) H1))
  --         (eq_of_rel R ((left_inv f a)⁻¹ ▸ (left_inv f a')⁻¹ ▸ r))
  --         (eq_of_rel R r),
  --       begin
  --         exact
  --         natural_square_tr (λw : (Σz : A × A, R z.1 z.2), eq_of_rel R w.2)
  --         (sigma_eq (prod_eq (left_inv f a) (left_inv f a')) H1)
  --       end,
  --       krewrite (ap_compose' (class_of R)) at H2,
  --       krewrite (ap_compose' (λz : A × A, z.1)) at H2,
  --       rewrite sigma.ap_fst at H2, rewrite sigma_eq_fst at H2,
  --       krewrite prod.ap_fst at H2, krewrite prod_eq_fst at H2,
  --       krewrite (ap_compose' (class_of R) (λx : (Σz : A × A, R z.1 z.2), x.1.2)) at H2,
  --       krewrite (ap_compose' (λz : A × A, z.2)) at H2,
  --       rewrite sigma.ap_fst at H2, rewrite sigma_eq_fst at H2,
  --       krewrite prod.ap_snd at H2, krewrite prod_eq_snd at H2,
  --       have H3 :
  --         (k (f⁻¹ (f a)) (f⁻¹ (f a')))⁻¹
  --         ((right_inv f (f a))⁻¹ ▸ (right_inv f (f a'))⁻¹ ▸ k a a' r)
  --         = (left_inv f a)⁻¹ ▸ (left_inv f a')⁻¹ ▸ r,
  --       begin
  --         rewrite [adj f a,adj f a',ap_inv',ap_inv'],
  --         rewrite [-(tr_compose _ f (left_inv f a')⁻¹ (k a a' r)),
  --                  -(tr_compose _ f (left_inv f a)⁻¹)],
  --         rewrite [-(fn_tr_eq_tr_fn (left_inv f a')⁻¹ (λx, k a x) r),
  --                  -(fn_tr_eq_tr_fn (left_inv f a)⁻¹
  --                    (λx, k x (f⁻¹ (f a')))),
  --                  left_inv (k _ _)]
  --       end,
  --       rewrite H3, apply H2 } }
  -- end
end

section
  variables {A : Type _} (R : A → A → Type _)
             {B : Type _} (Q : B → B → Type _)
             (f : A ≃ B) (k : Πa a' : A, R a a' ≃ Q (f a) (f a'))
  include f k

  /- This could also be proved using ua, but then it wouldn't compute -/
  @[hott] protected def equiv : quotient R ≃ quotient Q :=
  equiv.mk (quotient.functor R Q f (λa a', k a a')) (quotient.is_equiv _ _ _ _)
end


end quotient
end hott