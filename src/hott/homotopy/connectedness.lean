/-
Copyright (c) 2015 Ulrik Buchholtz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ulrik Buchholtz, Floris van Doorn

Connectedness of types and functions
-/
import ..types.trunc ..types.arrow_2 ..types.lift
universes u v w
hott_theory
namespace hott

open is_trunc hott.is_equiv hott.nat nat hott.equiv trunc hott.function fiber hott.funext hott.pi pointed

@[hott, reducible] def is_conn (n : ℕ₋₂) (A : Type _) : Type _ :=
is_contr (trunc n A)

@[hott, reducible] def is_conn_fun (n : ℕ₋₂) {A B : Type _} (f : A → B) : Type _ :=
Πb : B, is_conn n (fiber f b)

@[hott, reducible] def is_conn_inf (A : Type _) : Type _ := Πn, is_conn n A
@[hott, reducible] def is_conn_fun_inf {A B : Type _} (f : A → B) : Type _ := Πn, is_conn_fun n f

namespace is_conn

  @[hott] def is_conn_equiv_closed (n : ℕ₋₂) {A B : Type _}
    : A ≃ B → is_conn n A → is_conn n B :=
  begin
    intros H C,
    napply @is_contr_equiv_closed (trunc n A) _,
    exact trunc_equiv_trunc n H,
    infer
  end

  @[hott] theorem is_conn_of_le (A : Type _) {n k : ℕ₋₂} (H : n ≤ k) [is_conn k A] : is_conn n A :=
  begin
    napply is_contr_equiv_closed,
    apply trunc_trunc_equiv_left _ H,
    apply_instance
  end

  @[hott] theorem is_conn_fun_of_le {A B : Type _} (f : A → B) {n k : ℕ₋₂} (H : n ≤ k)
    [is_conn_fun k f] : is_conn_fun n f :=
  λb, is_conn_of_le _ H

  @[hott] def is_conn_of_is_conn_succ (n : ℕ₋₂) (A : Type _) [is_conn (n.+1) A] : is_conn n A :=
  is_trunc_trunc_of_le A -2 (trunc_index.self_le_succ n)

  namespace is_conn_fun
  section
    parameters (n : ℕ₋₂) {A : Type _} {B : Type _} {h : A → B}
               (H : is_conn_fun n h) (P : B → Type _) [Πb, is_trunc n (P b)]

    @[hott] private def rec.helper : (Πa : A, P (h a)) → Πb : B, trunc n (fiber h b) → P b :=
    λt b, trunc.rec (λx, point_eq x ▸ t (point x))

    @[hott] private def rec.g : (Πa : A, P (h a)) → (Πb : B, P b) :=
    λt b, rec.helper t b (@center (trunc n (fiber h b)) (H b))

    -- induction principle for n-connected maps (@[hott] lemma 7.5.7)
    @[hott] protected def rec : is_equiv (λs : Πb : B, P b, λa : A, s (h a)) :=
    adjointify (λs a, s (h a)) rec.g
    begin
      intro t, apply eq_of_homotopy, intro a, dsimp [rec.g, rec.helper],
      rwr [@center_eq _ (H (h a)) (tr (fiber.mk a idp))],
    end
    begin
      intro k, apply eq_of_homotopy, intro b, dsimp [rec.g],
      hinduction @center _ (H b) with q p, hinduction p with a p, induction p, refl
    end

    @[hott] protected def elim : (Πa : A, P (h a)) → (Πb : B, P b) :=
    @is_equiv.inv _ _ (λ(s : Πb : B, P b) a, s (h a)) rec

    @[hott] protected def elim_β : Πf : (Πa : A, P (h a)), Πa : A, elim f (h a) = f a :=
    λf, apd10 (@is_equiv.right_inv _ _ (λ(s : Πb : B, P b) a, s (h a)) rec f)

  end

  section
    parameters (n k : ℕ₋₂) {A : Type _} {B : Type _} {f : A → B}
               (H : is_conn_fun n f) (P : B → Type _) [HP : Πb, is_trunc (n +2+ k) (P b)]

    include H HP
    -- @[hott] lemma 8.6.1
    @[hott] lemma elim_general : is_trunc_fun k (pi_functor_left f P) :=
    begin
      unfreezeI, revert P HP,
      induction k with k IH; intros P HP t,
      { napply is_contr_fiber_of_is_equiv, napply is_conn_fun.rec, exact H, exact HP },
      { napply is_trunc_succ_intro,
        intros x y, cases x with g p, cases y with h q,
        have e : fiber (λr : g ~ h, (λa, r (f a))) (apd10 (p ⬝ q⁻¹))
                 ≃ (fiber.mk g p = fiber.mk h q
                     :> fiber (λs : (Πb, P b), (λa, s (f a))) t),
        begin
          apply equiv.trans (fiber.sigma_char _ _),
          have e' : Πr : g ~ h,
                 ((λa, r (f a)) = apd10 (p ⬝ q⁻¹))
               ≃ (ap (λv : Πb, P b, (λa, v (f a))) (eq_of_homotopy r) ⬝ q = p),
          begin
            intro r,
            refine equiv.trans _ (eq_con_inv_equiv_con_eq q p
                                   (ap (λ(v : Πb, P b) a, v (f a)) (eq_of_homotopy r))),
            rwr [←apd10_eq_of_homotopy r],
            rwr [←(apd10_ap_precompose_dependent f (eq_of_homotopy r)), apd10_eq_of_homotopy r],
            symmetry,
            apply eq_equiv_fn_eq (@apd10 A (λa, P (f a)) (λa, g (f a)) (λa, h (f a)))
          end,
          refine sigma.sigma_equiv_sigma_right e' ⬝e _, clear e',
          refine (sigma.sigma_equiv_sigma_left (λr : g = h, ap _ r ⬝ q = p)
            (eq_equiv_homotopy _ _))⁻¹ᵉ ⬝e _,
          symmetry, apply equiv.trans (fiber_eq_equiv _ _),
          apply sigma.sigma_equiv_sigma_right, intro r,
          apply eq_equiv_eq_symm
        end,
        apply @is_trunc_equiv_closed _ _ k e, clear e,
        exact @IH (λb : B, (g b = h b)) (λb, @is_trunc_eq (P b) (n +2+ k) (HP b) (g b) (h b)) _
        }
    end

  end

  section
    parameters (n : ℕ₋₂) {A : Type u} {B : Type v} {h : A → B}
    parameter sec : ΠP : B → trunctype.{max u v} n,
                    is_retraction (λs : (Πb : B, P b), λ a, s (h a))

    @[hott] private abbreviation s := sec (λb, trunctype.mk' n (trunc n (fiber h b)))

    include sec

    -- the other half of @[hott] lemma 7.5.7
    @[hott] def intro : is_conn_fun n h :=
    begin
      intro b,
      apply is_contr.mk (@is_retraction.sect _ _ _ (s n sec) (λa, tr (fiber.mk a idp)) b),
      intro x, dsimp at x, hinduction x with p, hinduction p with a p,
      apply transport
               (λz : (Σy, h a = y), @sect _ _ _ (s n sec) (λa, tr (mk a idp)) (sigma.fst z) =
                                    tr (fiber.mk a (sigma.snd z)))
               (@center_eq _ (is_contr_sigma_eq (h a)) (sigma.mk b p)),

      exact apd10 (@hott.function.right_inverse _ _ _ (s n sec) (λa, tr (fiber.mk a idp))) a
    end
  end
  end is_conn_fun

  -- Connectedness is related to maps to and from the unit type, first to
  section
    parameters (n : ℕ₋₂) (A : Type _)

    @[hott] def is_conn_of_map_to_unit
      : is_conn_fun n (const A unit.star) → is_conn n A :=
    begin
      intro H, dsimp [is_conn_fun] at H,
      exact is_conn_equiv_closed n (fiber.fiber_star_equiv A) (by infer),
    end

    @[hott] def is_conn_fun_to_unit_of_is_conn [H : is_conn n A] :
      is_conn_fun n (const A unit.star) :=
    begin
      intro u, induction u,
      exact is_conn_equiv_closed n (fiber.fiber_star_equiv A)⁻¹ᵉ (by infer),
    end

    -- now maps from unit
    @[hott] def is_conn_of_map_from_unit (a₀ : A) (H : is_conn_fun n (const unit a₀))
      : is_conn n .+1 A :=
    is_contr.mk (tr a₀)
    begin
      apply trunc.rec, intro a,
      exact trunc.elim (λz : fiber (const unit a₀) a, ap tr (point_eq z))
                            (@center _ (H a))
    end

    @[hott] def is_conn_fun_from_unit (a₀ : A) [H : is_conn n .+1 A]
      : is_conn_fun n (const unit a₀) :=
    begin
      intro a,
      apply is_conn_equiv_closed n (equiv.symm (fiber_const_equiv A a₀ a)),
      apply @is_contr_equiv_closed _ _ (tr_eq_tr_equiv n a₀ a),
    end

  end

  -- as special case we get elimination principles for pointed connected types
  namespace is_conn
    open pointed unit
    section
      parameters (n : ℕ₋₂) {A : Type*}
                 [H : is_conn n .+1 A] (P : A → Type _) [Πa, is_trunc n (P a)]

      include H
      @[hott] protected def rec : is_equiv (λs : Πa : A, P a, s (Point A)) :=
      @is_equiv_compose
        (Πa : A, P a) (unit → P (Point A)) (P (Point A))
        (λf, f unit.star) (λs x, s (Point A))
        (is_conn_fun.rec n (is_conn_fun_from_unit n A (Point A)) P)
        (to_is_equiv (arrow_unit_left (P (Point A))))

      @[hott] protected def elim : P (Point A) → (Πa : A, P a) :=
      @is_equiv.inv _ _ (λ(s : Πa : A, P a), s (Point A)) rec

      @[hott] protected def elim_β (p : P (Point A)) : elim p (Point A) = p :=
      @is_equiv.right_inv _ _ (λ(s : Πa : A, P a), s (Point A)) rec p
    end

    section
      parameters (n k : ℕ₋₂) {A : Type*}
                 [H : is_conn n .+1 A] (P : A → Type _) [Πa, is_trunc (n +2+ k) (P a)]

      include H
      @[hott] lemma elim_general (p : P (Point A))
        : is_trunc k (fiber (λs : (Πa : A, P a), s (Point A)) p) :=
      @is_trunc_equiv_closed _ _ k
        (equiv.symm (fiber.equiv_postcompose _ (arrow_unit_left (P (Point A))) _))
        (is_conn_fun.elim_general n k (is_conn_fun_from_unit n A (Point A)) P (λx, p))
    end
  end is_conn

  -- @[hott] lemma 7.5.2
  @[hott] def minus_one_conn_of_surjective {A B : Type _} (f : A → B)
    : is_surjective f → is_conn_fun -1 f :=
  begin
    intro H, intro b,
    exact @is_contr_of_inhabited_prop (∥fiber f b∥) (is_trunc_trunc -1 (fiber f b)) (H b),
  end

  @[hott] def is_surjection_of_minus_one_conn {A B : Type _} (f : A → B)
    : is_conn_fun -1 f → is_surjective f :=
  begin
    intro H, intro b,
    exact @center (∥fiber f b∥) (H b),
  end

  @[hott] def merely_of_minus_one_conn {A : Type _} : is_conn -1 A → ∥A∥ :=
  λH, @center (∥A∥) H

  @[hott] def minus_one_conn_of_merely {A : Type _} : ∥A∥ → is_conn -1 A :=
  @is_contr_of_inhabited_prop (∥A∥) (is_trunc_trunc -1 A)

  section
    open hott.arrow

    variables {f : arrow} {g : arrow}

    -- @[hott] lemma 7.5.4
    @[hott, instance] def retract_of_conn_is_conn (r : arrow_hom f g) [H : arrow.is_retraction r]
      (n : ℕ₋₂) [K : is_conn_fun n f] : is_conn_fun n g :=
    begin
      intro b, dsimp [is_conn],
      apply is_contr_retract (trunc_functor n (retraction_on_fiber r b)),
      exact K (r.sect.on_cod b)
    end

  end

  -- Corollary 7.5.5
  @[hott] def is_conn_homotopy (n : ℕ₋₂) {A B : Type _} {f g : A → B}
    (p : f ~ g) (H : is_conn_fun n f) : is_conn_fun n g :=
  @retract_of_conn_is_conn _ _
    (arrow.arrow_hom_of_homotopy p) (arrow.is_retraction_arrow_hom_of_homotopy p) n H

  -- all types are -2-connected
  @[hott] def is_conn_minus_two (A : Type _) : is_conn -2 A :=
  by apply_instance

  -- merely inhabited types are -1-connected
  @[hott] def is_conn_minus_one (A : Type _) (a : ∥ A ∥) : is_conn -1 A :=
  is_contr.mk a (is_prop.elim _)

  @[hott, instance] def is_conn_minus_one_pointed (A : Type*) : is_conn -1 A :=
  is_conn_minus_one A (tr pt)

  @[hott, instance] def is_conn_trunc (A : Type _) (n k : ℕ₋₂) [H : is_conn n A]
    : is_conn n (trunc k A) :=
  begin
    apply is_trunc_equiv_closed, apply trunc_trunc_equiv_trunc_trunc, apply_instance
  end

  @[hott, instance] def is_conn_eq (n : ℕ₋₂) {A : Type _} (a a' : A) [is_conn (n.+1) A] :
    is_conn n (a = a') :=
  begin
    apply is_trunc_equiv_closed, apply tr_eq_tr_equiv, apply_instance
  end

  @[hott, instance] def is_conn_loop (n : ℕ₋₂) (A : Type*) [is_conn (n.+1) A] : is_conn n (Ω A) :=
  is_conn_eq n pt pt

  open pointed
  @[hott, instance] def is_conn_ptrunc (A : Type*) (n k : ℕ₋₂) [H : is_conn n A]
    : is_conn n (ptrunc k A) :=
  is_conn_trunc A n k

  -- the following trivial cases are solved by type class inference
  @[hott] def is_conn_of_is_contr (k : ℕ₋₂) (A : Type _) [is_contr A] : is_conn k A :=
  by apply_instance
  @[hott] def is_conn_fun_of_is_equiv (k : ℕ₋₂) {A B : Type _} (f : A → B) [is_equiv f] :
    is_conn_fun k f :=
  by apply_instance

  -- @[hott] lemma 7.5.14
  @[hott, instance] theorem is_equiv_trunc_functor_of_is_conn_fun {A B : Type _} (n : ℕ₋₂) (f : A → B)
    [H : is_conn_fun n f] : is_equiv (trunc_functor n f) :=
  begin
    fapply adjointify,
    { intro b, hinduction b with b, exact trunc_functor n point (center (trunc n (fiber f b)))},
    { intro b, hinduction b with b, dsimp, hinduction center (trunc n (fiber f b)) with q v,
      hinduction v with a p, exact ap tr p },
    { intro a, hinduction a with a, dsimp, rwr [center_eq (tr (fiber.mk a idp))]}
  end

  @[hott] theorem trunc_equiv_trunc_of_is_conn_fun {A B : Type _} (n : ℕ₋₂) (f : A → B)
    [H : is_conn_fun n f] : trunc n A ≃ trunc n B :=
  equiv.mk (trunc_functor n f) (is_equiv_trunc_functor_of_is_conn_fun n f)

  @[hott] def is_conn_fun_trunc_functor_of_le {n k : ℕ₋₂} {A B : Type _} (f : A → B) (H : k ≤ n)
    [H2 : is_conn_fun k f] : is_conn_fun k (trunc_functor n f) :=
  begin
    apply is_conn_fun.intro,
    intro P, haveI : Πb, is_trunc n (P b), from λb, is_trunc_of_le _ H,
    fconstructor,
    { intros f' b, resetI, hinduction b with b, 
      refine @is_conn_fun.elim k _ _ _ H2 _ _ _ b, intro a, exact f' (tr a) },
    { intro f', apply eq_of_homotopy, intro a, dsimp,
      resetI, hinduction a using trunc.rec with a, dsimp, rwr [is_conn_fun.elim_β] }
  end

  @[hott] def is_conn_fun_trunc_functor_of_ge {n k : ℕ₋₂} {A B : Type _} (f : A → B) (H : n ≤ k)
    [H2 : is_conn_fun k f] : is_conn_fun k (trunc_functor n f) :=
  begin
    napply is_conn_fun_of_is_equiv,
    apply is_equiv_trunc_functor_of_le f H
  end

  -- Exercise 7.18
  @[hott] def is_conn_fun_trunc_functor {n k : ℕ₋₂} {A B : Type _} (f : A → B)
    [H2 : is_conn_fun k f] : is_conn_fun k (trunc_functor n f) :=
  begin
    eapply algebra.le_by_cases k n; intro H,
    { exact is_conn_fun_trunc_functor_of_le f H},
    { exact is_conn_fun_trunc_functor_of_ge f H}
  end

  open hott.ulift
  @[hott] def is_conn_fun_lift_functor (n : ℕ₋₂) {A B : Type _} (f : A → B) [is_conn_fun n f] :
    is_conn_fun n (ulift_functor f) :=
  begin
    intro b, cases b with b, apply is_trunc_equiv_closed_rev,
    { apply trunc_equiv_trunc, apply fiber_ulift_functor },
    apply_instance
  end

  open trunc_index
  @[hott] def is_conn_fun_inf.mk_nat {A B : Type _} {f : A → B} (H : Π(n : ℕ), is_conn_fun n f)
    : is_conn_fun_inf f :=
  begin
    intro n,
    cases n with n, { apply_instance },
    cases n with n, { have : -1 ≤ ↑0, from dec_star, exact is_conn_fun_of_le f this },
    change is_conn_fun (n.+2) f, rwr [←of_nat_add_two n], apply_instance
  end

  @[hott] def is_conn_inf.mk_nat {A : Type _} (H : Π(n : ℕ), is_conn n A) : is_conn_inf A :=
  begin
    intro n,
    cases n with n, { apply_instance },
    cases n with n, { have : -1 ≤ ↑0, from dec_star, apply is_conn_of_le A this},
    change is_conn (n.+2) A, rwr ←of_nat_add_two, apply_instance
  end

  @[hott] def is_conn_equiv_closed_rev (n : ℕ₋₂) {A B : Type _} (f : A ≃ B) (H : is_conn n B) :
    is_conn n A :=
  is_conn_equiv_closed n f⁻¹ᵉ (by apply_instance)

  @[hott] def is_conn_succ_intro {n : ℕ₋₂} {A : Type _} (a : trunc (n.+1) A)
    (H2 : Π(a a' : A), is_conn n (a = a')) : is_conn (n.+1) A :=
  begin
    napply is_contr_of_inhabited_prop,
    { apply is_trunc_succ_intro,
      refine trunc.rec _, intro a, refine trunc.rec _, intro a',
      apply is_contr_equiv_closed (tr_eq_tr_equiv _ _ _)⁻¹ᵉ, apply_instance },
    exact a
  end

  @[hott] def is_conn_pathover (n : ℕ₋₂) {A : Type _} {B : A → Type _} {a a' : A} (p : a = a') (b : B a)
    (b' : B a') [is_conn (n.+1) (B a')] : is_conn n (b =[p] b') :=
  is_conn_equiv_closed_rev n (pathover_equiv_tr_eq _ _ _) (by apply_instance)

  open hott.sigma
  @[hott, instance] lemma is_conn_sigma {A : Type _} (B : A → Type _) (n : ℕ₋₂)
    [HA : is_conn n A] [HB : Πa, is_conn n (B a)] : is_conn n (Σa, B a) :=
  begin
    unfreezeI, induction n with n IH generalizing A B HA HB,
    { apply is_conn_minus_two },
    apply is_conn_succ_intro,
    { resetI, hinduction center (trunc (n.+1) A) with q a,
      hinduction center (trunc (n.+1) (B a)) with q' b,
      exact tr ⟨a, b⟩ },
    intros a a', refine is_conn_equiv_closed_rev n (sigma_eq_equiv _ _) _,
    napply IH, apply is_conn_eq, intro p, apply is_conn_pathover
    /- an alternative proof of the successor case -/
    -- induction center (trunc (n.+1) A) with a₀,
    -- induction center (trunc (n.+1) (B a₀)) with b₀,
    -- apply is_contr.mk (tr ⟨a₀, b₀⟩),
    -- intro ab, induction ab with ab, induction ab with a b,
    -- induction tr_eq_tr_equiv n a₀ a !is_prop.elim with p, induction p,
    -- induction tr_eq_tr_equiv n b₀ b !is_prop.elim with q, induction q,
    -- reflexivity
  end

  @[hott, instance] lemma is_conn_prod (A B : Type _) (n : ℕ₋₂) [is_conn n A] [is_conn n B] :
    is_conn n (A × B) :=
  is_conn_equiv_closed n (sigma.equiv_prod _ _) (by apply_instance)

  @[hott] lemma is_conn_fun_of_is_conn {A B : Type _} (n : ℕ₋₂) (f : A → B)
    [HA : is_conn n A] [HB : is_conn (n.+1) B] : is_conn_fun n f :=
  λb, is_conn_equiv_closed_rev n (fiber.sigma_char _ _) (by apply_instance)

  @[hott] lemma is_conn_pfiber {A B : Type*} (n : ℕ₋₂) (f : A →* B)
    [HA : is_conn n A] [HB : is_conn (n.+1) B] : is_conn n (pfiber f) :=
  is_conn_fun_of_is_conn n f pt

  @[hott] def is_conn_fun_trunc_elim_of_le {n k : ℕ₋₂} {A B : Type _} [is_trunc n B] (f : A → B)
    (H : k ≤ n) [H2 : is_conn_fun k f] : is_conn_fun k (trunc.elim f : trunc n A → B) :=
  begin
    apply is_conn_fun.intro,
    intro P, have : Πb, is_trunc n (P b), from (λb, is_trunc_of_le _ H),
    fconstructor,
    { intros f' b,
      refine @is_conn_fun.elim k _ _ _ H2 _ _ _ b, intro a, exact f' (tr a) },
    { intro f', apply eq_of_homotopy, intro a, resetI,
      hinduction a with a, dsimp, rwr [is_conn_fun.elim_β] }
  end

  @[hott] def is_conn_fun_trunc_elim_of_ge {n k : ℕ₋₂} {A B : Type _} [is_trunc n B] (f : A → B)
    (H : n ≤ k) [H2 : is_conn_fun k f] : is_conn_fun k (trunc.elim f : trunc n A → B) :=
  begin
   napply is_conn_fun_of_is_equiv,
   have H3 : is_equiv (trunc_functor k f), from is_equiv_trunc_functor_of_is_conn_fun _ _,
   have H4 : is_equiv (trunc_functor n f), from is_equiv_trunc_functor_of_le _ H,
   apply is_equiv_of_equiv_of_homotopy (equiv.mk (trunc_functor n f) _ ⬝e trunc_equiv _ _),
   intro x, dsimp, hinduction x, refl,
   infer
  end

  @[hott] def is_conn_fun_trunc_elim {n k : ℕ₋₂} {A B : Type _} [is_trunc n B] (f : A → B)
    [H2 : is_conn_fun k f] : is_conn_fun k (trunc.elim f : trunc n A → B) :=
  begin
    eapply algebra.le_by_cases k n; intro H,
    { exact is_conn_fun_trunc_elim_of_le f H },
    { exact is_conn_fun_trunc_elim_of_ge f H }
  end

  @[hott] lemma is_conn_fun_tr (n : ℕ₋₂) (A : Type _) : is_conn_fun n (tr : A → trunc n A) :=
  begin
    apply is_conn_fun.intro,
    intro P,
    fconstructor,
    { intros f' b, hinduction b with a, exact f' a },
    { intro f', reflexivity }
  end


  @[hott] def is_contr_of_is_conn_of_is_trunc {n : ℕ₋₂} {A : Type _} (H : is_trunc n A)
    (K : is_conn n A) : is_contr A :=
  is_contr_equiv_closed (trunc_equiv n A)

end is_conn

/-
  (bundled) connected types, possibly also truncated or with a point
  The notation is n-Type*[k] for k-connected n-truncated pointed types, and you can remove
  `n-`, `[k]` or `*` in any combination to remove some conditions
-/

@[hott] structure conntype (n : ℕ₋₂) :=
  (carrier : Type _)
  (struct : is_conn n carrier)

notation `Type[`:95  n:0 `]`:0 := conntype n

@[hott] instance conntype_coe (n): has_coe_to_sort (conntype n) :=
⟨Type _ , conntype.carrier⟩

attribute [instance] [priority 1300] conntype.struct

section

  structure pconntype (n : ℕ₋₂) :=
    (pcarrier : Type*)
    (struct : is_conn n pcarrier)

  notation `Type*[`:95  n:0 `]`:0 := pconntype n

  /-
    There are multiple coercions from pconntype to Type. Type _ class inference doesn't recognize
    that all of them are definitionally equal (for performance reasons). One instance is
    automatically generated, and we manually add the missing instances.
  -/

  @[hott] instance pType_of_pconntype (n : ℕ₋₂) : has_coe Type*[n] Type* :=
  ⟨λx, x.pcarrier⟩

  @[hott] instance is_conn_pconntype {n : ℕ₋₂} (X : Type*[n]) : is_conn n X :=
  X.struct

  @[hott] def pconntype.to_conntype {n : ℕ₋₂} (X : Type*[n]) : Type[n] :=
  ⟨X, X.struct⟩

  @[hott] structure truncconntype (n k : ℕ₋₂) :=
    (carrier : Type u)
    (struct : is_trunc n carrier)
    (conn_struct : is_conn k carrier)

  notation n `-Type[`:95  k:0 `]`:0 := truncconntype n k

  @[hott] instance truncconntype_to_trunctype (n k : ℕ₋₂) : has_coe (n-Type[k]) (n-Type) :=
  ⟨λX, ⟨X.carrier, X.struct⟩⟩

  @[hott] instance truncconntype_to_conntype (n k : ℕ₋₂) : has_coe (n-Type[k]) (Type[k]) :=
  ⟨λX, ⟨X.carrier, X.conn_struct⟩⟩

  @[hott, reducible] def truncconntype.to_trunctype {n k : ℕ₋₂} (X : truncconntype.{u} n k) :
    trunctype.{u} n := ↑X
  @[hott, reducible] def truncconntype.to_conntype {n k : ℕ₋₂} (X : truncconntype.{u} n k) :
    conntype.{u} k := ↑X

  @[hott] def is_conn_truncconntype {n k : ℕ₋₂} (X : n-Type[k]) : is_conn k X :=
  by apply_instance

  @[hott, instance] def is_trunc_truncconntype {n k : ℕ₋₂} (X : n-Type[k]) : is_trunc n X :=
  X.struct

  @[hott] def is_trunc_truncconntype' {n k : ℕ₋₂} (X : n-Type[k]) :
    is_trunc n (X.to_trunctype) :=
  by apply_instance

  @[hott, instance] def is_conn_truncconntype' {n k : ℕ₋₂} (X : n-Type[k]) :
    is_conn k (X.to_trunctype) :=
  X.conn_struct

  @[hott, instance] def is_trunc_truncconntype'' {n k : ℕ₋₂} (X : n-Type[k]) :
    is_trunc n (X.to_conntype) :=
  X.struct

  @[hott] def is_conn_truncconntype'' {n k : ℕ₋₂} (X : n-Type[k]) :
    is_conn k (X.to_conntype) :=
  by apply_instance

  @[hott] structure ptruncconntype (n k : ℕ₋₂) :=
    (pcarrier : Type*)
    (struct : is_trunc n pcarrier)
    (conn_struct : is_conn k pcarrier)

  notation n `-Type*[`:95  k:0 `]`:0 := ptruncconntype n k

  @[hott] instance ptruncconntype_to_ptrunctype (n k : ℕ₋₂) : has_coe (n-Type*[k]) (n-Type*) :=
  ⟨λX, ⟨X.pcarrier, X.struct⟩⟩

  @[hott] instance ptruncconntype_to_pconntype (n k : ℕ₋₂) : has_coe (n-Type*[k]) (Type*[k]) :=
  ⟨λX, ⟨X.pcarrier, X.conn_struct⟩⟩

  @[hott] instance ptruncconntype_to_truncconntype (n k : ℕ₋₂) :
    has_coe (n-Type*[k]) (n-Type[k]) :=
  ⟨λX, ⟨X, X.struct, X.conn_struct⟩⟩

  @[hott, reducible] def ptruncconntype.to_ptrunctype {n k : ℕ₋₂} (X : ptruncconntype.{u} n k) :
    ptrunctype.{u} n := X
  @[hott, reducible] def ptruncconntype.to_pconntype {n k : ℕ₋₂} (X : ptruncconntype.{u} n k) :
    pconntype.{u} k := X
  @[hott, reducible] def ptruncconntype.to_truncconntype {n k : ℕ₋₂} (X : ptruncconntype.{u} n k) :
    truncconntype.{u} n k := X

  @[hott, reducible] def ptruncconntype.to_pType {n k : ℕ₋₂} (X : ptruncconntype.{u} n k) :
    pType.{u} := X
  @[hott, reducible] def ptruncconntype.to_conntype {n k : ℕ₋₂} (X : ptruncconntype.{u} n k) :
    conntype.{u} k := X
  @[hott, reducible] def ptruncconntype.to_trunctype {n k : ℕ₋₂} (X : ptruncconntype.{u} n k) :
    trunctype.{u} n := X

  @[hott] def is_conn_ptruncconntype {n k : ℕ₋₂} (X : n-Type*[k]) : is_conn k X :=
  by apply_instance

  @[hott] def is_trunc_ptruncconntype {n k : ℕ₋₂} (X : n-Type*[k]) : is_trunc n X :=
  by apply_instance

  @[hott] def is_trunc_ptruncconntype' {n k : ℕ₋₂} (X : n-Type*[k]) :
    is_trunc n (X.to_ptrunctype) :=
  by apply_instance

  @[hott, instance] def is_conn_ptruncconntype' {n k : ℕ₋₂} (X : n-Type*[k]) :
    is_conn k (X.to_ptrunctype) :=
  X.conn_struct

  @[hott, hsimp] def ptruncconntype.to_pType_mk {n k : ℕ₋₂} (X : Type*) (H : is_trunc n X)
    (H' : is_conn k X) : ptruncconntype.to_pType ⟨X, H, H'⟩ = X :=
  by refl

  @[hott] def ptruncconntype_eq {n k : ℕ₋₂} {X Y : n-Type*[k]} (p : X.to_pType ≃* Y.to_pType) :
    X = Y :=
  begin
    induction X with X Xt Xp Xc, induction Y with Y Yt Yp Yc,
    dsimp at p, hinduction eq_of_pequiv p,
    exact ap011 (ptruncconntype.mk X) (is_prop.elim _ _) (is_prop.elim _ _)
  end
end
end hott
