/-
Copyright (c) 2014 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Floris van Doorn

Ported from Coq HoTT
Theorems about the types equiv and is_equiv
-/

import .fiber .arrow ..arity ..prop_trunc ..cubical.square .pointed
universes u v w
hott_theory
namespace hott

open is_trunc hott.sigma hott.pi fiber hott.equiv

namespace is_equiv
  variables {A : Type _} {B : Type _} (f : A → B) [H : is_equiv f]
  include H
  /- is_equiv f is a mere proposition -/
  @[hott, instance] def is_contr_fiber_of_is_equiv (b : B) : is_contr (fiber f b) :=
  is_contr.mk
    (fiber.mk (f⁻¹ᶠ b) (right_inv f b))
    (λz, fiber.rec_on z (λa p,
      fiber_eq ((ap f⁻¹ᶠ p)⁻¹ ⬝ left_inv f a) (calc
        right_inv f b = (ap (f ∘ f⁻¹ᶠ) p)⁻¹ ⬝ ((ap (f ∘ f⁻¹ᶠ) p) ⬝ right_inv f b)
                                                            : by rwr inv_con_cancel_left
      ... = (ap (f ∘ f⁻¹ᶠ) p)⁻¹ ⬝ (right_inv f (f a) ⬝ p)   : by rwr [ap_con_eq_con (right_inv f)]
      ... = (ap (f ∘ f⁻¹ᶠ) p)⁻¹ ⬝ (ap f (left_inv f a) ⬝ p) : by rwr [adj f]
      ... = (ap (f ∘ f⁻¹ᶠ) p)⁻¹ ⬝ ap f (left_inv f a) ⬝ p   : by rwr con.assoc
      ... = (ap f (ap f⁻¹ᶠ p))⁻¹ ⬝ ap f (left_inv f a) ⬝ p  : by rwr ap_compose
      ... = ap f (ap f⁻¹ᶠ p)⁻¹ ⬝ ap f (left_inv f a) ⬝ p    : by rwr ap_inv
      ... = ap f ((ap f⁻¹ᶠ p)⁻¹ ⬝ left_inv f a) ⬝ p         : by rwr ap_con)))

  @[hott] def is_contr_right_inverse : is_contr (Σ(g : B → A), f ∘ g ~ id) :=
  begin
    fapply is_trunc_equiv_closed,
      {exact Σ(g : B → A), f ∘ g = id},
      {apply sigma_equiv_sigma_right, intro g, apply eq_equiv_homotopy},
    fapply is_trunc_equiv_closed,
      {exact fiber (λ(g : B → A), f ∘ g) id},
      {apply fiber.sigma_char},
    have : is_equiv (λ(g : B → A), f ∘ g) :=
      (to_is_equiv (arrow_equiv_arrow_right B (equiv.mk f H))),
    exactI is_contr_fiber_of_is_equiv _ _
  end

  @[hott] def is_contr_right_coherence (u : Σ(g : B → A), f ∘ g ~ id)
    : is_contr (Σ(η : u.1 ∘ f ~ id), Π(a : A), u.2 (f a) = ap f (η a)) :=
  begin
    fapply is_trunc_equiv_closed_rev -2
      (sigma_pi_equiv_pi_sigma (λa (ηa : (u.1 ∘ f) a = a), u.2 (f a) = ap f ηa)),
    fapply is_trunc_equiv_closed -2,
      {apply pi_equiv_pi_right, intro a,
        apply (fiber_eq_equiv (fiber.mk (u.1 (f a)) (u.2 (f a))) (fiber.mk a idp))},
    apply_instance
  end

  omit H

  @[hott] protected def sigma_char : (is_equiv f) ≃
  (Σ(g : B → A) (ε : f ∘ g ~ id) (η : g ∘ f ~ id), Π(a : A), ε (f a) = ap f (η a)) :=
  equiv.MK (λH, by exactI ⟨inv f, right_inv f, left_inv f, adj f⟩)
           (λp, is_equiv.mk f p.1 p.2.1 p.2.2.1 p.2.2.2)
           (λp, begin
                  induction p with p1 p2,
                  induction p2 with p21 p22,
                  induction p22 with p221 p222,
                  reflexivity
                end)
           (λH, by induction H; reflexivity)

  @[hott] protected def sigma_char' : (is_equiv f) ≃
  (Σ(u : Σ(g : B → A), f ∘ g ~ id) (η : u.1 ∘ f ~ id), Π(a : A), u.2 (f a) = ap f (η a)) :=
  calc
    (is_equiv f) ≃
      (Σ(g : B → A) (ε : f ∘ g ~ id) (η : g ∘ f ~ id), Π(a : A), ε (f a) = ap f (η a))
          : is_equiv.sigma_char _
    ... ≃ (Σ(u : Σ(g : B → A), f ∘ g ~ id), Σ(η : u.1 ∘ f ~ id), Π(a : A), u.2 (f a) = ap f (η a))
          : sigma_assoc_equiv (λ(u : Σ(g : B → A), f ∘ g ~ id), Σ(η : u.1 ∘ f ~ id), Π(a : A), u.2 (f a) = ap f (η a))

  local attribute [instance] [priority 1600] is_contr_right_inverse
  local attribute [instance] [priority 1600] is_contr_right_coherence

  @[hott, instance] theorem is_prop_is_equiv : is_prop (is_equiv f) :=
  begin
    apply is_prop_of_imp_is_contr,
    intro H, apply is_trunc_equiv_closed_rev -2 (is_equiv.sigma_char' _),
    exactI is_trunc_sigma _ _,
  end

  @[hott] def inv_eq_inv {A B : Type _} {f f' : A → B} {Hf : is_equiv f} {Hf' : is_equiv f'}
    (p : f = f') : f⁻¹ᶠ = f'⁻¹ᶠ :=
  apd011 inv p (is_prop.elimo _ _ _)

  /- contractible fibers -/
  @[hott] def is_contr_fun_of_is_equiv [H : is_equiv f] : is_contr_fun f :=
  is_contr_fiber_of_is_equiv f

  @[hott] def is_prop_is_contr_fun (f : A → B) : is_prop (is_contr_fun f) := by apply_instance

  @[hott] def is_equiv_of_is_contr_fun (f : A → B) [H : is_contr_fun f] : is_equiv f :=
  adjointify _ (λb, point (center (fiber f b)))
               (λb, point_eq (center (fiber f b)))
               (λa, ap point (center_eq (fiber.mk a idp)))

  @[hott] def is_equiv_of_imp_is_equiv (H : B → is_equiv f) : is_equiv f :=
  @is_equiv_of_is_contr_fun _ _ f (λb, @is_contr_fiber_of_is_equiv _ _ _ (H b) _)

  @[hott] def is_equiv_equiv_is_contr_fun (f : A → B) : is_equiv f ≃ is_contr_fun f :=
  begin
    apply equiv_of_is_prop,
      intro H, exactI is_contr_fun_of_is_equiv f,
      intro H, exactI is_equiv_of_is_contr_fun f,
  end

  @[hott] theorem inv_commute'_fn {A : Type _} {B C : A → Type _} (f : Π{a}, B a → C a) [H : Πa, is_equiv (@f a)]
    {g : A → A} (h : Π{a}, B a → B (g a)) (h' : Π{a}, C a → C (g a))
    (p : Π⦃a : A⦄ (b : B a), f (h b) = h' (f b)) {a : A} (b : B a) :
    inv_commute' @f @h @h' p (f b)
      = (ap f⁻¹ᶠ (p b))⁻¹ ⬝ left_inv f (h b) ⬝ (ap h (left_inv f b))⁻¹ :=
  begin
    dsimp [inv_commute',eq_of_fn_eq_fn'],
    rwr [ap_con,ap_con,←adj_inv f,con.assoc,con.assoc,con.assoc,inv_con_cancel_left,
       adj f,ap_inv,ap_inv,ap_inv,←ap_compose,←ap_compose,
       eq_bot_of_square (natural_square_tr (λb, (left_inv f (h b))⁻¹ᵖ ⬝ ap f⁻¹ᶠ (p b)) (left_inv f b))⁻¹ʰ, con_inv,eq.inv_inv,con.assoc,con.assoc,con.assoc,con.assoc,con.assoc],
    apply whisker_left, apply whisker_left, refine _ ⬝ con_idp _, apply whisker_left,
    rwr [con_inv_cancel_left,con.left_inv]
  end

end is_equiv

/- Moving equivalences around in homotopies -/
namespace is_equiv
  variables {A : Type _} {B : Type _} {C : Type _} (f : A → B) [Hf : is_equiv f]
  
  include Hf

  section pre_compose
  variables (α : A → C) (β : B → C)

  -- homotopy_inv_of_homotopy_pre is in init.equiv
  @[hott] protected def inv_homotopy_of_homotopy_pre.is_equiv
    : is_equiv (inv_homotopy_of_homotopy_pre f α β) :=
  adjointify _ (homotopy_of_inv_homotopy_pre f α β)
  begin abstract {
    intro q, apply eq_of_homotopy, intro b,
    dsimp [inv_homotopy_of_homotopy_pre, homotopy_of_inv_homotopy_pre],
    apply inverse, apply eq_bot_of_square,
    apply eq_hconcat (ap02 α (adj_inv f b)),
    apply eq_hconcat (ap_compose α _ (right_inv f b))⁻¹ᵖ,
    apply natural_square q (right_inv f b) } end
  begin abstract {
    intro p, apply eq_of_homotopy, intro a,
    dsimp [inv_homotopy_of_homotopy_pre, homotopy_of_inv_homotopy_pre],
    refine con.assoc' _ _ _ ⬝ _,
    apply inverse, apply eq_bot_of_square,
    refine hconcat_eq _ (ap02 β (adj f a))⁻¹,
    refine hconcat_eq _ (ap_compose β f (left_inv f a)),
    apply natural_square p (left_inv f a) } end
  end pre_compose

  section post_compose
  variables (α : C → A) (β : C → B)

  -- homotopy_inv_of_homotopy_post is in init.equiv
  @[hott] protected def inv_homotopy_of_homotopy_post.is_equiv
    : is_equiv (inv_homotopy_of_homotopy_post f α β) :=
  adjointify _ (homotopy_of_inv_homotopy_post f α β)
  begin abstract {
    intro q, apply eq_of_homotopy, intro c,
    dsimp [inv_homotopy_of_homotopy_post, homotopy_of_inv_homotopy_post],
    refine (whisker_right (left_inv f (α c)) (ap_con _ _ _ ⬝ whisker_right _ (ap_inv _ _))) ⬝ _,
    apply inverse, apply eq_bot_of_square,
    apply eq_hconcat (adj_inv f (β c))⁻¹,
    apply eq_vconcat (ap_compose' f⁻¹ᶠ _ _),
    refine vconcat_eq _ (ap_id (q c)),
    apply natural_square_tr (left_inv f) (q c)
   } end
  begin abstract {
    intro p, apply eq_of_homotopy, intro c,
    dsimp [inv_homotopy_of_homotopy_post, homotopy_of_inv_homotopy_post],
    refine (whisker_left _ (ap_con f (ap f⁻¹ᶠ (p c)) (left_inv f (α c)))) ⬝ _,
    refine con.assoc' _ _ _ ⬝ _,
    apply inverse, apply eq_bot_of_square,
    refine hconcat_eq _ (adj f (α c)),
    apply eq_vconcat (ap_compose f f⁻¹ᶠ (p c))⁻¹,
    refine vconcat_eq _ (ap_id (p c)),
    apply natural_square_tr (right_inv f) (p c)
  } end

  end post_compose

end is_equiv

namespace is_equiv

  /- @[hott] theorem 4.7.7 -/
  variables {A : Type _} {P : A → Type _} {Q : A → Type _}
  variable (f : Πa, P a → Q a)

  @[hott, reducible] def is_fiberwise_equiv := Πa, is_equiv (f a)

  @[hott] def is_equiv_total_of_is_fiberwise_equiv [H : is_fiberwise_equiv f] : is_equiv (total f) :=
  is_equiv_sigma_functor id f

  @[hott] def is_fiberwise_equiv_of_is_equiv_total [H : is_equiv (total f)]
    : is_fiberwise_equiv f :=
  begin
    intro a,
    have : is_contr_fun (f a),
    { intro q, apply is_trunc_equiv_closed, exact (fiber_total_equiv f q), apply_instance },
    exactI is_equiv_of_is_contr_fun _,
  end

end is_equiv

namespace equiv
  open hott.is_equiv
  variables {A : Type _} {B : Type _} {C : Type _}

  @[hott] def equiv_mk_eq {f f' : A → B} [H : is_equiv f] [H' : is_equiv f'] (p : f = f')
      : equiv.mk f H = equiv.mk f' H' :=
  apd011 equiv.mk p (is_prop.elimo _ _ _)

  @[hott] def equiv_eq' {f f' : A ≃ B} (p : to_fun f = to_fun f') : f = f' :=
  by induction f; induction f'; apply (equiv_mk_eq p)

  @[hott] def equiv_eq {f f' : A ≃ B} (p : to_fun f ~ to_fun f') : f = f' :=
  by apply equiv_eq'; apply eq_of_homotopy p

  @[hott] def trans_symm (f : A ≃ B) (g : B ≃ C) : (f ⬝e g)⁻¹ᵉ = g⁻¹ᵉ ⬝e f⁻¹ᵉ :> (C ≃ A) :=
  equiv_eq' idp

  @[hott] def symm_symm (f : A ≃ B) : f⁻¹ᵉ⁻¹ᵉ = f :> (A ≃ B) :=
  equiv_eq' idp

  @[hott] protected def equiv.sigma_char
    (A : Type u) (B : Type v) : (A ≃ B) ≃ Σ(f : A → B), is_equiv f :=
  begin
    fapply equiv.MK,
      {intro F, exact ⟨to_fun F, to_is_equiv F⟩},
      {intro p, cases p with f H, exact (equiv.mk f H)},
      {intro p, cases p, exact idp},
      {intro F, cases F, exact idp},
  end

  @[hott] def equiv_eq_char (f f' : A ≃ B) : (f = f') ≃ (to_fun f = to_fun f') :=
  calc
    (f = f') ≃ (to_fun (equiv.sigma_char _ _) f = to_fun (equiv.sigma_char _ _) f')
                : eq_equiv_fn_eq (to_fun (equiv.sigma_char _ _)) _ _
         ... ≃ ((to_fun (equiv.sigma_char _ _) f).1 = (to_fun (equiv.sigma_char _ _) f').1 ) : (equiv_subtype _ _)⁻¹ᵉ
         ... ≃ (to_fun f = to_fun f') : equiv.rfl

  @[hott] def is_equiv_ap_to_fun (f f' : A ≃ B)
    : is_equiv (ap to_fun : f = f' → to_fun f = to_fun f') :=
  begin
    fapply adjointify,
      { intro p, induction f with f H, induction f' with f' H', dsimp at p, induction p, apply ap (mk f), apply is_prop.elim },
      { intro p, cases f with f H, cases f' with f' H', dsimp at p, induction p,
        apply @concat _ _ (ap to_fun (ap (equiv.mk f) (is_prop.elim H H'))), refl,
        hgeneralize : is_prop.elim H H' = q, induction q, apply idp },
      { intro p, induction p, cases f with f H, dsimp, 
        refine ap02 (equiv.mk f) (is_set.elim _ idp) }
  end

  @[hott] def equiv_pathover {A : Type _} {a a' : A} (p : a = a')
    {B : A → Type _} {C : A → Type _} (f : B a ≃ C a) (g : B a' ≃ C a')
    (r : Π(b : B a) (b' : B a') (q : b =[p] b'), f b =[p] g b') : f =[p; λa, B a ≃ C a] g :=
  begin
    refine pathover_of_fn_pathover_fn (λa, equiv.sigma_char _ _) _,
    fapply sigma_pathover, apply arrow_pathover, exact r, apply is_prop.elimo
  end

  @[hott] def is_contr_equiv (A B : Type _) [HA : is_contr A] [HB : is_contr B] : is_contr (A ≃ B) :=
  begin
    apply is_contr_of_inhabited_prop _, apply is_prop.mk,
    intros x y, cases x with fx Hx, cases y with fy Hy,
    have : fx = fy, apply eq_of_homotopy, intro a, apply is_prop.elim, induction this,
    have : Hx = Hy, apply is_prop.elim, induction this, refl,
    apply equiv_of_is_contr_of_is_contr
  end

  @[hott] def is_trunc_succ_equiv (n : ℕ₋₂) (A B : Type _)
  [HA : is_trunc n.+1 A] [HB : is_trunc n.+1 B] : is_trunc n.+1 (A ≃ B) :=
  @is_trunc_equiv_closed _ _ n.+1 (equiv.symm (equiv.sigma_char _ _))
  (@is_trunc_sigma _ _ _ _ (λ f, is_trunc_succ_of_is_prop _ _))

  @[hott] def is_trunc_equiv (n : ℕ₋₂) (A B : Type _)
  [HA : is_trunc n A] [HB : is_trunc n B] : is_trunc n (A ≃ B) :=
  begin unfreezeI, cases n, exactI is_contr_equiv _ _, apply is_trunc_succ_equiv _ _ end

  @[hott] def eq_of_fn_eq_fn'_idp {A B : Type _} (f : A → B) [is_equiv f] (x : A)
    : eq_of_fn_eq_fn' f (idpath (f x)) = idpath x :=
  con.left_inv _

  @[hott] def eq_of_fn_eq_fn'_con {A B : Type _} (f : A → B) [is_equiv f] {x y z : A}
    (p : f x = f y) (q : f y = f z)
    : eq_of_fn_eq_fn' f (p ⬝ q) = eq_of_fn_eq_fn' f p ⬝ eq_of_fn_eq_fn' f q :=
  begin
    dsimp [eq_of_fn_eq_fn'],
    refine _ ⬝ con.assoc _ _ _, apply whisker_right,
    refine _ ⬝ (con.assoc _ _ _)⁻¹, refine _ ⬝ (con.assoc _ _ _)⁻¹, apply whisker_left,
    refine ap_con _ _ _ ⬝ _, apply whisker_left,
    refine (con_inv_cancel_left _ _)⁻¹
  end

end equiv
end hott