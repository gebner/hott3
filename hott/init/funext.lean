/-
Copyright (c) 2014 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob von Raumer, Floris van Doorn

Ported from Coq HoTT
-/
import .trunc .equiv .ua

universes u v w l k
hott_theory

namespace hott

open eq is_trunc sigma function is_equiv equiv prod unit

/-
   We now prove that funext follows from a couple of weaker-looking forms
   of function extensionality.

   This proof is originally due to Voevodsky; it has since been simplified
   by Peter Lumsdaine and Michael Shulman.
-/

@[hott] def funext :=
  Π ⦃A : Type l⦄ {P : A → Type k} (f g : Π x, P x), is_equiv (@apd10 A P f g)

-- Naive funext is the simple assertion that pointwise equal functions are equal.
@[hott] def naive_funext :=
  Π ⦃A : Type _⦄ {P : A → Type _} (f g : Πx, P x), (f ~ g) → f = g

-- Weak funext says that a product of contractible types is contractible.
@[hott] def weak_funext :=
  Π ⦃A : Type _⦄ (P : A → Type _) [H: Πx, is_contr (P x)], is_contr (Πx, P x)

@[hott] def weak_funext_of_naive_funext : naive_funext → weak_funext :=
begin
  intros nf A P Pc,
  let c := λ x, center (P x),
  apply is_contr.mk c, intro f,
  have eq' : (λx, center (P x)) ~ f := λ x, center_eq (f x),
  have eq : (λx, center (P x)) = f := @nf A P (λx, center (P x)) f eq',
  assumption
end

/-
  The less obvious direction is that weak_funext implies funext
  (and hence all three are logically equivalent).  The point is that under weak
  funext, the space of "pointwise homotopies" has the same universal property as
  the space of paths.
-/

section
  parameters [wf : weak_funext.{l k}] {A : Type.{l}} {B : A → Type.{k}} (f : Π x, B x)

  @[hott] def is_contr_sigma_homotopy : is_contr (Σ (g : Π x, B x), f ~ g) :=
    is_contr.mk (sigma.mk f (homotopy.refl f))
      (λ ⟨(g : Π x, B x), (h : f ~ g)⟩,
          let r := λ (k : Π x, Σ y, f x = y),
            @sigma.mk _ (λg, f ~ g)
              (λx, fst (k x)) (λx, snd (k x)) in
          let s (g : Π x, B x) (h : f ~ g) (x) :=
            @sigma.mk _ (λy, f x = y) (g x) (h x) in
          have t1 : Πx, is_contr (Σ y, f x = y),
            from (λx, is_contr_sigma_eq _),
          have t2 : is_contr (Πx, Σ y, f x = y),
            from wf _,
          have t3 : (λ x, @sigma.mk _ (λ y, f x = y) (f x) idp) = s g h,
            from @eq_of_is_contr (Π x, Σ y, f x = y) t2 _ _,
          have t4 : r (λ x, sigma.mk (f x) idp) = r (s g h),
            from ap r t3,
          t4
        )
  local attribute [instance] is_contr_sigma_homotopy

  parameters (Q : Π g (h : f ~ g), Type _) (d : Q f (homotopy.refl f))

  @[hott] def homotopy_ind (g : Πx, B x) (h : f ~ g) : Q g h :=
    @transport _ (λ gh, Q (sigma.fst gh) (snd gh)) (sigma.mk f (homotopy.refl f)) (sigma.mk g h)
      (@eq_of_is_contr _ is_contr_sigma_homotopy _ _) d

  -- local attribute weak_funext [reducible]
  -- local attribute homotopy_ind [reducible]
  @[hott] def homotopy_ind_comp : homotopy_ind f (homotopy.refl f) = d :=
  begin
    dsimp [homotopy_ind],
    have := @prop_eq_of_is_contr _ _ _ _ (eq_of_is_contr _ _) idp,
    rwr this, apply @is_contr_sigma_homotopy wf,
  end
end

/- Now the proof is fairly easy; we can just use the same induction principle on both sides. -/
section

-- local attribute weak_funext [reducible]
@[hott] def funext_of_weak_funext (wf : weak_funext.{l k}) : funext.{l k} :=
begin
  intros A B f g,
  let eq_to_f := λ g' x, f = g',
  let sim2path := @homotopy_ind wf _ _ f eq_to_f idp,
  have t1 : sim2path f (homotopy.refl f) = idp,
    by apply @homotopy_ind_comp wf,
  have t2 : apd10 (sim2path f (homotopy.refl f)) = (homotopy.refl f),
    from ap apd10 t1,
  have left_inv : apd10 ∘ (sim2path g) ~ id,
    from (@homotopy_ind wf _ _ f (λ g' x, apd10 (sim2path g' x) = x) t2) g,
  have right_inv : @comp (f = g) (f ~ g) (f = g) (sim2path g) (@apd10 A B f g) ~ id,
    {intro h, induction h, apply homotopy_ind_comp},
  exact is_equiv.adjointify apd10 (sim2path g) left_inv right_inv
end

@[hott] def funext_from_naive_funext : naive_funext → funext :=
  funext_of_weak_funext ∘ weak_funext_of_naive_funext
end

section

  @[hott] private theorem ua_isequiv_postcompose {A B : Type.{l}} {C : Type u}
      {w : A → B} [H0 : is_equiv w] : is_equiv (@comp C A B w) :=
    let w' := equiv.mk w H0 in
    let eqinv : A = B := ((@is_equiv.inv _ _ _ (univalence A B)) w') in
    let eq' := equiv_of_eq eqinv in
    have eqretr : eq' = w', from (@right_inv _ _ (@equiv_of_eq A B) (univalence A B) w'),
    have invs_eq : (to_fun eq')⁻¹ = (to_fun w')⁻¹, from inv_eq eq' w' eqretr,
    is_equiv.adjointify (@comp C A B w)
      (@comp C B A (is_equiv.inv w))
      (λ (x : C → B),
        have eqfin1 : Π(p : A = B), (to_fun (equiv_of_eq p)) ∘ ((to_fun (equiv_of_eq p))⁻¹ ∘ x) = x,
          by intro p; induction p; reflexivity,
        have eqfin : (to_fun eq') ∘ ((to_fun eq')⁻¹ ∘ x) = x,
          from eqfin1 eqinv,
        have eqfin' : (to_fun w') ∘ ((to_fun eq')⁻¹ ∘ x) = x,
          by { refine _ ⬝ eqfin, rwr eqretr },
        show (to_fun w') ∘ ((to_fun w')⁻¹ ∘ x) = x,
          by { refine _ ⬝ eqfin', rwr invs_eq }
      )
      (λ (x : C → A),
        have eqfin1 : Π(p : A = B), (to_fun (equiv_of_eq p))⁻¹ ∘ ((to_fun (equiv_of_eq p)) ∘ x) = x,
          by intro p; induction p; reflexivity,
        have eqfin : (to_fun eq')⁻¹ ∘ ((to_fun eq') ∘ x) = x,
          from eqfin1 eqinv,
        have eqfin' : (to_fun eq')⁻¹ ∘ ((to_fun w') ∘ x) = x,
          by { refine _ ⬝ eqfin, rwr eqretr },
        show (to_fun w')⁻¹ ∘ ((to_fun w') ∘ x) = x,
          by { refine _ ⬝ eqfin', rwr invs_eq }
      )

  -- We are ready to prove functional extensionality,
  -- starting with the naive non-dependent version.
  @[hott] private def diagonal (B : Type _) : Type _
    := Σ xy : B × B, fst xy = snd xy

  @[hott] private def isequiv_src_compose {A : Type u} {B : Type v}
      : @is_equiv (A → diagonal B)
                 (A → B)
                 (comp (prod.fst ∘ sigma.fst)) :=
    @ua_isequiv_postcompose (diagonal B) _ _ (prod.fst ∘ sigma.fst)
        (is_equiv.adjointify (prod.fst ∘ sigma.fst)
          (λ x : B, (sigma.mk (x , x) idp : diagonal B)) (λx, idp)
          (λ ⟨⟨b, c⟩, p⟩, by { dsimp at p, induction p, refl }))

  @[hott] private def isequiv_tgt_compose {A : Type u} {B : Type v}
      : is_equiv (comp (prod.snd ∘ sigma.fst) : (A → diagonal B) → (A → B)) :=
  @ua_isequiv_postcompose _ _ _ _ begin
    fapply adjointify,
    { intro b, exact ⟨(b, b), idp⟩},
    { intro b, reflexivity},
    { intro a, induction a with q p, induction q, dsimp at *, induction p, reflexivity}
  end

  @[hott] theorem nondep_funext_from_ua {A : Type _} {B : Type _}
      : Π {f g : A → B}, f ~ g → f = g :=
  begin
    intros f g p,
    let d := λ (x : A), @sigma.mk (B × B) (λ (xy : B × B), xy.1 = xy.2) (f x , f x) (eq.refl (f x, f x).1),
    let e := λ (x : A), @sigma.mk (B × B) (λ (xy : B × B), xy.1 = xy.2) (f x , g x) (p x),
    let precomp1 : (A → diagonal B) → (A → B) := comp (prod.fst ∘ sigma.fst),
    have equiv1 : is_equiv precomp1,
      from @isequiv_src_compose A B,
    have equiv2 : Π (x y : A → diagonal B), is_equiv (ap precomp1),
      from is_equiv.is_equiv_ap precomp1,
    have H' : Π (x y : A → diagonal B), prod.fst ∘ sigma.fst ∘ x = prod.fst ∘ sigma.fst ∘ y → x = y,
      from (λ x y, is_equiv.inv (ap precomp1)),
    have eq2 : prod.fst ∘ sigma.fst ∘ d = prod.fst ∘ sigma.fst ∘ e,
      from idp,
    have eq0 : d = e,
      from H' d e eq2,
    have eq1 : (prod.snd ∘ sigma.fst) ∘ d = (prod.snd ∘ sigma.fst) ∘ e,
      from ap _ eq0,
    exact eq1
  end

end

-- Now we use this to prove weak funext, which as we know
-- implies (with dependent eta) also the strong dependent funext.
@[hott] theorem weak_funext_of_ua : weak_funext.{u v} :=
  (λ (A : Type _) (P : A → Type _) allcontr,
    let U := (λ (x : A), ulift unit) in
  have pequiv : Π (x : A), P x ≃ unit,
    from (λ x, @equiv_unit_of_is_contr (P x) (allcontr x)),
  have psim : Π (x : A), P x = U x,
    from (λ x, eq_of_equiv_lift (pequiv x)),
  have p : P = U,
    from @nondep_funext_from_ua A _ P U psim,
  have tU' : is_contr (A → ulift unit),
    from is_contr.mk (λ x, ulift.up ())
      (λ f, nondep_funext_from_ua (λa, by induction (f a) with u;induction u;reflexivity)),
  have tU : is_contr (Π x, U x),
    from tU',
  have tlast : is_contr (Πx, P x),
    from (transport (λ PU : A → Type v, is_contr $ Π x, PU x) p⁻¹ᵖ tU: _),
  tlast)

-- we have proven function extensionality from the univalence axiom
@[hott] def funext_of_ua : funext :=
  funext_of_weak_funext (@weak_funext_of_ua)

/-
  We still take funext as an axiom, so that when you write "print axioms foo", you can see whether
  it uses only function extensionality, and not also univalence.
-/

axiom function_extensionality : funext

variables {A : Type _} {P : A → Type _} {f g : Π x, P x}

namespace funext
  @[instance, hott]
  theorem is_equiv_apdt (f g : Π x, P x) : is_equiv (@apd10 A P f g) :=
  function_extensionality f g
end funext

open funext

namespace eq
  @[hott] def eq_equiv_homotopy : (f = g) ≃ (f ~ g) :=
  equiv.mk apd10 (by apply_instance)

  @[hott] def eq_of_homotopy : f ~ g → f = g :=
  (@apd10 A P f g)⁻¹

  @[hott] def apd10_eq_of_homotopy (p : f ~ g) : apd10 (eq_of_homotopy p) = p :=
  right_inv apd10 p

  @[hott] def eq_of_homotopy_apd10 (p : f = g) : eq_of_homotopy (apd10 p) = p :=
  left_inv apd10 p

  @[hott] def eq_of_homotopy_idp (f : Π x, P x) : eq_of_homotopy (λx : A, idpath (f x)) = idpath f :=
  is_equiv.left_inv apd10 idp

  @[hott] def eq_of_homotopy_refl (f : Π x, P x) : eq_of_homotopy (homotopy.refl f) = idpath f :=
  eq_of_homotopy_idp _

  @[hott] def naive_funext_of_ua : naive_funext :=
  λ A P f g h, eq_of_homotopy h

  @[hott] protected def homotopy.rec_on {Q : (f ~ g) → Type _} (p : f ~ g)
    (H : Π(q : f = g), Q (apd10 q)) : Q p :=
  right_inv apd10 p ▸ H (eq_of_homotopy p)

  @[hott] protected def homotopy.rec_on_idp {Q : Π{g}, (f ~ g) → Type _} {g : Π x, P x}
    (p : f ~ g) (H : Q (homotopy.refl f)) : Q p :=
  homotopy.rec_on p (λq, by induction q; exact H)

  @[hott] protected def homotopy.rec_on' {f f' : Πa, P a} {Q : (f ~ f') → (f = f') → Type _}
    (p : f ~ f') (H : Π(q : f = f'), Q (apd10 q) q) : Q p (eq_of_homotopy p) :=
  begin
    refine homotopy.rec_on p _,
    intro q, exact (left_inv (apd10) q)⁻¹ ▸ H q
  end

  @[hott] protected def homotopy.rec_on_idp' {f : Πa, P a} {Q : Π{g}, (f ~ g) → (f = g) → Type _}
    {g : Πa, P a} (p : f ~ g) (H : Q (homotopy.refl f) idp) : Q p (eq_of_homotopy p) :=
  begin
    refine homotopy.rec_on' p _, intro q, induction q, exact H
  end

  @[hott] protected def homotopy.rec_on_idp_left {A : Type _} {P : A → Type _} {g : Πa, P a}
    {Q : Πf, (f ~ g) → Type _} {f : Π x, P x}
    (p : f ~ g) (H : Q g (homotopy.refl g)) : Q f p :=
  begin
    refine homotopy.rec_on p (λ q, _), induction q, exact H
  end

  @[hott] def homotopy.rec_idp {A : Type _} {P : A → Type _} {f : Πa, P a}
    (Q : Π{g}, (f ~ g) → Type _) (H : Q (homotopy.refl f)) {g : Π x, P x} (p : f ~ g) : Q p :=
  homotopy.rec_on_idp p H

  @[hott] def homotopy_rec_on_apd10 {A : Type _} {P : A → Type _} {f g : Πa, P a}
    (Q : f ~ g → Type _) (H : Π(q : f = g), Q (apd10 q)) (p : f = g) :
    homotopy.rec_on (apd10 p) H = H p :=
  begin
    dunfold homotopy.rec_on,
    transitivity, rwr adj,
    transitivity, symmetry; apply tr_compose,
    apply apdt
  end

  @[hott] def homotopy_rec_idp_refl {A : Type _} {P : A → Type _} {f : Πa, P a}
    (Q : Π{g}, f ~ g → Type _) (H : Q homotopy.rfl) :
    homotopy.rec_idp @Q H homotopy.rfl = H :=
  homotopy_rec_on_apd10 Q _ rfl

  @[hott] def eq_of_homotopy_inv {f g : Π x, P x} (H : f ~ g)
    : eq_of_homotopy (λx, (H x)⁻¹ᵖ) = (eq_of_homotopy H)⁻¹ :=
  begin
    apply homotopy.rec_on_idp H,
    change eq_of_homotopy (λ x, idp) = _,
    rwr [eq_of_homotopy_refl],
  end

  @[hott] def eq_of_homotopy_con {f g h : Π x, P x} (H1 : f ~ g) (H2 : g ~ h)
    : eq_of_homotopy (λx, H1 x ⬝ H2 x) = eq_of_homotopy H1 ⬝ eq_of_homotopy H2 :=
  begin
    apply homotopy.rec_on_idp H2, apply homotopy.rec_on_idp H1,
    rwr eq_of_homotopy_refl, apply eq_of_homotopy_idp,
  end

  @[hott] def compose_eq_of_homotopy {A B C : Type _} (g : B → C) {f f' : A → B} (H : f ~ f') :
    (ap (λf : A → B, g ∘ f) (eq_of_homotopy H): _) = eq_of_homotopy (hwhisker_left g H) :=
  begin
    apply homotopy.rec_on_idp H, rwr eq_of_homotopy_refl,
    symmetry, apply eq_of_homotopy_idp
  end

end eq

end hott
