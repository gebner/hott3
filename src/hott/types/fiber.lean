/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Mike Shulman

Ported from Coq HoTT
Theorems about fibers
-/

import .sigma .eq .pi ..cubical.squareover .pointed .eq

universes u v w
hott_theory

namespace hott

open hott.equiv hott.sigma hott.eq hott.pi hott.pointed hott.is_equiv

structure fiber {A B : Type _} (f : A → B) (b : B) :=
  (point : A)
  (point_eq : f point = b)

namespace fiber
  variables {A : Type _} {B : Type _} {f : A → B} {b : B}

  @[hott] protected def sigma_char
    (f : A → B) (b : B) : fiber f b ≃ (Σ(a : A), f a = b) :=
  begin
  fapply equiv.MK,
    {intro x, exact ⟨point x, point_eq x⟩},
    {intro x, exact (fiber.mk x.1 x.2)},
    {intro x, cases x, apply idp },
    {intro x, cases x, apply idp },
  end

  @[hott, hsimp] def sigma_char_mk_snd {A B : Type*} (f : A → B) (a : A) (b : B) (p : f a = b)
    : ((fiber.sigma_char f b) ⟨ a , p ⟩).snd = p  :=
  refl _

  @[hott, hsimp] def sigma_char_mk_fst {A B : Type*} (f : A → B) (a : A) (b : B) (p : f a = b)
    : ((fiber.sigma_char f b) ⟨ a , p ⟩).fst = a  :=
  refl _

  @[hott] def fiber_eq_equiv (x y : fiber f b)
    : (x = y) ≃ (Σ(p : point x = point y), point_eq x = ap f p ⬝ point_eq y) :=
  begin
    apply equiv.trans,
      apply eq_equiv_fn_eq_of_equiv, apply fiber.sigma_char,
    apply equiv.trans,
      apply sigma_eq_equiv,
    apply sigma_equiv_sigma_right,
    intro p,
    apply eq_pathover_equiv_Fl,
  end

  @[hott] def fiber_eq {x y : fiber f b} (p : point x = point y)
    (q : point_eq x = ap f p ⬝ point_eq y) : x = y :=
  to_inv (fiber_eq_equiv _ _) ⟨p, q⟩


  @[hott] def fiber_pathover {X : Type _} {A B : X → Type _} {x₁ x₂ : X} {p : x₁ = x₂}
    {f : Πx, A x → B x} {b : Πx, B x} {v₁ : fiber (f x₁) (b x₁)} {v₂ : fiber (f x₂) (b x₂)}
    (q : point v₁ =[p] point v₂)
    (r : squareover B hrfl (pathover_idp_of_eq _ (point_eq v₁)) (pathover_idp_of_eq _ (point_eq v₂))
                           (apo f q) (apd b p))
    : v₁ =[p; λ x, fiber (f x) (b x)] v₂ :=
  begin
    apply (pathover_of_fn_pathover_fn (λ (x : X), @fiber.sigma_char (A x) (B x) (f x) (b x))), dsimp,
    fapply sigma_pathover; dsimp,
    { exact q},
    { induction v₁ with a₁ p₁, induction v₂ with a₂ p₂, dsimp at *, induction q, 
      apply pathover_idp_of_eq, apply eq_of_vdeg_square, 
      dsimp[hrfl] at r,
      dsimp[apo, apd] at r, 
      exact (square_of_squareover_ids B r)}
  end

  open is_trunc
  @[hott] def π₁ {B : A → Type _} : (Σa, B a) → A := sigma.fst

  @[hott] def fiber_pr1 (B : A → Type _) (a : A) : fiber (π₁ : (Σa, B a) → A) a ≃ B a :=
  calc
    fiber π₁ a ≃ Σ(u : Σ a, B a), (π₁ u) = a    : fiber.sigma_char _ _
          ... ≃ Σ (a' : A) (b : B a'), a' = a  : (sigma_assoc_equiv (λ (u : Σ a, B a), (π₁ u) = a) ) ⁻¹ᵉ
          ... ≃ Σa' (p : a' = a), B a'         : sigma_equiv_sigma_right (λa', comm_equiv_nondep _ _)
          ... ≃ Σ(w : Σ a', a'=a), B (π₁ w)    : sigma_assoc_equiv (λ (w : Σ a', a'=a), B (π₁ w))
          ... ≃ B a                            : sigma_equiv_of_is_contr_left (λ (w : Σ a', a'=a), B (π₁ w))

  @[hott] def sigma_fiber_equiv (f : A → B) : (Σb, fiber f b) ≃ A :=
  calc
    (Σb, fiber f b) ≃ Σb a, f a = b : sigma_equiv_sigma_right (λb, fiber.sigma_char _ b)
                ... ≃ Σa b, f a = b : sigma_comm_equiv _
                ... ≃ A             : sigma_equiv_of_is_contr_right _

  @[hott, instance] def is_pointed_fiber (f : A → B) (a : A)
    : pointed (fiber f (f a)) :=
  pointed.mk (fiber.mk a idp)

  @[hott] def pointed_fiber (f : A → B) (a : A) : Type* :=
  pointed.Mk (fiber.mk a (idpath (f a)))

  @[hott, reducible] def is_trunc_fun (n : ℕ₋₂) (f : A → B) :=
  Π(b : B), is_trunc n (fiber f b)

  @[hott, reducible] def is_contr_fun (f : A → B) := is_trunc_fun -2 f

  -- pre and post composition with equivalences
  open function
  variable (f)
  @[hott] protected def equiv_postcompose {B' : Type _} (g : B ≃ B') --[H : is_equiv g]
    (b : B) : fiber (g ∘ f) (g b) ≃ fiber f b :=
  calc
    fiber (g ∘ f) (g b) ≃ Σa : A, g (f a) = g b : fiber.sigma_char _ _
                    ... ≃ Σa : A, f a = b       : begin
                                                    apply sigma_equiv_sigma_right, 
                                                    intro a,
                                                    apply equiv.symm, 
                                                    apply eq_equiv_fn_eq
                                                  end
                    ... ≃ fiber f b             : (fiber.sigma_char _ _) ⁻¹ᵉ

  @[hott] protected def equiv_precompose {A' : Type _} (g : A' ≃ A) --[H : is_equiv g]
    (b : B) : fiber (f ∘ g) b ≃ fiber f b :=
  calc
    fiber (f ∘ g) b ≃ Σa' : A', f (g a') = b   : fiber.sigma_char _ _
                ... ≃ Σa : A, f a = b          : begin
                                                   apply sigma_equiv_sigma g,
                                                   intro a', apply erfl
                                                 end
                ... ≃ fiber f b                : (fiber.sigma_char _ _) ⁻¹ᵉ

end fiber

open unit is_trunc pointed

namespace fiber

  @[hott] def fiber_star_equiv (A : Type _) : fiber (λx : A, star) star ≃ A :=
  begin
    fapply equiv.MK,
    { intro f, cases f with a H, exact a },
    { intro a, apply fiber.mk a, reflexivity },
    { intro a, reflexivity },
    { intro f, cases f with a H, change fiber.mk a (refl star) = fiber.mk a H,
      rwr [is_set.elim H (refl star)] }
  end

  @[hott] def fiber_const_equiv (A : Type _) (a₀ : A) (a : A)
    : fiber (λz : unit, a₀) a ≃ a₀ = a :=
  calc
    fiber (λz : unit, a₀) a ≃ Σz : unit, a₀ = a : fiber.sigma_char _ _
                        ... ≃ a₀ = a : sigma_unit_left _

  -- the pointed fiber of a pointed map, which is the fiber over the basepoint
  open pointed
  @[hott] def pfiber {X Y : Type*} (f : X →* Y) : Type* :=
  pointed.MK (fiber f pt) (fiber.mk pt (respect_pt _))

  @[hott] def ppoint {X Y : Type*} (f : X →* Y) : pfiber f →* X :=
  pmap.mk point idp

  @[hott] def pfiber.sigma_char {A B : Type*} (f : A →* B)
    : pfiber f ≃* pointed.MK (Σa, f a = pt) ⟨pt, respect_pt f⟩ :=
  pequiv_of_equiv (fiber.sigma_char f pt) idp

  @[hott, hsimp] def pfiber.sigma_char_mk_snd {A B : Type*} (f : A →* B) (a : A) (p : f a = pt)
    : ((pfiber.sigma_char f).to_pmap ⟨ a , p ⟩).snd = p  :=
  refl _

  @[hott] def pointed_fst {A : Type*} (B : A → Type) (pt_B : B pt) :  
    pointed.MK (Σa, B a) ⟨pt, pt_B⟩ →* A :=
  pmap.mk π₁ (refl _) 

  @[hott] def ppoint_sigma_char {A B : Type*} (f : A →* B)
    : ppoint f ~* (pointed_fst _ _)  ∘* (pfiber.sigma_char f).to_pmap :=
  phomotopy.refl _


  @[hott] def pfiber_pequiv_of_phomotopy {A B : Type*} {f g : A →* B} (h : f ~* g)
    : pfiber f ≃* pfiber g :=
  begin
    fapply pequiv_of_equiv,
    { refine (fiber.sigma_char f pt ⬝e _ ⬝e (fiber.sigma_char g pt)⁻¹ᵉ),
      apply sigma_equiv_sigma_right, intros a,
      apply equiv_eq_closed_left, apply (to_homotopy h) },
    { refine (fiber_eq rfl _),
      change (h pt)⁻¹ ⬝ respect_pt f = idp ⬝ respect_pt g,
      rwr idp_con, apply inv_con_eq_of_eq_con, symmetry, exact (to_homotopy_pt h) }
  end

  @[hott] def transport_fiber_equiv {A B : Type _} (f : A → B) {b1 b2 : B} (p : b1 = b2)
    : fiber f b1 ≃ fiber f b2 :=
    calc fiber f b1 ≃ Σa, f a = b1 : fiber.sigma_char _ _
               ...  ≃ Σa, f a = b2 : sigma_equiv_sigma_right (λa, equiv_eq_closed_right (f a) p)
               ...  ≃ fiber f b2   : (fiber.sigma_char _ _) ⁻¹ᵉ

  @[hott,hsimp] def transport_fiber_equiv_mk {A B : Type _} 
    (f : A → B) {b1 b2 : B} (p : b1 = b2) (a : A) (q : f a = b1) :
      (transport_fiber_equiv f p) ⟨ a , q ⟩ = ⟨ a , q ⬝ p ⟩ :=  
  begin
    induction p, induction q, refl
  end

  @[hott, hsimp] def snd_point_pfiber_eq_respect_pt {A B : Type*} (f : A →* B) : 
    (pfiber f).Point = ⟨ pt , respect_pt f ⟩ :=
    by refl

  @[hott] def pequiv_postcompose {A B B' : Type*} (f : A →* B) (g : B ≃* B')
    : pfiber (g.to_pmap ∘* f) ≃* pfiber f :=
  begin
    fapply pequiv_of_equiv, 
    refine 
      transport_fiber_equiv (g.to_pmap ∘* f) (respect_pt g.to_pmap)⁻¹ ⬝e 
        fiber.equiv_postcompose f (equiv_of_pequiv g) (Point B),
    dsimp, apply (ap (fiber.mk (Point A))), refine (con.assoc _ _ _) ⬝ _, 
    apply inv_con_eq_of_eq_con, 
    dsimp, 
    rwr [con.assoc, eq.con.right_inv, con_idp, ← ap_compose],
    exact ap_con_eq_con 
      (λ x, ap g⁻¹ᵉ*.to_pmap (ap g.to_pmap (pleft_inv' g x)⁻¹) ⬝ ap g⁻¹ᵉ*.to_pmap 
      (pright_inv g (g.to_pmap x)) ⬝
      pleft_inv' g x) (respect_pt f)
  end 

  @[hott] def pequiv_precompose {A A' B : Type*} (f : A →* B) (g : A' ≃* A)
    : pfiber (f ∘* g.to_pmap) ≃* pfiber f :=
  begin
    fapply pequiv_of_equiv, 
    refine fiber.equiv_precompose f (equiv_of_pequiv g) (Point B),
    apply (eq_of_fn_eq_fn (fiber.sigma_char _ _)), fapply sigma_eq,
    { apply respect_pt g.to_pmap },
    { apply eq_pathover_Fl' }
  end

  @[hott] def pfiber_pequiv_of_square {A B C D : Type*} {f : A →* B} {g : C →* D} (h : A ≃* C)
    (k : B ≃* D) (s : k.to_pmap ∘* f ~* g ∘* h.to_pmap) : pfiber f ≃* pfiber g :=
    calc pfiber f ≃* pfiber (k.to_pmap ∘* f) : (pequiv_postcompose f k) ⁻¹ᵉ*
              ... ≃* pfiber (g ∘* h.to_pmap) : pfiber_pequiv_of_phomotopy s
              ... ≃* pfiber g : (pequiv_precompose _ _)

  @[hott] def pcompose_ppoint {A B : Type*} (f : A →* B) : f ∘* ppoint f ~* pconst (pfiber f) B :=
  begin
    fapply phomotopy.mk,
    { exact point_eq },
    { exact !idp_con⁻¹ }
  end

  @[hott] def point_fiber_eq {A B : Type _} {f : A → B} {b : B} {x y : fiber f b}
    (p : point x = point y) (q : point_eq x = ap f p ⬝ point_eq y) :
    ap point (fiber_eq p q) = p :=
  begin
    induction x with a γ, induction y with a' γ', dsimp at p q,  
    induction p, induction γ', dsimp at q,
    hinduction q using eq.rec_symm, reflexivity
  end

  @[hott] def fiber_eq_equiv_fiber {A B : Type _} {f : A → B} {b : B} (x y : fiber f b) :
    x = y ≃ fiber (ap1_gen f (point_eq x) (point_eq y)) (idpath b) :=
  calc
    x = y ≃ fiber.sigma_char f b x = fiber.sigma_char f b y :
                    eq_equiv_fn_eq_of_equiv (fiber.sigma_char f b) x y
      ... ≃ Σ(p : point x = point y), point_eq x =[p; λ z, f z = b] point_eq y : sigma_eq_equiv _ _
      ... ≃ Σ(p : point x = point y), (point_eq x)⁻¹ ⬝ ap f p ⬝ point_eq y = idp :
      sigma_equiv_sigma_right (λp,
      calc 
        point_eq x =[p; λ z, f z = b] point_eq y ≃ point_eq x = ap f p ⬝ point_eq y : eq_pathover_equiv_Fl _ _ _ 
              ... ≃ ap f p ⬝ point_eq y = point_eq x : eq_equiv_eq_symm _ _
              ... ≃ (point_eq x)⁻¹ ⬝ (ap f p ⬝ point_eq y) = idp : eq_equiv_inv_con_eq_idp _ _
              ... ≃ (point_eq x)⁻¹ ⬝ ap f p ⬝ point_eq y = idp : equiv_eq_closed_left _ (con.assoc _ _ _) ⁻¹)
              ... ≃ fiber (ap1_gen f (point_eq x) (point_eq y)) (idpath b) : (fiber.sigma_char _ _) ⁻¹ᵉ 

  @[hott] def loop_pfiber {A B : Type*} (f : A →* B) : Ω (pfiber f) ≃* pfiber (Ω→ f) :=
  pequiv_of_equiv (fiber_eq_equiv_fiber (Point (pfiber f)) (Point (pfiber f)))
    begin
      induction f with f f₀, induction B with B b₀, dsimp at f f₀, induction f₀, reflexivity
    end

  @[hott] def pfiber_loop_space {A B : Type*} (f : A →* B) : pfiber (Ω→ f) ≃* Ω (pfiber f) :=
  (loop_pfiber f)⁻¹ᵉ*

  @[hott] def point_fiber_eq_equiv_fiber {A B : Type _} {f : A → B} {b : B} {x y : fiber f b}
    (p : x = y) : point (fiber_eq_equiv_fiber x y p) = ap1_gen point idp idp p :=
  by induction p; reflexivity

  @[hott] lemma ppoint_loop_pfiber {A B : Type*} (f : A →* B) :
    ppoint (Ω→ f) ∘* (loop_pfiber f).to_pmap ~* Ω→ (ppoint f) :=
  phomotopy.mk (point_fiber_eq_equiv_fiber)
    begin
     induction f with f f₀, induction B with B b₀, dsimp at f f₀, induction f₀, reflexivity
    end

  @[hott] lemma ppoint_loop_pfiber_inv {A B : Type*} (f : A →* B) :
    Ω→ (ppoint f) ∘* ((loop_pfiber f)⁻¹ᵉ*).to_pmap ~* ppoint (Ω→ f) :=
  (phomotopy_pinv_right_of_phomotopy (ppoint_loop_pfiber f))⁻¹*

  @[hott] lemma pfiber_pequiv_of_phomotopy_ppoint {A B : Type*} {f g : A →* B} (h : f ~* g)
    : ppoint g ∘* (pfiber_pequiv_of_phomotopy h).to_pmap ~* ppoint f :=
  begin
    induction f with f f₀, induction g with g g₀, induction h with h h₀, 
    induction B with B b₀, induction A with A a₀,
    dsimp at *,
    induction g₀,
    dsimp [respect_pt] at h₀,
    induction h₀,
    dsimp [ppoint],
    fapply phomotopy.mk,
    { reflexivity },
    { dsimp at *, refine idp_con _ ⬝ _, symmetry, apply point_fiber_eq }
  end

  @[hott] lemma pequiv_postcompose_ppoint {A B B' : Type*} (f : A →* B) (g : B ≃* B')
    : ppoint f ∘* (fiber.pequiv_postcompose f g).to_pmap ~* ppoint (g.to_pmap ∘* f) :=
  begin
    induction f with f f₀, induction g with g hg g₀, induction B with B b₀,
    induction B' with B' b₀', dsimp at *, induction g₀, induction f₀,
    fapply phomotopy.mk,
    { reflexivity },
    { sorry }
    -- { refine idp_con _ ⬝ _, symmetry, dsimp [pequiv_postcompose],
    --   refine (ap_compose _ _ _) ⁻¹ ⬝ _, apply ap_constant }
  end

  @[hott] lemma pequiv_precompose_ppoint {A A' B : Type*} (f : A →* B) (g : A' ≃* A)
    : ppoint f ∘* (fiber.pequiv_precompose f g).to_pmap ~* g.to_pmap ∘* ppoint (f ∘* g.to_pmap) :=
  begin
    induction f with f f₀, induction g with g h₁ h₂ p₁ p₂, induction B with B b₀,
    induction g with g g₀, induction A with A a₀', dsimp at *, induction g₀, induction f₀,
    reflexivity
  end

  @[hott] def pfiber_pequiv_of_square_ppoint {A B C D : Type*} {f : A →* B} {g : C →* D}
    (h : A ≃* C) (k : B ≃* D) (s : k.to_pmap ∘* f ~* g ∘* h.to_pmap)
    : ppoint g ∘* (pfiber_pequiv_of_square h k s).to_pmap ~* h.to_pmap ∘* ppoint f :=
  begin
    refine (passoc _ _ _) ⁻¹* ⬝* _,
    refine pwhisker_right _ (pequiv_precompose_ppoint _ _) ⬝* _,
    refine (passoc _ _ _) ⬝* _,
    apply pwhisker_left,
    refine (passoc _ _ _) ⁻¹* ⬝* _,
    refine pwhisker_right _ (pfiber_pequiv_of_phomotopy_ppoint _) ⬝* _,
    apply pinv_right_phomotopy_of_phomotopy,
    refine (pequiv_postcompose_ppoint _ _)⁻¹*,
  end

  -- this breaks certain proofs if it is an instance
  @[hott] def is_trunc_fiber (n : ℕ₋₂) {A B : Type _} (f : A → B) (b : B)
    [is_trunc n A] [is_trunc (n.+1) B] : is_trunc n (fiber f b) :=
  is_trunc_equiv_closed_rev n (fiber.sigma_char _ _) (is_trunc_sigma _ n)

  @[hott] def is_trunc_pfiber (n : ℕ₋₂) {A B : Type*} (f : A →* B)
    [is_trunc n A] [is_trunc (n.+1) B] : is_trunc n (pfiber f) :=
  is_trunc_fiber n f pt

  @[hott] def fiber_equiv_of_is_contr {A B : Type _} (f : A → B) (b : B) [is_contr B] :
    fiber f b ≃ A :=
  (fiber.sigma_char _ _) ⬝e sigma_equiv_of_is_contr_right _

  @[hott] def pfiber_pequiv_of_is_contr {A B : Type*} (f : A →* B) [is_contr B] :
    pfiber f ≃* A :=
  pequiv_of_equiv (fiber_equiv_of_is_contr f pt) idp

  @[hott] def pfiber_ppoint_equiv {A B : Type*} (f : A →* B) : pfiber (ppoint f) ≃ Ω B :=
  calc
    pfiber (ppoint f) ≃ Σ(x : pfiber f), ppoint f x = pt : fiber.sigma_char _ _
      ... ≃ Σ(x : Σa, f a = pt), x.1 = pt : 
              by exact sigma_equiv_sigma (fiber.sigma_char _ _) (λ a, erfl)
      ... ≃ Σ(x : Σa, a = pt), f x.1 = pt : by exact sorry --(sigma_assoc_comm_equiv _ _)
      ... ≃ f pt = pt : by exact sorry -- (sigma_equiv_of_is_contr_left _)
      ... ≃ Ω B : by exact (equiv_eq_closed_left _ (respect_pt _))

  @[hott] def pfiber_ppoint_pequiv {A B : Type*} (f : A →* B) : pfiber (ppoint f) ≃* Ω B :=
  pequiv_of_equiv (pfiber_ppoint_equiv f) sorry -- (con.left_inv _)

  @[hott] def fiber_ppoint_equiv_eq {A B : Type*} {f : A →* B} {a : A} (p : f a = pt)
    (q : ppoint f (fiber.mk a p) = pt) :
    pfiber_ppoint_equiv f (fiber.mk (fiber.mk a p) q) = (respect_pt f)⁻¹ ⬝ ap f q⁻¹ ⬝ p :=
  begin
    refine _ ⬝ (con.assoc _ _ _) ⁻¹,
    apply whisker_left,
    sorry
    -- refine eq_transport_Fl _ _ ⬝ _,
    -- apply whisker_right 
    -- refine inverse2 (ap_inv _ _) ⬝ (inv_inv _) ⬝ _,
    -- refine ap_compose f pr₁ _ ⬝ ap02 f !ap_pr1_center_eq_sigma_eq',
  end

  @[hott] def fiber_ppoint_equiv_inv_eq {A B : Type*} (f : A →* B) (p : Ω B) :
    (pfiber_ppoint_equiv f)⁻¹ᵉ p = fiber.mk (fiber.mk pt (respect_pt f ⬝ p)) idp :=
  begin
    apply inv_eq_of_eq,
    refine _ ⬝ (fiber_ppoint_equiv_eq _ _)⁻¹,
    exact (inv_con_cancel_left _ _)⁻¹
  end


end fiber

open function is_equiv

namespace fiber
  /- @[hott] theorem 4.7.6 -/
  variables {A : Type _} {P : A → Type _ } {Q : A → Type _}
  variable (f : Πa, P a → Q a)

  @[hott] def fiber_total_equiv {a : A} (q : Q a)
    : fiber (total f) ⟨a , q⟩ ≃ fiber (f a) q := sorry
  -- calc
    -- fiber (total f) ⟨a , q⟩
    --       ≃ Σ(w : Σx, P x), (⟨w.1 , f w.1 w.2 ⟩ : Σ x, _) = ⟨a , q⟩
    --         : fiber.sigma_char _ _
    --   ... ≃ Σ(x : A), Σ(p : P x), (⟨x , f x p⟩ : Σx, _) = ⟨a , q⟩
    --         : (sigma_assoc_equiv _) 
    --   ... ≃ Σ(x : A), Σ(p : P x), Σ(H : x = a), f x p =[H] q
    --         :
    --         begin
    --           apply sigma_equiv_sigma_right, intro x,
    --           apply sigma_equiv_sigma_right, intro p,
    --           apply sigma_eq_equiv
    --         end
    --   ... ≃ Σ(x : A), Σ(H : x = a), Σ(p : P x), f x p =[H] q
    --         :
    --         begin
    --           apply sigma_equiv_sigma_right, intro x,
    --           apply sigma_comm_equiv
    --         end
    --   ... ≃ Σ(w : Σx, x = a), Σ(p : P w.1), f w.1 p =[w.2] q
    --         : sigma_assoc_equiv
    --   ... ≃ Σ(p : P (center (Σx, x=a)).1), f (center (Σx, x=a)).1 p =[(center (Σx, x=a)).2] q
    --         : sigma_equiv_of_is_contr_left
    --   ... ≃ Σ(p : P a), f a p =[idpath a] q
    --         : equiv_of_eq idp
    --   ... ≃ Σ(p : P a), f a p = q
    --         :
    --         begin
    --           apply sigma_equiv_sigma_right, intro p,
    --           apply pathover_idp
    --         end
    --   ... ≃ fiber (f a) q
    --         : fiber.sigma_char

end fiber
end hott