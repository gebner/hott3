/-
Copyright (c) 2017 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn

More results about pointed types.

Contains
- squares of pointed maps,
- equalities between pointed homotopies and
- squares between pointed homotopies
- pointed maps into and out of (ppmap A B), the pointed type of pointed maps from A to B
-/

import ..eq2 .pointed .unit .bool
--algebra.homotopy_group 
universes u v w
hott_theory

namespace hott
open hott.trunc /-hott.nat-/ is_trunc hott.equiv hott.is_equiv hott.bool
--open hott.unit trunc nat group sigma function bool

namespace pointed
  variables {A : Type*} {B : Type*} {C : Type*} {P : A → Type _} 
    {p₀ : P pt} {k k' l m n : ppi P p₀}

  @[hott] def punit_pmap_phomotopy {A : Type*} (f : unit* →* A) :
    f ~* pconst unit* A :=
  phomotopy_of_is_contr_dom _ _

  @[hott] def punit_ppi (P : unit* → Type) (p₀ : P ⋆) : ppi P p₀ :=
  begin
    fapply ppi.mk, intro u, induction u, exact p₀,
    refl
  end

  @[hott] def punit_ppi_phomotopy {P : unit* → Type} {p₀ : P ⋆} (f : ppi P p₀) :
    f ~* punit_ppi P p₀ :=
  phomotopy_of_is_contr_dom _ _

  @[hott] def is_contr_punit_ppi (P : unit* → Type) (p₀ : P ⋆) : is_contr (ppi P p₀) :=
  is_contr.mk (punit_ppi P p₀) (λf, eq_of_phomotopy (punit_ppi_phomotopy f)⁻¹*)

  @[hott] def is_contr_punit_pmap (A : Type*) : is_contr (unit* →* A) :=
  is_contr_punit_ppi _ _

  -- @[hott] def phomotopy_eq_equiv (h₁ h₂ : k ~* l) :
  --   (h₁ = h₂) ≃ Σ(p : to_homotopy h₁ ~ to_homotopy h₂),
  --     whisker_right (respect_pt l) (p pt) ⬝ to_homotopy_pt h₂ = to_homotopy_pt h₁ :=
  -- begin
  --   refine ppi_eq_equiv _ _ ⬝e phomotopy.sigma_char _ _ ⬝e sigma_equiv_sigma_right _,
  --   intro p,
  -- end

  /- Short term TODO: generalize to dependent maps (use ppi_eq_equiv?)
     Long term TODO: use homotopies between pointed homotopies, not equalities
  -/

  @[hott] def phomotopy_eq_equiv {A B : Type*} {f g : A →* B} (h k : f ~* g) :
    (h = k) ≃ Σ(p : to_homotopy h ~ to_homotopy k),
      whisker_right (respect_pt g) (p pt) ⬝ to_homotopy_pt k = to_homotopy_pt h :=
      sorry
  -- calc
  --   h = k ≃ phomotopy.sigma_char f g h = phomotopy.sigma_char f g k
  --     : eq_equiv_fn_eq (phomotopy.sigma_char f g) h k
  --     ... ≃ Σ(p : to_homotopy h = to_homotopy k),
  --             to_homotopy_pt h =[p; λ(q : to_homotopy h = to_homotopy k), q pt ⬝ respect_pt g = respect_pt f] to_homotopy_pt k
  --     : sigma_eq_equiv _ _
  --     ... ≃ Σ(p : to_homotopy h = to_homotopy k),
  --             to_homotopy_pt h = ap (λq, q pt ⬝ respect_pt g) p ⬝ to_homotopy_pt k
  --     : sigma_equiv_sigma_right (λp, eq_pathover_equiv_Fl p (to_homotopy_pt h) (to_homotopy_pt k))
  --     ... ≃ Σ(p : to_homotopy h = to_homotopy k),
  --             ap (λq, q pt ⬝ respect_pt g) p ⬝ to_homotopy_pt k = to_homotopy_pt h
  --     : sigma_equiv_sigma_right (λp, eq_equiv_eq_symm _ _)
  --     ... ≃ Σ(p : to_homotopy h = to_homotopy k),
  --     whisker_right (respect_pt g) (apd10 p pt) ⬝ to_homotopy_pt k = to_homotopy_pt h
  --     : sigma_equiv_sigma_right (λp, equiv_eq_closed_left _ (whisker_right _ )(whisker_right_ap _ _)⁻¹))
  --     ... ≃ Σ(p : to_homotopy h ~ to_homotopy k),
  --     whisker_right (respect_pt g) (p pt) ⬝ to_homotopy_pt k = to_homotopy_pt h
  --     : sigma_equiv_sigma_left' eq_equiv_homotopy

  @[hott] def phomotopy_eq {A B : Type*} {f g : A →* B} {h k : f ~* g} (p : to_homotopy h ~ to_homotopy k)
    (q : whisker_right (respect_pt g) (p pt) ⬝ to_homotopy_pt k = to_homotopy_pt h) : h = k :=
  to_inv (phomotopy_eq_equiv h k) ⟨p, q⟩

  @[hott] def phomotopy_eq' {A B : Type*} {f g : A →* B} {h k : f ~* g} (p : to_homotopy h ~ to_homotopy k)
    (q : square (to_homotopy_pt h) (to_homotopy_pt k) (whisker_right (respect_pt g) (p pt)) idp) : h = k :=
  phomotopy_eq p (eq_of_square q)⁻¹

  @[hott, hsimp] def trans_refl (p : k ~* l) : p ⬝* phomotopy.rfl = p :=
  begin
    induction A with A a₀,
    induction k with k k₀, induction l with l l₀, induction p with p p₀', dsimp at *,
    induction l₀, dsimp at p₀', induction p₀', refl
  end

  @[hott] def eq_of_phomotopy_trans {X Y : Type*} {f g h : X →* Y} (p : f ~* g) (q : g ~* h) :
    eq_of_phomotopy (p ⬝* q) = eq_of_phomotopy p ⬝ eq_of_phomotopy q :=
  begin
    hinduction p using phomotopy_rec_idp, hinduction q using phomotopy_rec_idp,
    exact ap eq_of_phomotopy (trans_refl _) ⬝ whisker_left _ (eq_of_phomotopy_refl _)⁻¹ᵖ
  end

  @[hott] def refl_trans (p : k ~* l) : phomotopy.rfl ⬝* p = p :=
  begin
    hinduction p using phomotopy_rec_idp,
    apply trans_refl
  end

  @[hott] def trans_assoc (p : k ~* l) (q : l ~* m) (r : m ~* n) : p ⬝* q ⬝* r = p ⬝* (q ⬝* r) :=
  begin
    hinduction r using phomotopy_rec_idp,
    hinduction q using phomotopy_rec_idp,
    hinduction p using phomotopy_rec_idp,
    induction k with k k₀, induction k₀,
    refl
  end

  @[hott] def refl_symm : phomotopy.rfl⁻¹* = phomotopy.refl k :=
  begin
    induction k with k k₀, induction k₀,
    refl
  end

  @[hott] def symm_symm (p : k ~* l) : p⁻¹*⁻¹* = p :=
  begin
    hinduction p using phomotopy_rec_idp, induction k with k k₀, induction k₀, refl
  end

  @[hott] def trans_right_inv (p : k ~* l) : p ⬝* p⁻¹* = phomotopy.rfl :=
  begin
    hinduction p using phomotopy_rec_idp, exact refl_trans _ ⬝ refl_symm
  end

  @[hott] def trans_left_inv (p : k ~* l) : p⁻¹* ⬝* p = phomotopy.rfl :=
  begin
    hinduction p using phomotopy_rec_idp, exact trans_refl _ ⬝ refl_symm
  end

  @[hott] def trans2 {p p' : k ~* l} {q q' : l ~* m} (r : p = p') (s : q = q') : p ⬝* q = p' ⬝* q' :=
  ap011 phomotopy.trans r s

  @[hott] def pcompose3 {A B C : Type*} {g g' : B →* C} {f f' : A →* B}
  {p p' : g ~* g'} {q q' : f ~* f'} (r : p = p') (s : q = q') : p ◾* q = p' ◾* q' :=
  ap011 pcompose2 r s

  @[hott] def symm2 {p p' : k ~* l} (r : p = p') : p⁻¹* = p'⁻¹* :=
  ap phomotopy.symm r

  infixl ` ◾** `:80 := pointed.trans2
  infixl ` ◽* `:81 := pointed.pcompose3
  postfix `⁻²**`:(max+1) := pointed.symm2

  @[hott] def trans_symm (p : k ~* l) (q : l ~* m) : (p ⬝* q)⁻¹* = q⁻¹* ⬝* p⁻¹* :=
  begin
    hinduction p using phomotopy_rec_idp, hinduction q using phomotopy_rec_idp,
    exact (trans_refl _)⁻²** ⬝ (trans_refl _)⁻¹ ⬝ idp ◾** refl_symm⁻¹
  end

  @[hott] def phwhisker_left (p : k ~* l) {q q' : l ~* m} (s : q = q') : p ⬝* q = p ⬝* q' :=
  idp ◾** s

  @[hott] def phwhisker_right {p p' : k ~* l} (q : l ~* m) (r : p = p') : p ⬝* q = p' ⬝* q :=
  r ◾** idp

  @[hott, hsimp] def pwhisker_left_refl {A B C : Type*} (g : B →* C) (f : A →* B) :
    pwhisker_left g (phomotopy.refl f) = phomotopy.refl (g ∘* f) :=
  begin
    induction A with A a₀, induction B with B b₀, induction C with C c₀,
    induction f with f f₀, induction g with g g₀,
    dsimp at *, induction g₀, induction f₀, refl
  end

  @[hott, hsimp] def pwhisker_right_refl {A B C : Type*} (f : A →* B) (g : B →* C) :
    pwhisker_right f (phomotopy.refl g) = phomotopy.refl (g ∘* f) :=
  begin
    induction A with A a₀, induction B with B b₀, induction C with C c₀,
    induction f with f f₀, induction g with g g₀,
    dsimp at *, induction g₀, induction f₀, refl
  end

  @[hott] def pcompose2_refl {A B C : Type*} (g : B →* C) (f : A →* B) :
    phomotopy.refl g ◾* phomotopy.refl f = phomotopy.rfl :=
  pwhisker_right_refl _ _ ◾** pwhisker_left_refl _ _ ⬝ refl_trans _

  @[hott] def pcompose2_refl_left {A B C : Type*} (g : B →* C) {f f' : A →* B} (p : f ~* f') :
    phomotopy.rfl ◾* p = pwhisker_left g p :=
  pwhisker_right_refl _ _ ◾** idp ⬝ refl_trans _

  @[hott] def pcompose2_refl_right {A B C : Type*} {g g' : B →* C} (f : A →* B) (p : g ~* g') :
    p ◾* phomotopy.rfl = pwhisker_right f p :=
  idp ◾** pwhisker_left_refl _ _ ⬝ trans_refl _

  @[hott] def pwhisker_left_trans {A B C : Type*} (g : B →* C) {f₁ f₂ f₃ : A →* B}
    (p : f₁ ~* f₂) (q : f₂ ~* f₃) :
    pwhisker_left g (p ⬝* q) = pwhisker_left g p ⬝* pwhisker_left g q :=
  begin
    hinduction p using phomotopy_rec_idp,
    hinduction q using phomotopy_rec_idp,
    refine _ ⬝ (pwhisker_left_refl _ _)⁻¹ ◾** (pwhisker_left_refl _ _)⁻¹,
    refine ap (pwhisker_left g) (trans_refl _) ⬝ pwhisker_left_refl _ _ ⬝ (trans_refl _)⁻¹
  end

  @[hott] def pwhisker_right_trans {A B C : Type*} (f : A →* B) {g₁ g₂ g₃ : B →* C}
    (p : g₁ ~* g₂) (q : g₂ ~* g₃) :
    pwhisker_right f (p ⬝* q) = pwhisker_right f p ⬝* pwhisker_right f q :=
  begin
    hinduction p using phomotopy_rec_idp,
    hinduction q using phomotopy_rec_idp,
    refine _ ⬝ (pwhisker_right_refl _ _)⁻¹ ◾** (pwhisker_right_refl _ _)⁻¹,
    refine ap (pwhisker_right f) (trans_refl _) ⬝ pwhisker_right_refl _ _ ⬝ (trans_refl _)⁻¹
  end

  @[hott] def pwhisker_left_symm {A B C : Type*} (g : B →* C) {f₁ f₂ : A →* B} (p : f₁ ~* f₂) :
    pwhisker_left g p⁻¹* = (pwhisker_left g p)⁻¹* :=
  begin
    hinduction p using phomotopy_rec_idp,
    refine _ ⬝ ap phomotopy.symm (pwhisker_left_refl _ _)⁻¹ᵖ,
    refine ap (pwhisker_left g) refl_symm ⬝ pwhisker_left_refl _ _ ⬝ refl_symm⁻¹
  end

  @[hott] def pwhisker_right_symm {A B C : Type*} (f : A →* B) {g₁ g₂ : B →* C} (p : g₁ ~* g₂) :
    pwhisker_right f p⁻¹* = (pwhisker_right f p)⁻¹* :=
  begin
    hinduction p using phomotopy_rec_idp,
    refine _ ⬝ ap phomotopy.symm (pwhisker_right_refl _ _)⁻¹ᵖ,
    refine ap (pwhisker_right f) refl_symm ⬝ pwhisker_right_refl _ _ ⬝ refl_symm⁻¹
  end

  @[hott] def trans_eq_of_eq_symm_trans {p : k ~* l} {q : l ~* m} {r : k ~* m} (s : q = p⁻¹* ⬝* r) :
    p ⬝* q = r :=
  idp ◾** s ⬝ (trans_assoc _ _ _)⁻¹ ⬝ trans_right_inv p ◾** idp ⬝ refl_trans _

  @[hott] def eq_symm_trans_of_trans_eq {p : k ~* l} {q : l ~* m} {r : k ~* m} (s : p ⬝* q = r) :
    q = p⁻¹* ⬝* r :=
  (refl_trans _)⁻¹ ⬝ (trans_left_inv _)⁻¹ ◾** idp ⬝ trans_assoc _ _ _ ⬝ idp ◾** s

  @[hott] def trans_eq_of_eq_trans_symm {p : k ~* l} {q : l ~* m} {r : k ~* m} (s : p = r ⬝* q⁻¹*) :
    p ⬝* q = r :=
  s ◾** idp ⬝ trans_assoc _ _ _ ⬝ idp ◾** trans_left_inv q ⬝ trans_refl _

  @[hott] def eq_trans_symm_of_trans_eq {p : k ~* l} {q : l ~* m} {r : k ~* m} (s : p ⬝* q = r) :
    p = r ⬝* q⁻¹* :=
  (trans_refl _)⁻¹ ⬝ idp ◾** (trans_right_inv _)⁻¹ ⬝ (trans_assoc _ _ _)⁻¹ ⬝ s ◾** idp

  @[hott] def eq_trans_of_symm_trans_eq {p : k ~* l} {q : l ~* m} {r : k ~* m} (s : p⁻¹* ⬝* r = q) :
    r = p ⬝* q :=
  (refl_trans _)⁻¹ ⬝ (trans_right_inv _)⁻¹ ◾** idp ⬝ trans_assoc _ _ _ ⬝ idp ◾** s

  @[hott] def symm_trans_eq_of_eq_trans {p : k ~* l} {q : l ~* m} {r : k ~* m} (s : r = p ⬝* q) :
    p⁻¹* ⬝* r = q :=
  idp ◾** s ⬝ (trans_assoc _ _ _)⁻¹ ⬝ trans_left_inv p ◾** idp ⬝ refl_trans _

  @[hott] def eq_trans_of_trans_symm_eq {p : k ~* l} {q : l ~* m} {r : k ~* m} (s : r ⬝* q⁻¹* = p) :
    r = p ⬝* q :=
  (trans_refl _)⁻¹ ⬝ idp ◾** (trans_left_inv _)⁻¹ ⬝ (trans_assoc _ _ _)⁻¹ ⬝ s ◾** idp

  @[hott] def trans_symm_eq_of_eq_trans {p : k ~* l} {q : l ~* m} {r : k ~* m} (s : r = p ⬝* q) :
    r ⬝* q⁻¹* = p :=
  s ◾** idp ⬝ trans_assoc _ _ _ ⬝ idp ◾** trans_right_inv q ⬝ trans_refl _

  section phsquare
  /-
    Squares of pointed homotopies
  -/

  variables {f f' f₀₀ f₂₀ f₄₀ f₀₂ f₂₂ f₄₂ f₀₄ f₂₄ f₄₄ : ppi P p₀}
            {p₁₀ : f₀₀ ~* f₂₀} {p₃₀ : f₂₀ ~* f₄₀}
            {p₀₁ : f₀₀ ~* f₀₂} {p₂₁ : f₂₀ ~* f₂₂} {p₄₁ : f₄₀ ~* f₄₂}
            {p₁₂ : f₀₂ ~* f₂₂} {p₃₂ : f₂₂ ~* f₄₂}
            {p₀₃ : f₀₂ ~* f₀₄} {p₂₃ : f₂₂ ~* f₂₄} {p₄₃ : f₄₂ ~* f₄₄}
            {p₁₄ : f₀₄ ~* f₂₄} {p₃₄ : f₂₄ ~* f₄₄}

  @[hott, reducible] def phsquare (p₁₀ : f₀₀ ~* f₂₀) (p₁₂ : f₀₂ ~* f₂₂)
                                  (p₀₁ : f₀₀ ~* f₀₂) (p₂₁ : f₂₀ ~* f₂₂) : Type _ :=
  p₁₀ ⬝* p₂₁ = p₀₁ ⬝* p₁₂

  @[hott] def phsquare_of_eq (p : p₁₀ ⬝* p₂₁ = p₀₁ ⬝* p₁₂) : phsquare p₁₀ p₁₂ p₀₁ p₂₁ := p
  @[hott] def eq_of_phsquare (p : phsquare p₁₀ p₁₂ p₀₁ p₂₁) : p₁₀ ⬝* p₂₁ = p₀₁ ⬝* p₁₂ := p

  -- @[hott] def phsquare.mk (p : Πx, square (p₁₀ x) (p₁₂ x) (p₀₁ x) (p₂₁ x))
  --   (q : cube (square_of_eq (to_homotopy_pt p₁₀)) (square_of_eq (to_homotopy_pt p₁₂))
  --             (square_of_eq (to_homotopy_pt p₀₁)) (square_of_eq (to_homotopy_pt p₂₁))
  --             (p pt) ids) : phsquare p₁₀ p₁₂ p₀₁ p₂₁ :=
  -- begin
  --   fapply phomotopy_eq,
  --   { intro x, apply eq_of_square (p x) },
  --   { generalize p pt, intro r, exact sorry }
  -- end


  @[hott] def phhconcat (p : phsquare p₁₀ p₁₂ p₀₁ p₂₁) (q : phsquare p₃₀ p₃₂ p₂₁ p₄₁) :
    phsquare (p₁₀ ⬝* p₃₀) (p₁₂ ⬝* p₃₂) p₀₁ p₄₁ :=
  trans_assoc _ _ _ ⬝ idp ◾** q ⬝ (trans_assoc _ _ _)⁻¹ ⬝ p ◾** idp ⬝ trans_assoc _ _ _

  @[hott] def phvconcat (p : phsquare p₁₀ p₁₂ p₀₁ p₂₁) (q : phsquare p₁₂ p₁₄ p₀₃ p₂₃) :
    phsquare p₁₀ p₁₄ (p₀₁ ⬝* p₀₃) (p₂₁ ⬝* p₂₃) :=
  (phhconcat p⁻¹ q⁻¹)⁻¹

  @[hott] def phhdeg_square {p₁ p₂ : f ~* f'} (q : p₁ = p₂) : phsquare phomotopy.rfl phomotopy.rfl p₁ p₂ :=
  refl_trans _ ⬝ q⁻¹ ⬝ (trans_refl _)⁻¹
  @[hott] def phvdeg_square {p₁ p₂ : f ~* f'} (q : p₁ = p₂) : phsquare p₁ p₂ phomotopy.rfl phomotopy.rfl :=
  trans_refl _ ⬝ q ⬝ (refl_trans _)⁻¹

  variables (p₀₁ p₁₀)
  @[hott] def phhrefl : phsquare phomotopy.rfl phomotopy.rfl p₀₁ p₀₁ := phhdeg_square idp
  @[hott] def phvrefl : phsquare p₁₀ p₁₀ phomotopy.rfl phomotopy.rfl := phvdeg_square idp
  variables {p₀₁ p₁₀}
  @[hott] def phhrfl : phsquare phomotopy.rfl phomotopy.rfl p₀₁ p₀₁ := phhrefl p₀₁
  @[hott] def phvrfl : phsquare p₁₀ p₁₀ phomotopy.rfl phomotopy.rfl := phvrefl p₁₀

  /-
    The names are very baroque. The following stands for
    "pointed homotopy path-horizontal composition" (i.e. composition on the left with a path)
    The names are obtained by using the ones for squares, and putting "ph" in front of it.
    In practice, use the notation ⬝ph** defined below, which might be easier to remember
  -/
  @[hott] def phphconcat {p₀₁'} (p : p₀₁' = p₀₁) (q : phsquare p₁₀ p₁₂ p₀₁ p₂₁) :
    phsquare p₁₀ p₁₂ p₀₁' p₂₁ :=
  by induction p; exact q

  @[hott] def phhpconcat {p₂₁'} (q : phsquare p₁₀ p₁₂ p₀₁ p₂₁) (p : p₂₁ = p₂₁') :
    phsquare p₁₀ p₁₂ p₀₁ p₂₁' :=
  by induction p; exact q

  @[hott] def phpvconcat {p₁₀'} (p : p₁₀' = p₁₀) (q : phsquare p₁₀ p₁₂ p₀₁ p₂₁) :
    phsquare p₁₀' p₁₂ p₀₁ p₂₁ :=
  by induction p; exact q

  @[hott] def phvpconcat {p₁₂'} (q : phsquare p₁₀ p₁₂ p₀₁ p₂₁) (p : p₁₂ = p₁₂') :
    phsquare p₁₀ p₁₂' p₀₁ p₂₁ :=
  by induction p; exact q

  @[hott] def phhinverse (p : phsquare p₁₀ p₁₂ p₀₁ p₂₁) : phsquare p₁₀⁻¹* p₁₂⁻¹* p₂₁ p₀₁ :=
  begin
    refine (eq_symm_trans_of_trans_eq _)⁻¹,
    refine (trans_assoc _ _ _)⁻¹ ⬝ _,
    refine (eq_trans_symm_of_trans_eq _)⁻¹,
    exact (eq_of_phsquare p)⁻¹
  end

  @[hott] def phvinverse (p : phsquare p₁₀ p₁₂ p₀₁ p₂₁) : phsquare p₁₂ p₁₀ p₀₁⁻¹* p₂₁⁻¹* :=
  (phhinverse p⁻¹)⁻¹

  infix ` ⬝h** `:78 := phhconcat
  infix ` ⬝v** `:78 := phvconcat
  infixr ` ⬝ph** `:77 := phphconcat
  infixl ` ⬝hp** `:77 := phhpconcat
  infixr ` ⬝pv** `:77 := phpvconcat
  infixl ` ⬝vp** `:77 := phvpconcat
  postfix `⁻¹ʰ**`:(max+1) := phhinverse
  postfix `⁻¹ᵛ**`:(max+1) := phvinverse

  @[hott] def phwhisker_rt (p : f ~* f₂₀) (q : phsquare p₁₀ p₁₂ p₀₁ p₂₁) :
    phsquare (p₁₀ ⬝* p⁻¹*) p₁₂ p₀₁ (p ⬝* p₂₁) :=
  trans_assoc _ _ _ ⬝ idp ◾** ((trans_assoc _ _ _)⁻¹ ⬝ trans_left_inv _ ◾** idp ⬝ refl_trans _) ⬝ q

  @[hott] def phwhisker_br (p : f₂₂ ~* f) (q : phsquare p₁₀ p₁₂ p₀₁ p₂₁) :
    phsquare p₁₀ (p₁₂ ⬝* p) p₀₁ (p₂₁ ⬝* p) :=
  (trans_assoc _ _ _)⁻¹ ⬝ q ◾** idp ⬝ trans_assoc _ _ _

  @[hott] def phmove_top_of_left' {p₀₁ : f ~* f₀₂} (p : f₀₀ ~* f)
    (q : phsquare p₁₀ p₁₂ (p ⬝* p₀₁) p₂₁) : phsquare (p⁻¹* ⬝* p₁₀) p₁₂ p₀₁ p₂₁ :=
  trans_assoc _ _ _ ⬝ (eq_symm_trans_of_trans_eq (q ⬝ (trans_assoc _ _ _))⁻¹)⁻¹

  @[hott] def phmove_bot_of_left {p₀₁ : f₀₀ ~* f} (p : f ~* f₀₂)
    (q : phsquare p₁₀ p₁₂ (p₀₁ ⬝* p) p₂₁) : phsquare p₁₀ (p ⬝* p₁₂) p₀₁ p₂₁ :=
  q ⬝ trans_assoc _ _ _

  @[hott] def passoc_phomotopy_right {A B C D : Type*} (h : C →* D) (g : B →* C) {f f' : A →* B}
    (p : f ~* f') : phsquare (passoc h g f) (passoc h g f')
      (pwhisker_left (h ∘* g) p) (pwhisker_left h (pwhisker_left g p)) :=
  begin
    hinduction p using phomotopy_rec_idp,
    refine idp ◾** (ap (pwhisker_left h) (pwhisker_left_refl _ _) ⬝ pwhisker_left_refl _ _) ⬝ _ ⬝
          (pwhisker_left_refl _ _)⁻¹ ◾** idp,
    exact trans_refl _ ⬝ (refl_trans _)⁻¹
  end

  @[hott] theorem passoc_phomotopy_middle {A B C D : Type*} (h : C →* D) {g g' : B →* C} (f : A →* B)
    (p : g ~* g') : phsquare (passoc h g f) (passoc h g' f)
      (pwhisker_right f (pwhisker_left h p)) (pwhisker_left h (pwhisker_right f p)) :=
  begin
    hinduction p using phomotopy_rec_idp,
    rwr [pwhisker_right_refl, pwhisker_left_refl],
    rwr [pwhisker_right_refl, pwhisker_left_refl],
    exact phvrfl
  end

  @[hott] def pwhisker_right_pwhisker_left {A B C : Type*} {g g' : B →* C} {f f' : A →* B}
    (p : g ~* g') (q : f ~* f') :
    phsquare (pwhisker_right f p) (pwhisker_right f' p) (pwhisker_left g q) (pwhisker_left g' q) :=
  begin
    hinduction p using phomotopy_rec_idp,
    hinduction q using phomotopy_rec_idp,
    exact pwhisker_right_refl _ _ ◾** pwhisker_left_refl _ _ ⬝
          (pwhisker_left_refl _ _)⁻¹ ◾** (pwhisker_right_refl _ _)⁻¹
  end

  end phsquare

  section nondep_phsquare

  variables {f f' f₀₀ f₂₀ f₀₂ f₂₂ : A →* B}
            {p₁₀ : f₀₀ ~* f₂₀} {p₀₁ : f₀₀ ~* f₀₂} {p₂₁ : f₂₀ ~* f₂₂} {p₁₂ : f₀₂ ~* f₂₂}

  @[hott] def pwhisker_left_phsquare (f : B →* C) (p : phsquare p₁₀ p₁₂ p₀₁ p₂₁) :
    phsquare (pwhisker_left f p₁₀) (pwhisker_left f p₁₂)
             (pwhisker_left f p₀₁) (pwhisker_left f p₂₁) :=
  (pwhisker_left_trans _ _ _)⁻¹ ⬝ ap (pwhisker_left f) p ⬝ pwhisker_left_trans _ _ _

  @[hott] def pwhisker_right_phsquare (f : C →* A) (p : phsquare p₁₀ p₁₂ p₀₁ p₂₁) :
    phsquare (pwhisker_right f p₁₀) (pwhisker_right f p₁₂)
             (pwhisker_right f p₀₁) (pwhisker_right f p₂₁) :=
  (pwhisker_right_trans _ _ _)⁻¹ ⬝ ap (pwhisker_right f) p ⬝ pwhisker_right_trans _ _ _

  end nondep_phsquare

  @[hott] def phomotopy_of_eq_con (p : k = l) (q : l = m) :
    phomotopy_of_eq (p ⬝ q) = phomotopy_of_eq p ⬝* phomotopy_of_eq q :=
  begin induction q, induction p, symmetry, apply trans_refl end

  @[hott] def pcompose_left_eq_of_phomotopy {A B C : Type*} (g : B →* C) {f f' : A →* B}
    (H : f ~* f') : ap (λf, g ∘* f) (eq_of_phomotopy H) = eq_of_phomotopy (pwhisker_left g H) :=
  begin
    hinduction H using phomotopy_rec_idp,
    refine ap02 _ (eq_of_phomotopy_refl _) ⬝ (eq_of_phomotopy_refl _)⁻¹ ⬝ ap eq_of_phomotopy _,
    exact (pwhisker_left_refl _ _)⁻¹
  end

  @[hott] def pcompose_right_eq_of_phomotopy {A B C : Type*} {g g' : B →* C} (f : A →* B)
    (H : g ~* g') : ap (λg, g ∘* f) (eq_of_phomotopy H) = eq_of_phomotopy (pwhisker_right f H) :=
  begin
    hinduction H using phomotopy_rec_idp,
    refine ap02 _ (eq_of_phomotopy_refl _) ⬝ (eq_of_phomotopy_refl _)⁻¹ ⬝ ap eq_of_phomotopy _,
    exact (pwhisker_right_refl _ _)⁻¹
  end

  @[hott] def phomotopy_of_eq_pcompose_left {A B C : Type*} (g : B →* C) {f f' : A →* B}
    (p : f = f') : phomotopy_of_eq (ap (λf, g ∘* f) p) = pwhisker_left g (phomotopy_of_eq p) :=
  begin
    induction p, exact (pwhisker_left_refl _ _)⁻¹
  end

  @[hott] def phomotopy_of_eq_pcompose_right {A B C : Type*} {g g' : B →* C} (f : A →* B)
    (p : g = g') : phomotopy_of_eq (ap (λg, g ∘* f) p) = pwhisker_right f (phomotopy_of_eq p) :=
  begin
    induction p, exact (pwhisker_right_refl _ _)⁻¹
  end

  @[hott] def phomotopy_mk_ppmap {A B C : Type*} {f g : A →* ppmap B C} (p : Πa, f a ~* g a)
    (q : p pt ⬝* phomotopy_of_eq (respect_pt g) = phomotopy_of_eq (respect_pt f))
    : f ~* g :=
  begin
    apply phomotopy.mk (λa, eq_of_phomotopy (p a)),
    apply eq_of_fn_eq_fn (pmap_eq_equiv _ _),
    refine phomotopy_of_eq_con _ _ ⬝ _,
    refine phomotopy_of_eq_of_phomotopy _ ◾** idp ⬝ q,
  end

  /- properties of ppmap, the pointed type of pointed maps -/
  @[hott] def pcompose_pconst (f : B →* C) : f ∘* pconst A B ~* pconst A C :=
  phomotopy.mk (λa, respect_pt f) (idp_con _)⁻¹

  @[hott] def pconst_pcompose (f : A →* B) : pconst B C ∘* f ~* pconst A C :=
  phomotopy.mk (λa, rfl) (ap_constant _ _)⁻¹

  @[hott] def ppcompose_left (g : B →* C) : ppmap A B →* ppmap A C :=
  pmap.mk (pcompose g) (eq_of_phomotopy (pcompose_pconst g))

  @[hott] def ppcompose_right (f : A →* B) : ppmap B C →* ppmap A C :=
  pmap.mk (λg, g ∘* f) (eq_of_phomotopy (pconst_pcompose f))

  /- TODO: give construction using pequiv.MK, which computes better (see comment for a start of the proof), rename to ppmap_pequiv_ppmap_right -/
  @[hott] def pequiv_ppcompose_left (g : B ≃* C) : ppmap A B ≃* ppmap A C :=
  pequiv.MK' (ppcompose_left g.to_pmap) (ppcompose_left g⁻¹ᵉ*.to_pmap).to_fun
    begin intro f, apply eq_of_phomotopy, apply pinv_pcompose_cancel_left end
    begin intro f, apply eq_of_phomotopy, apply pcompose_pinv_cancel_left end
  -- pequiv.MK (ppcompose_left g) (ppcompose_left g⁻¹ᵉ*)
  --   abstract begin
  --     apply phomotopy_mk_ppmap (pinv_pcompose_cancel_left g), esimp,
  --     refine trans_refl _ ⬝ _,
  --     refine _ ⬝ (phomotopy_of_eq_con _ _ ⬝ (phomotopy_of_eq_pcompose_left _ _ ⬝
  --       ap (pwhisker_left _) (phomotopy_of_eq_of_phomotopy _)) ◾** (phomotopy_of_eq_of_phomotopy _))⁻¹,

  --   end end
  --   abstract begin
  --     exact sorry
  --   end end

  @[hott] def pequiv_ppcompose_right (f : A ≃* B) : ppmap B C ≃* ppmap A C :=
  begin
    fapply pequiv.MK',
    { exact ppcompose_right f.to_pmap },
    { exact (ppcompose_right f⁻¹ᵉ*.to_pmap).to_fun },
    { intro g, apply eq_of_phomotopy, apply pcompose_pinv_cancel_right },
    { intro g, apply eq_of_phomotopy, apply pinv_pcompose_cancel_right },
  end

  @[hott] def loop_ppmap_commute (A B : Type*) : Ω(ppmap A B) ≃* (ppmap A (Ω B)) :=
    pequiv_of_equiv
      (calc Ω(ppmap A B) 
        ≃ (pconst A B ~* pconst A B)                       : pmap_eq_equiv _ _
    ... ≃ Σ(p : pconst A B ~ pconst A B), p pt ⬝ rfl = rfl : phomotopy.sigma_char _ _
    ... ≃ (A →* Ω B)                                       : pmap.sigma_char⁻¹ᵉ)
      (by refl)

  @[hott] def papply {A : Type*} (B : Type*) (a : A) : ppmap A B →* B :=
  pmap.mk (λ(f : A →* B), f a) idp

  @[hott] def papply_pcompose {A : Type*} (B : Type*) (a : A) : ppmap A B →* B :=
  pmap.mk (λ(f : A →* B), f a) idp

  @[hott] def ppmap_pbool_pequiv (B : Type*) : ppmap bool* B ≃* B :=
  begin
    fapply pequiv.MK',
    { exact papply B tt },
    { exact pbool_pmap },
    { intro f, fapply eq_of_phomotopy, fapply phomotopy.mk,
      { intro b, cases b, exact (respect_pt _)⁻¹ᵖ, refl },
      { exact con.left_inv _ }},
    { intro b, refl },
  end

  @[hott] def papn_pt (n : ℕ) (A B : Type*) : ppmap A B →* ppmap (Ω[n] A) (Ω[n] B) :=
  pmap.mk (λf, apn n f) (eq_of_phomotopy (apn_pconst _ _ _))

  @[hott] def papn_fun {n : ℕ} {A : Type*} (B : Type*) (p : Ω[n] A) :
    ppmap A B →* Ω[n] B :=
  papply _ p ∘* papn_pt n A B

  @[hott] def pconst_pcompose_pconst (A B C : Type*) :
    pconst_pcompose (pconst A B) = pcompose_pconst (pconst B C) :=
  idp

  @[hott] def pconst_pcompose_phomotopy_pconst {A B C : Type*} {f : A →* B} (p : f ~* pconst A B) :
    pconst_pcompose f = pwhisker_left (pconst B C) p ⬝* pcompose_pconst (pconst B C) :=
  begin
    have H : Π(p : pconst A B ~* f),
      pconst_pcompose f = pwhisker_left (pconst B C) p⁻¹* ⬝* pcompose_pconst (pconst B C),
    { intro p, hinduction p using phomotopy_rec_idp, refl },
    refine H p⁻¹* ⬝ ap (pwhisker_left _) (symm_symm _) ◾** idp,
  end

  @[hott] def passoc_pconst_right {A B C D : Type*} (h : C →* D) (g : B →* C) :
    passoc h g (pconst A B) ⬝* (pwhisker_left h (pcompose_pconst g) ⬝* pcompose_pconst h) =
    pcompose_pconst (h ∘* g) :=
  begin
    fapply phomotopy_eq,
    { intro a, apply idp_con },
    { induction h with h h₀, induction g with g g₀, induction D with D d₀, induction C with C c₀,
      dsimp at *, induction g₀, induction h₀, refl }
  end

  @[hott] def passoc_pconst_middle {A A' B B' : Type*} (g : B →* B') (f : A' →* A) :
    passoc g (pconst A B) f ⬝* (pwhisker_left g (pconst_pcompose f) ⬝* pcompose_pconst g) =
    pwhisker_right f (pcompose_pconst g) ⬝* pconst_pcompose f :=
  begin
    fapply phomotopy_eq,
    { intro a, exact idp_con _ ⬝ idp_con _ },
    { induction g with g g₀, induction f with f f₀, induction B' with D d₀, induction A with C c₀,
      dsimp at *, induction g₀, induction f₀, refl }
  end

  @[hott] def passoc_pconst_left {A B C D : Type*} (g : B →* C) (f : A →* B) :
    phsquare (passoc (pconst C D) g f) (pconst_pcompose f)
             (pwhisker_right f (pconst_pcompose g)) (pconst_pcompose (g ∘* f)) :=
  begin
    fapply phomotopy_eq,
    { intro a, dsimp [passoc, phomotopy.trans, phomotopy.mk], exact idp_con _ },
    { induction g with g g₀, induction f with f f₀, induction C with C c₀, induction B with B b₀,
      dsimp at *, induction g₀, induction f₀, refl }
  end
 
  @[hott] def ppcompose_left_pcompose {A B C D : Type*} (h : C →* D) (g : B →* C) :
    @ppcompose_left A _ _ (h ∘* g) ~* ppcompose_left h ∘* ppcompose_left g :=
  begin
    fapply phomotopy_mk_ppmap,
    { exact passoc h g },
    { dsimp [ppcompose_left], 
      refine idp ◾** (phomotopy_of_eq_con _ _ ⬝
        (ap phomotopy_of_eq (pcompose_left_eq_of_phomotopy _ _) ⬝ phomotopy_of_eq_of_phomotopy _) ◾**
        phomotopy_of_eq_of_phomotopy _) ⬝ _,
      refine _ ⬝ (phomotopy_of_eq_of_phomotopy _)⁻¹ᵖ,
      exact passoc_pconst_right h g }
  end

  @[hott] def ppcompose_right_pcompose {A B C D : Type*} (g : B →* C) (f : A →* B) :
    @ppcompose_right _ _ D (g ∘* f) ~* ppcompose_right f ∘* ppcompose_right g :=
  begin
    symmetry,
    fapply phomotopy_mk_ppmap,
    { intro h, exact passoc h g f },
    { dsimp [ppcompose_right],
      refine idp ◾** phomotopy_of_eq_of_phomotopy _ ⬝ _ ⬝ (phomotopy_of_eq_con _ _ ⬝
        (ap phomotopy_of_eq (pcompose_right_eq_of_phomotopy _ _) ⬝ (phomotopy_of_eq_of_phomotopy _)) ◾** (phomotopy_of_eq_of_phomotopy _))⁻¹,
      exact passoc_pconst_left g f }
  end

  @[hott] def ppcompose_left_ppcompose_right {A A' B B' : Type*} (g : B →* B') (f : A' →* A) :
    psquare (ppcompose_left g) (ppcompose_left g) (ppcompose_right f) (ppcompose_right f) :=
  begin
    fapply phomotopy_mk_ppmap,
    { intro h, exact passoc g h f },
    { dsimp [ppcompose_left, ppcompose_right], refine idp ◾** (phomotopy_of_eq_con _ _ ⬝
        (ap phomotopy_of_eq (pcompose_left_eq_of_phomotopy _ _) ⬝ (phomotopy_of_eq_of_phomotopy _)) ◾**
        (phomotopy_of_eq_of_phomotopy _)) ⬝ _ ⬝ (phomotopy_of_eq_con _ _ ⬝
        (ap phomotopy_of_eq (pcompose_right_eq_of_phomotopy _ _) ⬝ (phomotopy_of_eq_of_phomotopy _)) ◾**
        (phomotopy_of_eq_of_phomotopy _))⁻¹,
      apply passoc_pconst_middle }
  end

  @[hott] def pcompose_pconst_phomotopy {A B C : Type*} {f f' : B →* C} (p : f ~* f') :
    pwhisker_right (pconst A B) p ⬝* pcompose_pconst f' = pcompose_pconst f :=
  begin
    fapply phomotopy_eq,
    { intro a, exact to_homotopy_pt p },
    { hinduction p using phomotopy_rec_idp, induction C with C c₀, induction f with f f₀,
      dsimp at *, induction f₀, refl }
  end

  @[hott] def pid_pconst (A B : Type*) : pcompose_pconst (pid B) = pid_pcompose (pconst A B) :=
  by refl

  @[hott] def pid_pconst_pcompose {A B C : Type*} (f : A →* B) :
    phsquare (pid_pcompose (pconst B C ∘* f))
             (pcompose_pconst (pid C))
             (pwhisker_left (pid C) (pconst_pcompose f))
             (pconst_pcompose f) :=
  begin
    fapply phomotopy_eq,
    { refl },
    { induction f with f f₀, induction B with B b₀, dsimp at *, induction f₀, refl }
  end

  @[hott] def ppcompose_left_pconst (A B C : Type*) :
    @ppcompose_left A _ _ (pconst B C) ~* pconst (ppmap A B) (ppmap A C) :=
  begin
    fapply phomotopy_mk_ppmap,
    { exact pconst_pcompose },
    { dsimp [ppcompose_left],
      exact idp ◾** phomotopy_of_eq_idp _ ⬝ (phomotopy_of_eq_of_phomotopy _)⁻¹ }
  end

  @[hott] def ppcompose_left_phomotopy {A B C : Type*} {g g' : B →* C} (p : g ~* g') :
    @ppcompose_left A _ _ g ~* ppcompose_left g' :=
  begin
    hinduction p using phomotopy_rec_idp,
    refl
  end

  @[hott] def ppcompose_left_phomotopy_refl {A B C : Type*} (g : B →* C) :
    ppcompose_left_phomotopy (phomotopy.refl g) = phomotopy.refl (@ppcompose_left A _ _ g) :=
  by dsimp [ppcompose_left_phomotopy]; exact phomotopy_rec_idp_refl _

    /- a more explicit proof of ppcompose_left_phomotopy, which might be useful if we need to prove properties about it
    -/
    -- fapply phomotopy_mk_ppmap,
    -- { intro f, exact pwhisker_right f p },
    -- { refine ap (λx, _ ⬝* x) (phomotopy_of_eq_of_phomotopy _) ⬝ _ ⬝ (phomotopy_of_eq_of_phomotopy _)⁻¹,
    --   exact pcompose_pconst_phomotopy p }

  @[hott] def ppcompose_right_phomotopy {A B C : Type*} {f f' : A →* B} (p : f ~* f') :
    @ppcompose_right _ _ C f ~* ppcompose_right f' :=
  begin
    hinduction p using phomotopy_rec_idp,
    refl
  end

  @[hott] def pppcompose (A B C : Type*) : ppmap B C →* ppmap (ppmap A B) (ppmap A C) :=
  pmap.mk ppcompose_left (eq_of_phomotopy (ppcompose_left_pconst _ _ _))

  section psquare

  variables {A' : Type*} {A₀₀ : Type*} {A₂₀ : Type*} {A₄₀ : Type*} 
            {A₀₂ : Type*} {A₂₂ : Type*} {A₄₂ : Type*} 
            {A₀₄ : Type*} {A₂₄ : Type*} {A₄₄ : Type*}
            {f₁₀ f₁₀' : A₀₀ →* A₂₀} {f₃₀ : A₂₀ →* A₄₀}
            {f₀₁ f₀₁' : A₀₀ →* A₀₂} {f₂₁ f₂₁' : A₂₀ →* A₂₂} {f₄₁ : A₄₀ →* A₄₂}
            {f₁₂ f₁₂' : A₀₂ →* A₂₂} {f₃₂ : A₂₂ →* A₄₂}
            {f₀₃ : A₀₂ →* A₀₄} {f₂₃ : A₂₂ →* A₂₄} {f₄₃ : A₄₂ →* A₄₄}
            {f₁₄ : A₀₄ →* A₂₄} {f₃₄ : A₂₄ →* A₄₄}

  -- @[hott] def ptrunc_functor_psquare (n : ℕ₋₂) (p : psquare f₁₀ f₁₂ f₀₁ f₂₁) :
  --   psquare (ptrunc_functor n f₁₀) (ptrunc_functor n f₁₂)
  --           (ptrunc_functor n f₀₁) (ptrunc_functor n f₂₁) :=
  -- (ptrunc_functor_pcompose _ _ _)⁻¹* ⬝* ptrunc_functor_phomotopy n p ⬝* 
  -- ptrunc_functor_pcompose _ _ _

  -- @[hott] def homotopy_group_functor_psquare (n : ℕ) (p : psquare f₁₀ f₁₂ f₀₁ f₂₁) :
  --       psquare (π→[n] f₁₀) (π→[n] f₁₂) (π→[n] f₀₁) (π→[n] f₂₁) :=
  -- (homotopy_group_functor_compose _ _ _)⁻¹* ⬝* homotopy_group_functor_phomotopy n p ⬝*
  -- homotopy_group_functor_compose _ _ _

  -- @[hott] def homotopy_group_homomorphism_psquare (n : ℕ) [H : is_succ n]
  --   (p : psquare f₁₀ f₁₂ f₀₁ f₂₁) : hsquare (π→g[n] f₁₀) (π→g[n] f₁₂) (π→g[n] f₀₁) (π→g[n] f₂₁) :=
  -- begin
  --   induction H with n, exact to_homotopy (ptrunc_functor_psquare 0 (apn_psquare (succ n) p))
  -- end

  @[hott] def ppcompose_left_psquare {A : Type*} (p : psquare f₁₀ f₁₂ f₀₁ f₂₁) :
    psquare (@ppcompose_left A _ _ f₁₀) (ppcompose_left f₁₂)
            (ppcompose_left f₀₁) (ppcompose_left f₂₁) :=
  (ppcompose_left_pcompose _ _)⁻¹* ⬝* ppcompose_left_phomotopy p ⬝* ppcompose_left_pcompose _ _

  @[hott] def ppcompose_right_psquare {A : Type*} (p : psquare f₁₀ f₁₂ f₀₁ f₂₁) :
    psquare (@ppcompose_right _ _ A f₁₂) (ppcompose_right f₁₀)
            (ppcompose_right f₂₁) (ppcompose_right f₀₁) :=
  (ppcompose_right_pcompose _ _)⁻¹* ⬝* ppcompose_right_phomotopy p⁻¹* ⬝* 
  ppcompose_right_pcompose _ _

  @[hott] def trans_phomotopy_hconcat {f₀₁' f₀₁''}
    (q₂ : f₀₁'' ~* f₀₁') (q₁ : f₀₁' ~* f₀₁) (p : psquare f₁₀ f₁₂ f₀₁ f₂₁) :
    (q₂ ⬝* q₁) ⬝ph* p = q₂ ⬝ph* q₁ ⬝ph* p :=
  idp ◾** (ap (pwhisker_left f₁₂) (trans_symm _ _) ⬝ pwhisker_left_trans _ _ _) ⬝ (trans_assoc _ _ _)⁻¹

  @[hott] def symm_phomotopy_hconcat {f₀₁'} (q : f₀₁ ~* f₀₁')
    (p : psquare f₁₀ f₁₂ f₀₁ f₂₁) : q⁻¹* ⬝ph* p = p ⬝* pwhisker_left f₁₂ q :=
  idp ◾** ap (pwhisker_left f₁₂) (symm_symm _)

  @[hott] def refl_phomotopy_hconcat (p : psquare f₁₀ f₁₂ f₀₁ f₂₁) : phomotopy.rfl ⬝ph* p = p :=
  idp ◾** (ap (pwhisker_left _) refl_symm ⬝ pwhisker_left_refl _ _) ⬝ trans_refl _

  local attribute [reducible] phomotopy.rfl
  @[hott] theorem pwhisker_left_phomotopy_hconcat {f₀₁'} (r : f₀₁' ~* f₀₁)
    (p : psquare f₁₀ f₁₂ f₀₁ f₂₁) (q : psquare f₁₂ f₁₄ f₀₃ f₂₃) :
    pwhisker_left f₀₃ r ⬝ph* (p ⬝v* q) = (r ⬝ph* p) ⬝v* q :=
  begin 
    hinduction r using phomotopy_rec_idp,
    rwr [pwhisker_left_refl, refl_phomotopy_hconcat, refl_phomotopy_hconcat]
  end

  @[hott] theorem pvcompose_pwhisker_left {f₀₁'} (r : f₀₁ ~* f₀₁')
    (p : psquare f₁₀ f₁₂ f₀₁ f₂₁) (q : psquare f₁₂ f₁₄ f₀₃ f₂₃) :
    (p ⬝v* q) ⬝* (pwhisker_left f₁₄ (pwhisker_left f₀₃ r)) = (p ⬝* pwhisker_left f₁₂ r) ⬝v* q :=
  begin 
    hinduction r using phomotopy_rec_idp, hsimp
  end
  -- by hinduction r using phomotopy_rec_idp; rwr [+pwhisker_left_refl, + trans_refl]

  @[hott] def phconcat2 {p p' : psquare f₁₀ f₁₂ f₀₁ f₂₁} {q q' : psquare f₃₀ f₃₂ f₂₁ f₄₁}
    (r : p = p') (s : q = q') : p ⬝h* q = p' ⬝h* q' :=
  ap011 phconcat r s

  @[hott] def pvconcat2 {p p' : psquare f₁₀ f₁₂ f₀₁ f₂₁} {q q' : psquare f₁₂ f₁₄ f₀₃ f₂₃}
    (r : p = p') (s : q = q') : p ⬝v* q = p' ⬝v* q' :=
  ap011 pvconcat r s

  @[hott] def phinverse2 {f₁₀ : A₀₀ ≃* A₂₀} {f₁₂ : A₀₂ ≃* A₂₂} 
    {p p' : psquare f₁₀.to_pmap f₁₂.to_pmap f₀₁ f₂₁} (r : p = p') : p⁻¹ʰ* = p'⁻¹ʰ* :=
  ap phinverse r

  @[hott] def pvinverse2 {f₀₁ : A₀₀ ≃* A₀₂} {f₂₁ : A₂₀ ≃* A₂₂} 
    {p p' : psquare f₁₀ f₁₂ f₀₁.to_pmap f₂₁.to_pmap} (r : p = p') : p⁻¹ᵛ* = p'⁻¹ᵛ* :=
  ap pvinverse r

  @[hott] def phomotopy_hconcat2 {q q' : f₀₁' ~* f₀₁} {p p' : psquare f₁₀ f₁₂ f₀₁ f₂₁}
    (r : q = q') (s : p = p') : q ⬝ph* p = q' ⬝ph* p' :=
  ap011 phomotopy_hconcat r s

  @[hott] def hconcat_phomotopy2 {p p' : psquare f₁₀ f₁₂ f₀₁ f₂₁} {q q' : f₂₁' ~* f₂₁}
    (r : p = p') (s : q = q') : p ⬝hp* q = p' ⬝hp* q' :=
  ap011 hconcat_phomotopy r s

  @[hott] def phomotopy_vconcat2 {q q' : f₁₀' ~* f₁₀} {p p' : psquare f₁₀ f₁₂ f₀₁ f₂₁}
    (r : q = q') (s : p = p') : q ⬝pv* p = q' ⬝pv* p' :=
  ap011 phomotopy_vconcat r s

  @[hott] def vconcat_phomotopy2 {p p' : psquare f₁₀ f₁₂ f₀₁ f₂₁} {q q' : f₁₂' ~* f₁₂}
    (r : p = p') (s : q = q') : p ⬝vp* q = p' ⬝vp* q' :=
  ap011 vconcat_phomotopy r s

  -- for consistency, should there be a second star here?
  infix ` ◾h* `:79 := phconcat2
  infix ` ◾v* `:79 := pvconcat2
  infixl ` ◾hp* `:79 := hconcat_phomotopy2
  infixr ` ◾ph* `:79 := phomotopy_hconcat2
  infixl ` ◾vp* `:79 := vconcat_phomotopy2
  infixr ` ◾pv* `:79 := phomotopy_vconcat2
  postfix `⁻²ʰ*`:(max+1) := phinverse2
  postfix `⁻²ᵛ*`:(max+1) := pvinverse2

  end psquare

  variables {X : Type*} {X' : Type*} {Y : Type*} {Y' : Type*} {Z : Type*}
  @[hott] def pap1 (X Y : Type*) : ppmap X Y →* ppmap (Ω X) (Ω Y) :=
  pmap.mk ap1 (eq_of_phomotopy (ap1_pconst _ _))

  @[hott] def ap1_gen_const {A B : Type _} {a₁ a₂ : A} (b : B) (p : a₁ = a₂) :
    ap1_gen (const A b) idp idp p = idp :=
  ap1_gen_idp_left (const A b) p ⬝ ap_constant p b

  @[hott] def ap1_gen_compose_const_left
    {A B C : Type _} (c : C) (f : A → B) {a₁ a₂ : A} (p : a₁ = a₂) :
    ap1_gen_compose (const B c) f idp idp idp idp p ⬝
    ap1_gen_const c (ap1_gen f idp idp p) =
    ap1_gen_const c p :=
  begin induction p, refl end

  local attribute [reducible] ap1_gen
  @[hott] def ap1_gen_compose_const_right
    {A B C : Type _} (g : B → C) (b : B) {a₁ a₂ : A} (p : a₁ = a₂) :
    ap1_gen_compose g (const A b) idp idp idp idp p ⬝
    begin 
      change ap1_gen g idp idp (ap1_gen (const A b) idp idp p) = ap1_gen g idp idp idp, 
      apply ap (ap1_gen g idp idp), exact (ap1_gen_const b p) end =
    ap1_gen_const (g b) p :=
  begin induction p, refl end

  @[hott] def ap1_pcompose_pconst_left {A B C : Type*} (f : A →* B) :
    phsquare (ap1_pcompose (pconst B C) f)
             (ap1_pconst A C)
             (ap1_phomotopy (pconst_pcompose f))
             (pwhisker_right (Ω→ f) (ap1_pconst B C) ⬝* pconst_pcompose (Ω→ f)) :=
  begin
    induction A with A a₀, induction B with B b₀, induction C with C c₀, induction f with f f₀,
    dsimp at *, induction f₀,
    refine idp ◾** trans_refl _ ⬝ _ ⬝ (refl_trans _)⁻¹ᵖ ⬝ (ap1_phomotopy_refl _)⁻¹ ◾** idp,
    fapply phomotopy_eq,
    { exact ap1_gen_compose_const_left c₀ f },
    { refl }
  end

  @[hott] def ap1_pcompose_pconst_right {A B C : Type*} (g : B →* C) :
    phsquare (ap1_pcompose g (pconst A B))
             (ap1_pconst A C)
             (ap1_phomotopy (pcompose_pconst g))
             (pwhisker_left (Ω→ g) (ap1_pconst A B) ⬝* pcompose_pconst (Ω→ g)) :=
  begin
    induction A with A a₀, induction B with B b₀, induction C with C c₀, induction g with g g₀,
    dsimp at *, induction g₀,
    refine idp ◾** trans_refl _ ⬝ _ ⬝ (refl_trans _)⁻¹ᵖ ⬝ (ap1_phomotopy_refl _)⁻¹ ◾** idp,
    fapply phomotopy_eq,
    { exact ap1_gen_compose_const_right g b₀ },
    { refl }
  end

  @[hott] def pap1_natural_left (f : X' →* X) :
    psquare (pap1 X Y) (pap1 X' Y) (ppcompose_right f) (ppcompose_right (Ω→ f)) :=
  begin
    fapply phomotopy_mk_ppmap,
    { intro g, exact (ap1_pcompose _ _)⁻¹* },
    { dsimp [ppcompose_right], 
      refine idp ◾** (ap phomotopy_of_eq (ap1_eq_of_phomotopy _  ◾ idp ⬝ 
        (eq_of_phomotopy_trans _ _)⁻¹ᵖ) ⬝ (phomotopy_of_eq_of_phomotopy _))  ⬝ _, 
      refine _ ⬝ (ap phomotopy_of_eq ((pcompose_right_eq_of_phomotopy _ _) ◾ idp ⬝ 
        (eq_of_phomotopy_trans _ _)⁻¹ᵖ) ⬝ (phomotopy_of_eq_of_phomotopy _))⁻¹ᵖ,
      apply symm_trans_eq_of_eq_trans, exact (ap1_pcompose_pconst_left f)⁻¹ᵖ }
  end

  @[hott] def pap1_natural_right (f : Y →* Y') :
    psquare (pap1 X Y) (pap1 X Y') (ppcompose_left f) (ppcompose_left (Ω→ f)) :=
  begin
    fapply phomotopy_mk_ppmap,
    { intro g, exact (ap1_pcompose _ _)⁻¹* },
    { dsimp [ppcompose_left], 
      refine idp ◾** (ap phomotopy_of_eq (ap1_eq_of_phomotopy _  ◾ idp ⬝ 
        (eq_of_phomotopy_trans _ _)⁻¹) ⬝ (phomotopy_of_eq_of_phomotopy _))  ⬝ _,
      refine _ ⬝ (ap phomotopy_of_eq ((pcompose_left_eq_of_phomotopy _ _) ◾ idp ⬝ 
        (eq_of_phomotopy_trans _ _)⁻¹ᵖ) ⬝ (phomotopy_of_eq_of_phomotopy _))⁻¹ᵖ,
      apply symm_trans_eq_of_eq_trans, exact (ap1_pcompose_pconst_right f)⁻¹ᵖ }
  end

  @[hott] def pequiv.sigma_char {A B : Type*} : (A ≃* B) ≃ 
    Σ(f : A →* B), (Σ(g : B →* A), f ∘* g ~* pid B) × (Σ(h : B →* A), h ∘* f ~* pid A) :=
  begin
    fapply equiv.MK,
    { intro f, exact ⟨f, (⟨pequiv.to_pinv1 f, pequiv.pright_inv f⟩,
                          ⟨pequiv.to_pinv2 f, pequiv.pleft_inv f⟩)⟩, },
    { intro f, exact pequiv.mk' f.1 (pr1 f.2).1 (pr2 f.2).1 (pr1 f.2).2 (pr2 f.2).2 },
    { intro f, induction f with f v, induction v with hl hr, induction hl, induction hr,
      refl },
    { intro f, induction f, refl }
  end

  @[hott] def is_contr_pright_inv (f : A ≃* B) : is_contr (Σ(g : B →* A), f.to_pmap ∘* g ~* pid B) :=
  begin
    fapply is_trunc_equiv_closed,
      { exact fiber.sigma_char _ _ ⬝e sigma_equiv_sigma_right (λg, pmap_eq_equiv _ _) },
    fapply is_contr_fiber_of_is_equiv,
    exact pequiv.to_is_equiv (pequiv_ppcompose_left f)
  end

  @[hott] def is_contr_pleft_inv (f : A ≃* B) : is_contr (Σ(h : B →* A), h ∘* f.to_pmap ~* pid A) :=
  begin
    fapply is_trunc_equiv_closed,
      { exact fiber.sigma_char _ _ ⬝e sigma_equiv_sigma_right (λg, pmap_eq_equiv _ _) },
    fapply is_contr_fiber_of_is_equiv,
    exact pequiv.to_is_equiv (pequiv_ppcompose_right f)
  end

  @[hott] def pequiv_eq_equiv (f g : A ≃* B) : (f = g) ≃ f.to_pmap ~* g.to_pmap :=
  have Π(f : A →* B), is_prop ((Σ(g : B →* A), f ∘* g ~* pid B) × (Σ(h : B →* A), h ∘* f ~* pid A)),
  begin
    intro f, apply is_prop_of_imp_is_contr, intro v,
    let f' := pequiv.sigma_char⁻¹ᵉ ⟨f, v⟩,
    apply is_trunc_prod, exact is_contr_pright_inv f', exact is_contr_pleft_inv f'
  end,
  calc (f = g) ≃ (pequiv.sigma_char f = pequiv.sigma_char g)
                 : eq_equiv_fn_eq pequiv.sigma_char f g
          ...  ≃ (f = g :> (A →* B)) : subtype_eq_equiv
          ...  ≃ (f ~* g) : pmap_eq_equiv f g

  @[hott] def pequiv_eq {f g : A ≃* B} (H : f ~* g) : f = g :=
  (pequiv_eq_equiv f g)⁻¹ᵉ H

  open algebra
  @[hott] def pequiv_of_isomorphism_of_eq {G₁ G₂ : Group} (p : G₁ = G₂) :
    pequiv_of_isomorphism (isomorphism_of_eq p) = pequiv_of_eq (ap pType_of_Group p) :=
  begin
    induction p,
    apply pequiv_eq,
    fapply phomotopy.mk,
    { intro g, refl },
    { apply is_prop.elim }
  end

end pointed
end hott