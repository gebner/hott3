/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Ulrik Buchholtz

Declaration of suspension
-/

import ..hit.pushout ..types.pointed2 ..cubical.square .connectedness
universes u v w

namespace hott
hott_theory

open hott.pushout hott.equiv unit pointed hott.is_equiv

@[hott] def susp' (A : Type _) : Type _ := pushout (λ(a : A), star) (λ(a : A), star)

namespace susp

  @[hott] def north' {A : Type _} : susp' A :=
  inl star

  @[hott, instance] def pointed_susp (X : Type _) : pointed (susp' X) :=
  pointed.mk north'

end susp open susp

@[hott] def susp (X : Type _) : Type* :=
pointed.MK (susp' X) north'

@[hott, hsimp] def carrier_susp (X : Type _) : ↥(susp X) = susp' X := by refl

notation `⅀` := susp

namespace susp
section
  variable {A : Type _}

  @[hott] def north {A : Type _} : susp A :=
  north'

  @[hott] def south {A : Type _} : susp A :=
  inr star

  @[hott] def merid (a : A) : @north A = @south A :=
  glue a

  @[hott, induction, elab_as_eliminator] protected def rec {P : susp A → Type _} 
    (PN : P north) (PS : P south) (Pm : Π(a : A), PN =[merid a] PS) (x : susp' A) : P x :=
  begin
    hinduction x using pushout.rec with u u,
    { cases u, exact PN },
    { cases u, exact PS },
    { apply Pm },
  end

  @[hott] theorem rec_merid {P : susp A → Type _} (PN : P north) (PS : P south)
    (Pm : Π(a : A), PN =[merid a] PS) (a : A)
      : apd (susp.rec PN PS Pm) (merid a) = Pm a :=
  begin delta susp.rec, dsimp, exact rec_glue _ _ _ a end

  @[hott, induction] protected def elim {P : Type _} (PN : P) (PS : P) (Pm : A → PN = PS)
    (x : susp' A) : P :=
  susp.rec PN PS (λa, pathover_of_eq _ (Pm a)) x

  @[hott] theorem elim_merid {P : Type _} {PN PS : P} (Pm : A → PN = PS) (a : A)
    : ap (susp.elim PN PS Pm) (merid a) = Pm a :=
  begin
    apply eq_of_fn_eq_fn_inv ((pathover_constant (merid a)) _ _),
    dsimp [susp.elim, susp.rec], refine (apd_eq_pathover_of_eq_ap _ _)⁻¹ ⬝ rec_glue _ _ _ _
  end

  @[hott] protected def elim_type (PN : Type _) (PS : Type _) (Pm : A → PN ≃ PS)
    (x : susp' A) : Type _ :=
  pushout.elim_type (λx, PN) (λx, PS) Pm x

  @[hott] theorem elim_type_merid (PN : Type _) (PS : Type _) (Pm : A → PN ≃ PS)
    (a : A) : transport (susp.elim_type PN PS Pm) (merid a) = Pm a :=
  elim_type_glue _ _ _ _

  @[hott] theorem elim_type_merid_inv {A : Type _} (PN : Type _) (PS : Type _) (Pm : A → PN ≃ PS)
    (a : A) : transport (susp.elim_type PN PS Pm) (merid a)⁻¹ = to_inv (Pm a) :=
  elim_type_glue_inv _ _ _ _

  @[hott] protected def merid_square {a a' : A} (p : a = a')
    : square (merid a) (merid a') idp idp :=
  by induction p; apply vrefl

  open is_trunc is_conn trunc
  -- theorem 8.2.1
  @[hott, instance] def is_conn_susp (n : trunc_index) (A : Type _)
    [H : is_conn n A] : is_conn (n .+1) (susp A) :=
  is_contr.mk (tr north)
  begin
    intro x, hinduction x with x, dsimp at x, hinduction x,
    { refl },
    { hinduction center (trunc n A) with p a, exact ap tr (merid a) },
    { hinduction center (trunc n A) with p a', dsimp,
      apply pathover_of_tr_eq,
      rwr [eq_transport_Fr, idp_con],
      unfreezeI,
      induction n with n IH generalizing H,
      { apply is_prop.elim },
      { change ap (@tr n .+2 (susp A)) (merid a) = ap tr (merid a'),
        hgeneralize : a' = x,
        apply is_conn_fun.elim n
              (is_conn_fun_from_unit n A a)
              (λx : A, trunctype.mk' n (ap (@tr n .+2 (susp A)) (merid a) = ap tr (merid x))),
        intros,
        change ap (@tr n .+2 (susp A)) (merid a) = ap tr (merid a),
        refl }
    }
  end
end
  /- Flattening @[hott] lemma -/

  open prod
  section
    parameters (A : Type _) (PN PS : Type u) (Pm : A → PN ≃ PS)
    include Pm

    private abbreviation P := susp.elim_type PN PS Pm

    private abbreviation F : A × PN → PN := λz, z.2

    private abbreviation G : A × PN → PS := λz, Pm z.1 z.2

    @[hott] protected def flattening : sigma P ≃ pushout F G :=
    begin
      refine pushout.flattening _ _ _ _ _ ⬝e _,
      fapply pushout.equiv,
      { exact sigma.equiv_prod A PN },
      { apply sigma.sigma_unit_left },
      { apply sigma.sigma_unit_left },
      { refl },
      { refl }
    end
  end

end susp

/- Functoriality and equivalence -/
namespace susp
  variables {A : Type _} {B : Type _} (f : A → B)
  include f

  @[hott] def susp_functor' : susp A → susp B :=
  begin
    intro x, dsimp at x, hinduction x with a,
    { exact north },
    { exact south },
    { exact merid (f a) }
  end

  variable [Hf : is_equiv f]
  include Hf

  open is_equiv
  @[hott, instance] protected def is_equiv_functor : is_equiv (susp_functor' f) :=
  adjointify (susp_functor' f) (susp_functor' f⁻¹ᶠ)
  begin abstract {
    intro sb, dsimp at sb, hinduction sb with b, refl, refl,
    apply eq_pathover,
    rwr [ap_id, ap_compose (susp_functor' f) (susp_functor' f⁻¹ᶠ)],
    dsimp [susp_functor'], rwr [susp.elim_merid, susp.elim_merid], apply transpose,
    apply susp.merid_square (right_inv f b)
   } end
  begin abstract {
    intro sa, dsimp at sa, hinduction sa with a, refl, refl,
    apply eq_pathover,
    rwr [ap_id, ap_compose (susp_functor' f⁻¹ᶠ) (susp_functor' f)],
    dsimp [susp_functor'],
    rwr [susp.elim_merid, susp.elim_merid], apply transpose,
    apply susp.merid_square (left_inv f a)
  } end


end susp

namespace susp
  variables {A : Type _} {B : Type _} (f : A ≃ B)

  @[hott] protected def equiv : susp A ≃ susp B :=
  equiv.mk (susp_functor' f) (susp.is_equiv_functor f)
end susp

namespace susp
  open pointed is_trunc
  variables {X : Type*} {X' : Type*} {Y : Type*} {Y' : Type*} {Z : Type*}

  @[hott] def susp_functor (f : X →* Y) : susp X →* susp Y :=
  begin
    fconstructor,
    { exact susp_functor' f },
    { refl }
  end

  @[hott, hsimp] def functor_merid (f : X →* Y) (x : X) : 
    @ap (susp X) (susp Y) (susp_functor f).to_fun _ _ (merid x) = merid (f.to_fun x) :=
  elim_merid _ x

  @[hott] def is_equiv_susp_functor (f : X →* Y) [Hf : is_equiv f]
    : is_equiv (susp_functor f) :=
  susp.is_equiv_functor f

  @[hott] def susp_pequiv (f : X ≃* Y) : susp X ≃* susp Y :=
  pequiv_of_equiv (susp.equiv f.to_equiv) idp

set_option pp.coercions true
  @[hott] def susp_functor_pcompose (g : Y →* Z) (f : X →* Y) :
    susp_functor (g ∘* f) ~* susp_functor g ∘* susp_functor f :=
  begin
    fapply phomotopy.mk,
    { intro x, dsimp at *, hinduction x,
      { refl },
      { refl },
      { apply eq_pathover, apply hdeg_square,
        refine functor_merid _ _ ⬝ _ ⬝ (ap_compose (susp_functor g) _ _)⁻¹ᵖ,
        hsimp, refl }},
    { refl },
  end

  @[hott] def susp_functor_phomotopy {f g : X →* Y} (p : f ~* g) :
    susp_functor f ~* susp_functor g :=
  begin
    fapply phomotopy.mk,
    { intro x, dsimp at *, hinduction x,
      { refl },
      { refl },
      { apply eq_pathover, apply hdeg_square, refine (elim_merid _ _) ⬝ _ ⬝ (elim_merid _ _)⁻¹ᵖ,
        exact ap merid (p a), }},
    { refl },
  end

  @[hott] def susp_functor_pid (A : Type*) : susp_functor (pid A) ~* pid (susp A) :=
  begin
    fapply phomotopy.mk,
    { intro x, dsimp at x, hinduction x,
      { refl },
      { refl },
      { apply eq_pathover_id_right, apply hdeg_square, apply elim_merid }},
    { refl },
  end

  /- adjunction originally  ported from Coq-HoTT,
     but we proved some additional naturality conditions -/

  @[hott] def loop_susp_unit (X : Type*) : X →* Ω(susp X) :=
  begin
    fconstructor,
    { intro x, exact merid x ⬝ (merid pt)⁻¹ },
    { apply con.right_inv },
  end
/-
 (eq.rec (refl (refl (susp_functor' f ((⅀ X).Point))))
               (ap (susp_functor' f) ((loop_susp_unit {carrier := X, Point := x}).to_fun x)) ⬝
             (ap_con (susp_functor' f) (merid x) (merid x)⁻¹ ⬝
                whisker_left (ap (susp_functor' f) (merid x)) (ap_inv (susp_functor' f) (merid x))) ⬝
           elim_merid (λ (a : X), merid (f a)) x ◾ (elim_merid (λ (a : X), merid (f a)) x)⁻²)⁻¹ ⬝
      (ap ((Ω→ (susp_functor {to_fun := f, resp_pt := refl (f x)})).to_fun)
           ((loop_susp_unit {carrier := X, Point := x}).resp_pt) ⬝
         (Ω→ (susp_functor {to_fun := f, resp_pt := refl (f x)})).resp_pt) =
    refl ((loop_susp_unit {carrier := Y, Point := f x}).to_fun (f x)) ⬝
      (loop_susp_unit {carrier := Y, Point := f x}).resp_pt
-/
  @[hott] def loop_susp_unit_natural (f : X →* Y)
    : loop_susp_unit Y ∘* f ~* Ω→ (susp_functor f) ∘* loop_susp_unit X :=
  begin
    induction X with X x, induction Y with Y y, induction f with f pf, dsimp at *, induction pf,
    fapply phomotopy.mk,
    { intro x', symmetry,
      exact
        ap1_gen_idp_left _ _ ⬝
        (ap_con _ _ _ ⬝ whisker_left _ (ap_inv _ _)) ⬝
        elim_merid _ _ ◾ (elim_merid _ _)⁻² },
    { dsimp [loop_susp_unit, -con.right_inv, -ap1_gen_idp_left], refine _ ⬝ (idp_con _)⁻¹ᵖ,
      apply inv_con_eq_of_eq_con,
      refine _ ⬝ con.assoc' _ _ _, rwr inverse2_right_inv,
      refine _ ⬝ con.assoc' _ _ _,
      rwr [ap_con_right_inv],
      rwr [ap1_gen_idp_left_con],
      rwr [←ap_compose (concat idp)] },
  end

  @[hott] def loop_susp_counit (X : Type*) : susp (Ω X) →* X :=
  begin
    fapply pmap.mk,
    { intro x, dsimp at x, hinduction x, exact pt, exact pt, exact a },
    { refl },
  end

  @[hott] def loop_susp_counit_natural (f : X →* Y)
    : f ∘* loop_susp_counit X ~* loop_susp_counit Y ∘* (susp_functor (ap1 f)) :=
  begin
    induction X with X x, induction Y with Y y, induction f with f pf, dsimp at *, induction pf,
    fconstructor,
    { intro x', dsimp at *, hinduction x' with p,
      { refl },
      { refl },
      { apply eq_pathover, apply hdeg_square, dsimp [pcompose, loop_susp_counit],
        rwr [ap_compose f, ap_compose (susp.elim (f x) (f x) (λ (a : f x = f x), a))],
        dsimp [susp_functor, susp_functor'], rwr [elim_merid, elim_merid, elim_merid],
        dsimp [ap1], rwr [ap1_gen_idp_left] }},
    { refl }
  end

  @[hott] def loop_susp_counit_unit (X : Type*)
    : ap1 (loop_susp_counit X) ∘* loop_susp_unit (Ω X) ~* pid (Ω X) :=
  begin
    induction X with X x, fconstructor,
    { intro p, 
      refine (ap1_gen_idp_left _ _) ⬝
             (ap_con _ _ _ ⬝
             whisker_left _ (ap_inv _ _)) ⬝ _,
      refine (elim_merid _ _ ◾ (elim_merid _ _)⁻²) ⬝ _, refl },
    { dsimp [loop_susp_unit, -ap1_gen_idp_left, -con.right_inv], 
      refine idp ◾ ((con_idp _)⁻¹ᵖ ⬝ inverse2_right_inv _) ⬝ _,
      refine con.assoc _ _ _ ⬝ _,
      refine whisker_left _ (ap_con_right_inv (susp.elim x x (λa, a)) (merid (refl x))) ⬝ _,
      rwr [ap1_gen_idp_left_con, ←ap_compose] }
  end

  @[hott] def loop_susp_unit_counit (X : Type*)
    : loop_susp_counit (susp X) ∘* susp_functor (loop_susp_unit X) ~* pid (susp X) :=
  begin
    induction X with X x, fconstructor,
    { intro x', dsimp at *, hinduction x',
      { refl },
      { exact merid x },
      { apply eq_pathover, dsimp [pid, pcompose, loop_susp_counit], 
        refine ap_compose (susp.elim north north (λa, a)) _ _ ⬝ph _ ⬝hp (ap_id _)⁻¹ᵖ,
        refine ap02 _ (functor_merid _ _) ⬝ elim_merid _ _ ⬝ph _,
        apply square_of_eq, exact idp_con _ ⬝ (inv_con_cancel_right _ _)⁻¹ }},
    { refl }
  end

  @[hott] def susp_elim {X Y : Type*} (f : X →* Ω Y) : susp X →* Y :=
  loop_susp_counit Y ∘* susp_functor f

  @[hott] def loop_susp_intro {X Y : Type*} (f : susp X →* Y) : X →* Ω Y :=
  ap1 f ∘* loop_susp_unit X

  @[hott] def susp_elim_susp_functor {A B C : Type*} (g : B →* Ω C) (f : A →* B) :
    susp_elim g ∘* susp_functor f ~* susp_elim (g ∘* f) :=
  begin
    refine passoc _ _ _ ⬝* _, exact pwhisker_left _ (susp_functor_pcompose _ _)⁻¹*
  end

  @[hott] def susp_elim_phomotopy {A B : Type*} {f g : A →* Ω B} (p : f ~* g) : susp_elim f ~* susp_elim g :=
  pwhisker_left _ (susp_functor_phomotopy p)

  @[hott] def susp_elim_natural {X Y Z : Type*} (g : Y →* Z) (f : X →* Ω Y)
    : g ∘* susp_elim f ~* susp_elim (Ω→ g ∘* f) :=
  begin
    refine _ ⬝* pwhisker_left _ (susp_functor_pcompose _ _)⁻¹*,
    refine (passoc _ _ _)⁻¹* ⬝* _ ⬝* passoc _ _ _,
    exact pwhisker_right _ (loop_susp_counit_natural _)
  end

  @[hott] def loop_susp_intro_natural {X Y Z : Type*} (g : susp Y →* Z) (f : X →* Y) :
    loop_susp_intro (g ∘* susp_functor f) ~* loop_susp_intro g ∘* f :=
  pwhisker_right _ (ap1_pcompose _ _) ⬝* passoc _ _ _ ⬝* 
  pwhisker_left _ (loop_susp_unit_natural _)⁻¹* ⬝* (passoc _ _ _)⁻¹*

  @[hott] def susp_adjoint_loop_right_inv {X Y : Type*} (g : X →* Ω Y) :
    loop_susp_intro (susp_elim g) ~* g :=
  begin
    refine pwhisker_right _ (ap1_pcompose _ _) ⬝* _,
    refine passoc _ _ _ ⬝* _,
    refine pwhisker_left _ (loop_susp_unit_natural _)⁻¹* ⬝* _,
    refine (passoc _ _ _)⁻¹* ⬝* _,
    refine pwhisker_right _ (loop_susp_counit_unit _) ⬝* _,
    apply pid_pcompose
  end

  @[hott] def susp_adjoint_loop_left_inv {X Y : Type*} (f : susp X →* Y) :
    susp_elim (loop_susp_intro f) ~* f :=
  begin
    refine pwhisker_left _ (susp_functor_pcompose _ _) ⬝* _,
    refine (passoc _ _ _)⁻¹* ⬝* _,
    refine pwhisker_right _ (loop_susp_counit_natural _)⁻¹* ⬝* _,
    refine passoc _ _ _ ⬝* _,
    refine pwhisker_left _ (loop_susp_unit_counit _) ⬝* _,
    apply pcompose_pid
  end

  @[hott] def susp_adjoint_loop_unpointed (X Y : Type*) : susp X →* Y ≃ X →* Ω Y :=
  begin
    fapply equiv.MK,
    { exact loop_susp_intro },
    { exact susp_elim },
    { intro g, apply eq_of_phomotopy, exact susp_adjoint_loop_right_inv g },
    { intro f, apply eq_of_phomotopy, exact susp_adjoint_loop_left_inv f }
  end

  @[hott] def susp_functor_pconst_homotopy {X Y : Type*} (x : susp X) :
    susp_functor (pconst X Y) x = pt :=
  begin
    dsimp at x, hinduction x,
    { refl },
    { exact (merid pt)⁻¹ },
    { apply eq_pathover, refine (elim_merid _ _) ⬝ph _ ⬝hp (ap_constant _ _)⁻¹, exact square_of_eq (con.right_inv _)⁻¹ }
  end

  @[hott] def susp_functor_pconst (X Y : Type*) : susp_functor (pconst X Y) ~* pconst (susp X) (susp Y) :=
  begin
    fapply phomotopy.mk,
    { exact susp_functor_pconst_homotopy },
    { refl }
  end

  @[hott] def susp_pfunctor (X Y : Type*) : ppmap X Y →* ppmap (susp X) (susp Y) :=
  pmap.mk susp_functor (eq_of_phomotopy (susp_functor_pconst _ _))

  @[hott] def susp_pelim (X Y : Type*) : ppmap X (Ω Y) →* ppmap (susp X) Y :=
  ppcompose_left (loop_susp_counit Y) ∘* susp_pfunctor X (Ω Y)

  @[hott] def loop_susp_pintro (X Y : Type*) : ppmap (susp X) Y →* ppmap X (Ω Y) :=
  ppcompose_right (loop_susp_unit X) ∘* pap1 (susp X) Y

  @[hott] def loop_susp_pintro_natural_left (f : X' →* X) :
    psquare (loop_susp_pintro X Y) (loop_susp_pintro X' Y)
            (ppcompose_right (susp_functor f)) (ppcompose_right f) :=
  pap1_natural_left _ ⬝h* ppcompose_right_psquare (loop_susp_unit_natural f)⁻¹*

  @[hott] def loop_susp_pintro_natural_right (f : Y →* Y') :
    psquare (loop_susp_pintro X Y) (loop_susp_pintro X Y')
            (ppcompose_left f) (ppcompose_left (Ω→ f)) :=
  pap1_natural_right _ ⬝h* (ppcompose_left_ppcompose_right _ _)⁻¹*

  @[hott] def is_equiv_loop_susp_pintro (X Y : Type*) :
    is_equiv (loop_susp_pintro X Y) :=
  begin
    fapply adjointify,
    { exact susp_pelim X Y },
    { intro g, apply eq_of_phomotopy, exact susp_adjoint_loop_right_inv g },
    { intro f, apply eq_of_phomotopy, exact susp_adjoint_loop_left_inv f }
  end

  -- @[hott] def susp_adjoint_loop (X Y : Type*) : ppmap (susp X) Y ≃* ppmap X (Ω Y) :=
  -- pequiv_of_pmap (loop_susp_pintro X Y) (is_equiv_loop_susp_pintro X Y)

  -- @[hott] def susp_adjoint_loop_natural_right (f : Y →* Y') :
  --   psquare (susp_adjoint_loop X Y).to_pmap (susp_adjoint_loop X Y').to_pmap
  --           (ppcompose_left f) (ppcompose_left (Ω→ f)) :=
  -- loop_susp_pintro_natural_right f

  -- @[hott] def susp_adjoint_loop_natural_left (f : X' →* X) :
  --   psquare (susp_adjoint_loop X Y).to_pmap (susp_adjoint_loop X' Y).to_pmap
  --           (ppcompose_right (susp_functor f)) (ppcompose_right f) :=
  -- loop_susp_pintro_natural_left f

  -- @[hott] def ap1_susp_elim {A : Type*} {X : Type*} (p : A →* Ω X) :
  --   Ω→(susp_elim p) ∘* loop_susp_unit A ~* p :=
  -- susp_adjoint_loop_right_inv p

  -- /- the underlying homotopies of susp_adjoint_loop_natural_* -/
  -- @[hott] def susp_adjoint_loop_nat_right (f : susp X →* Y) (g : Y →* Z)
  --   : (susp_adjoint_loop X Z).to_pmap (g ∘* f) ~* ap1 g ∘* (susp_adjoint_loop X Y).to_pmap f :=
  -- begin
  --   dsimp [susp_adjoint_loop],
  --   refine _ ⬝* passoc _ _ _,
  --   apply pwhisker_right,
  --   apply ap1_pcompose
  -- end

  -- @[hott] def susp_adjoint_loop_nat_left (f : Y →* Ω Z) (g : X →* Y)
  --   : (susp_adjoint_loop X Z)⁻¹ᵉ (f ∘* g) ~* (susp_adjoint_loop Y Z)⁻¹ᵉ f ∘* susp_functor g :=
  -- begin
  --   esimp [susp_adjoint_loop],
  --   refine _ ⬝* (passoc _ _ _)⁻¹*,
  --   apply pwhisker_left,
  --   apply susp_functor_pcompose
  -- end

  -- /- iterated suspension -/
  -- @[hott] def iterate_susp (n : ℕ) (A : Type*) : Type* := iterate (λX, susp X) n A

  -- open is_conn trunc_index nat
  -- @[hott] def iterate_susp_succ (n : ℕ) (A : Type*) :
  --   iterate_susp (succ n) A = susp (iterate_susp n A) :=
  -- idp

  -- @[hott] def is_conn_iterate_susp [instance] (n : ℕ₋₂) (m : ℕ) (A : Type*)
  --   [H : is_conn n A] : is_conn (n + m) (iterate_susp m A) :=
  -- begin induction m with m IH, exact H, exact @is_conn_susp _ _ IH end

  -- -- Separate cases for n = 0, which comes up often
  -- @[hott] def is_conn_iterate_susp_zero [instance] (m : ℕ) (A : Type*)
  --   [H : is_conn 0 A] : is_conn m (iterate_susp m A) :=
  -- begin induction m with m IH, exact H, exact @is_conn_susp _ _ IH end

  -- @[hott] def iterate_susp_functor (n : ℕ) {A B : Type*} (f : A →* B) :
  --   iterate_susp n A →* iterate_susp n B :=
  -- begin
  --   induction n with n g,
  --   { exact f },
  --   { exact susp_functor g }
  -- end

  -- @[hott] def iterate_susp_succ_in (n : ℕ) (A : Type*) :
  --   iterate_susp (succ n) A ≃* iterate_susp n (susp A) :=
  -- begin
  --   induction n with n IH,
  --   { refl},
  --   { exact susp_pequiv IH}
  -- end

  -- @[hott] def iterate_susp_adjoint_loopn (X Y : Type*) (n : ℕ) :
  --   ppmap (iterate_susp n X) Y ≃* ppmap X (Ω[n] Y) :=
  -- begin
  --   induction n with n IH generalizing X Y,
  --   { refl },
  --   { refine susp_adjoint_loop _ _ ⬝e* IH _ _ ⬝e* _, apply pequiv_ppcompose_left,
  --     symmetry, apply loopn_succ_in }
  -- end

end susp
end hott