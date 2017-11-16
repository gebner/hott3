/-
Copyright (c) 2014 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Floris van Doorn

Theorems about W-types (well-founded trees)
-/

import .sigma .pi

universes u v w
hott_theory

namespace hott
open decidable

open hott.eq hott.equiv hott.is_equiv sigma

inductive Wtype {A : Type u} (B : A → Type v) : Type (max u v) |
sup : Π (a : A), (B a → Wtype) → Wtype

namespace Wtype
  notation `W` binders `, ` r:(scoped B, Wtype B) := r

  variables {A A' : Type u} {B B' : A → Type v} {C : Π(a : A), B a → Type _}
            {a a' : A} {f : B a → W a, B a} {f' : B a' → W a, B a} {w w' : W(a : A), B a}

  @[hott] protected def fst (w : W(a : A), B a) : A :=
  by induction w with a f; exact a

  @[hott] protected def snd (w : W(a : A), B a) : B w.fst → W(a : A), B a :=
  by induction w with a f; exact f

  
  @[hott] protected def eta (w : W a, B a) : sup w.fst  w.snd = w :=
  by induction w; exact idp


  @[hott] def sup_eq_sup (p : a = a') (q : f =[p; λa, B a → W a, B a] f') : sup a f = sup a' f' :=
  by induction q; exact idp

  @[hott] def Wtype_eq (p : Wtype.fst w = Wtype.fst w') (q : Wtype.snd w =[p;λ a, B a → W(a : A), B a] Wtype.snd w') : w = w' :=
  by induction w; induction w';exact (sup_eq_sup p q)

  @[hott] def Wtype_eq_fst (p : w = w') : w.fst = w'.fst :=
  by induction p;exact idp

  @[hott] def Wtype_eq_snd (p : w = w') : w.snd =[Wtype_eq_fst p; λ a, B a → W(a : A), B a] w'.snd :=
  by induction p;exact idpo

  namespace ops
  postfix `..fst`:(max+1) := Wtype_eq_fst
  postfix `..snd`:(max+1) := Wtype_eq_snd
  end ops open ops open sigma

  
  @[hott] def sup_path_W (p : w.fst = w'.fst) (q : w.snd =[p; λ a, B a → W(a : A), B a] w'.snd)
    : @dpair 
        (w.fst=w'.fst) 
        (λp, w.snd =[p; λ a, B a → W(a : A), B a] w'.snd) 
        (Wtype_eq p q)..fst 
        (Wtype_eq p q)..snd 
    = ⟨p, q⟩ :=
  begin induction w with a f, 
        induction w' with a' f',
        dsimp [Wtype.fst] at p,
        dsimp [Wtype.snd] at q,        
        -- hinduction_only q using pathover.rec, 
        -- exact idp 
        exact sorry
  end

  @[hott] def fst_path_W (p : w.fst = w'.fst) (q : w.snd =[p; λ a, B a → W(a : A), B a] w'.snd) : (Wtype_eq p q)..fst = p :=
  (sup_path_W _ _)..1

  @[hott] def snd_path_W (p : w.fst = w'.fst) (q : w.snd =[p; λ a, B a → W(a : A), B a] w'.snd)
      : (Wtype_eq p q)..snd =[fst_path_W p q; λp, w.snd =[p; λ a, B a → W(a : A), B a] w'.snd] q :=
  (sup_path_W _ _)..2

  @[hott] def eta_path_W (p : w = w') : Wtype_eq (p..fst) (p..snd) = p :=
  by induction p; induction w; exact idp

  @[hott] def transport_fst_path_W {B' : A → Type _} (p : w.fst = w'.fst) (q : w.snd =[p; λ a, B a → W(a : A), B a] w'.snd)
      : transport (λ(x:W a, B a), B' x.fst) (Wtype_eq p q) = transport B' p :=
  begin 
    induction w with a f, 
    induction w' with a f', 
    dsimp [Wtype.fst] at p,
    dsimp [Wtype.snd] at q,        
    -- hinduction q,
    -- exact idp 
    exact sorry
  end

  @[hott] def path_W_uncurried (pq : Σ(p : w.fst = w'.fst), w.snd =[p; λ a, B a → W(a : A), B a] w'.snd) : w = w' :=
  by induction pq with p q; exact (Wtype_eq p q)

  @[hott] def sup_path_W_uncurried (pq : Σ(p : w.fst = w'.fst), w.snd =[p; λ a, B a → W(a : A), B a] w'.snd)
      :  @dpair (w.fst = w'.fst) (λp, w.snd =[p; λ a, B a → W(a : A), B a] w'.snd) (path_W_uncurried pq)..fst (path_W_uncurried pq)..snd = pq :=
  by induction pq with p q; exact (sup_path_W p q)

  @[hott] def fst_path_W_uncurried (pq : Σ(p : w.fst = w'.fst), w.snd =[p; λ a, B a → W(a : A), B a] w'.snd)
      : (path_W_uncurried pq)..fst = pq.fst :=
  (sup_path_W_uncurried _)..1

  @[hott] def snd_path_W_uncurried (pq : Σ(p : w.fst = w'.fst), w.snd =[p; λ a, B a → W(a : A), B a] w'.snd)
      : (path_W_uncurried pq)..snd =[fst_path_W_uncurried pq; λ p, w.snd =[p; λ a, B a → W(a : A), B a] w'.snd] pq.snd :=
  (sup_path_W_uncurried _)..2

  @[hott] def eta_path_W_uncurried (p : w = w') : path_W_uncurried ⟨p..fst, p..snd⟩ = p :=
  eta_path_W _

  @[hott] def transport_fst_path_W_uncurried {B' : A → Type _} (pq : Σ(p : w.fst = w'.fst), w.snd =[p; λ a, B a → W(a : A), B a] w'.snd)
      : transport (λ(x:W a, B a), B' x.fst) (@path_W_uncurried A B w w' pq) = transport B' pq.fst :=
  by induction pq with p q; exact (transport_fst_path_W p q)

  @[hott] def isequiv_path_W /-[instance]-/ (w w' : W a, B a)
      : is_equiv (path_W_uncurried : (Σ(p : w.fst = w'.fst), w.snd =[p; λ a, B a → W(a : A), B a] w'.snd) → w = w') :=
  adjointify path_W_uncurried
             (λp, ⟨p..fst, p..snd⟩)
             eta_path_W_uncurried
             sup_path_W_uncurried

  @[hott] def equiv_path_W (w w' : W a, B a) : (Σ(p : w.fst = w'.fst), w.snd =[p; λ a, B a → W(a : A), B a] w'.snd) ≃ (w = w') :=
  equiv.mk path_W_uncurried (isequiv_path_W _ _)

  @[hott] def double_induction_on {P : (W a, B a) → (W a, B a) → Type _} (w w' : W a, B a)
    (H : ∀ (a a' : A) (f : B a → W a, B a) (f' : B a' → W a, B a),
      (∀ (b : B a) (b' : B a'), P (f b) (f' b')) → P (sup a f) (sup a' f')) : P w w' :=
  begin
    revert w',
    induction w with a f IH,
    intro w',
    induction w' with a' f',
    apply H, intros b b',
    apply IH
  end

  /- truncatedness -/
  open is_trunc pi hott.sigma hott.pi

#check @sigma.is_trunc_sigma

local attribute [instance] is_trunc_pi_eq

  @[hott, instance] def is_trunc_W (n : trunc_index)
    [HA : is_trunc (n.+1) A] : is_trunc (n.+1) (W a, B a) :=
  begin
  fapply is_trunc_succ_intro, intros w w',
  eapply (double_induction_on w w'), intros a a' f f' IH,
  apply is_trunc_equiv_closed,
  apply equiv_path_W,
  dsimp [Wtype.fst,Wtype.snd],
  let HD : Π (p : a = a'), is_trunc n (f =[p; λ (a : A), B a → Wtype B] f'),
  intro p, 
  induction p, apply is_trunc_equiv_closed_rev,
      apply pathover_idp, apply_instance,
      apply is_trunc_sigma,
  end

end Wtype

end hott
