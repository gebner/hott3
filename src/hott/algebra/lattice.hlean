/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jeremy Avigad
-/
import .order

open eq

variable {A : Type _}
set_option class.force_new true

/- lattices (we could split this to upper- and lower-semilattices, if needed) -/

namespace algebra
structure lattice [class] (A : Type _) extends weak_order A :=
(inf : A → A → A)
(sup : A → A → A)
(inf_le_left : Π a b, le (inf a b) a)
(inf_le_right : Π a b, le (inf a b) b)
(le_inf : Πa b c, le c a → le c b → le c (inf a b))
(le_sup_left : Π a b, le a (sup a b))
(le_sup_right : Π a b, le b (sup a b))
(sup_le : Π a b c, le a c → le b c → le (sup a b) c)

@[hott] def inf := @lattice.inf
@[hott] def sup := @lattice.sup
infix ` ⊓ `:70 := inf
infix ` ⊔ `:65 := sup

section
  variable [s : lattice A]
  include s

  @[hott] theorem inf_le_left (a b : A) : a ⊓ b ≤ a := !lattice.inf_le_left

  @[hott] theorem inf_le_right (a b : A) : a ⊓ b ≤ b := !lattice.inf_le_right

  @[hott] theorem le_inf {a b c : A} (H₁ : c ≤ a) (H₂ : c ≤ b) : c ≤ a ⊓ b := !lattice.le_inf H₁ H₂

  @[hott] theorem le_sup_left (a b : A) : a ≤ a ⊔ b := !lattice.le_sup_left

  @[hott] theorem le_sup_right (a b : A) : b ≤ a ⊔ b := !lattice.le_sup_right

  @[hott] theorem sup_le {a b c : A} (H₁ : a ≤ c) (H₂ : b ≤ c) : a ⊔ b ≤ c := !lattice.sup_le H₁ H₂

  /- inf -/

  @[hott] theorem eq_inf {a b c : A} (H₁ : c ≤ a) (H₂ : c ≤ b) (H₃ : Π{d}, d ≤ a → d ≤ b → d ≤ c) :
    c = a ⊓ b :=
  le.antisymm (le_inf H₁ H₂) (H₃ !inf_le_left !inf_le_right)

  @[hott] theorem inf.comm (a b : A) : a ⊓ b = b ⊓ a :=
  eq_inf !inf_le_right !inf_le_left (λ c H₁ H₂, le_inf H₂ H₁)

  @[hott] theorem inf.assoc (a b c : A) : (a ⊓ b) ⊓ c = a ⊓ (b ⊓ c) :=
  begin
    apply eq_inf,
    { apply le.trans, apply inf_le_left, apply inf_le_left },
    { apply le_inf, apply le.trans, apply inf_le_left, apply inf_le_right, apply inf_le_right },
    { intros [d, H₁, H₂], apply le_inf, apply le_inf H₁, apply le.trans H₂, apply inf_le_left,
      apply le.trans H₂, apply inf_le_right }
  end

  @[hott] theorem inf.left_comm (a b c : A) : a ⊓ (b ⊓ c) = b ⊓ (a ⊓ c) :=
  binary.left_comm (@inf.comm A s) (@inf.assoc A s) a b c

  @[hott] theorem inf.right_comm (a b c : A) : (a ⊓ b) ⊓ c = (a ⊓ c) ⊓ b :=
  binary.right_comm (@inf.comm A s) (@inf.assoc A s) a b c

  @[hott] theorem inf_self (a : A) : a ⊓ a = a :=
  by apply inverse; apply eq_inf (le.refl a) !le.refl; intros; assumption

  @[hott] theorem inf_eq_left {a b : A} (H : a ≤ b) : a ⊓ b = a :=
  by apply inverse; apply eq_inf !le.refl H; intros; assumption

  @[hott] theorem inf_eq_right {a b : A} (H : b ≤ a) : a ⊓ b = b :=
  eq.subst !inf.comm (inf_eq_left H)

  /- sup -/

  @[hott] theorem eq_sup {a b c : A} (H₁ : a ≤ c) (H₂ : b ≤ c) (H₃ : Π{d}, a ≤ d → b ≤ d → c ≤ d) :
    c = a ⊔ b :=
  le.antisymm (H₃ !le_sup_left !le_sup_right) (sup_le H₁ H₂)

  @[hott] theorem sup.comm (a b : A) : a ⊔ b = b ⊔ a :=
  eq_sup !le_sup_right !le_sup_left (λ c H₁ H₂, sup_le H₂ H₁)

  @[hott] theorem sup.assoc (a b c : A) : (a ⊔ b) ⊔ c = a ⊔ (b ⊔ c) :=
  begin
    apply eq_sup,
    { apply le.trans, apply le_sup_left a b, apply le_sup_left },
    { apply sup_le, apply le.trans, apply le_sup_right a b, apply le_sup_left, apply le_sup_right },
    { intros [d, H₁, H₂], apply sup_le, apply sup_le H₁, apply le.trans !le_sup_left H₂,
      apply le.trans !le_sup_right H₂}
  end

  @[hott] theorem sup.left_comm (a b c : A) : a ⊔ (b ⊔ c) = b ⊔ (a ⊔ c) :=
  binary.left_comm (@sup.comm A s) (@sup.assoc A s) a b c

  @[hott] theorem sup.right_comm (a b c : A) : (a ⊔ b) ⊔ c = (a ⊔ c) ⊔ b :=
  binary.right_comm (@sup.comm A s) (@sup.assoc A s) a b c

  @[hott] theorem sup_self (a : A) : a ⊔ a = a :=
  by apply inverse; apply eq_sup (le.refl a) !le.refl; intros; assumption

  @[hott] theorem sup_eq_left {a b : A} (H : b ≤ a) : a ⊔ b = a :=
  by apply inverse; apply eq_sup !le.refl H; intros; assumption

  @[hott] theorem sup_eq_right {a b : A} (H : a ≤ b) : a ⊔ b = b :=
  eq.subst !sup.comm (sup_eq_left H)
end

end algebra
