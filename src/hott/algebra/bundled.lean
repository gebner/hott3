/-
Copyright (c) 2015 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad

Bundled structures
-/
import .ring

universes u v w
hott_theory

namespace hott

open algebra pointed is_trunc

namespace algebra
@[hott] structure Semigroup :=
(carrier : Type _) (struct : semigroup carrier)

@[hott] instance has_coe_to_sort_Semigroup : has_coe_to_sort Semigroup := 
⟨_, Semigroup.carrier⟩
attribute [instance] Semigroup.struct 

@[hott] structure CommSemigroup :=
(carrier : Type _) (struct : comm_semigroup carrier)

@[hott] instance has_coe_to_sort_CommSemigroup : has_coe_to_sort CommSemigroup := 
⟨_, CommSemigroup.carrier⟩
attribute [instance] CommSemigroup.struct 

@[hott] structure Monoid :=
(carrier : Type _) (struct : monoid carrier)

@[hott] instance has_coe_to_sort_Monoid : has_coe_to_sort Monoid := 
⟨_, Monoid.carrier⟩
attribute [instance] Monoid.struct 

@[hott] structure CommMonoid :=
(carrier : Type _) (struct : comm_monoid carrier)

@[hott] instance has_coe_to_sort_CommMonoid : has_coe_to_sort CommMonoid := 
⟨_, CommMonoid.carrier⟩
attribute [instance] CommMonoid.struct

@[hott] structure Group :=
(carrier : Type _) (struct' : group carrier)

attribute [instance] Group.struct' 

@[hott, reducible] def pSet_of_Group (G : Group) : Set* :=
ptrunctype.mk (pType.mk (Group.carrier G) 1) (semigroup.is_set_carrier _)

@[hott] instance has_coe_Group_pSet : has_coe Group Set* := 
⟨pSet_of_Group⟩

@[hott, instance, priority 2000] def Group.struct (G : Group) : group G :=
Group.struct' G

@[hott, reducible] def pType_of_Group (G : Group.{u}) : pType.{u} :=
↑(↑G : pSet.{u})
@[hott, reducible] def Set_of_Group (G : Group.{u}) : Set.{u} :=
↑(↑G : pSet.{u})

@[hott] structure AbGroup :=
(carrier : Type _) (struct' : ab_group carrier)

attribute [instance] AbGroup.struct'

section
@[hott] def Group_of_AbGroup (G : AbGroup) : Group :=
Group.mk G.carrier (ab_group.to_group _)

@[hott] instance has_coe_AbGroup_Group : has_coe AbGroup Group :=
⟨Group_of_AbGroup⟩
end

@[hott, instance, priority 2000] def AbGroup.struct (G : AbGroup) : ab_group G :=
AbGroup.struct' G

-- some bundled infinity-structures
@[hott] structure InfGroup :=
(carrier : Type _) (struct' : inf_group carrier)

attribute [instance] InfGroup.struct'

@[hott, reducible] def pType_of_InfGroup (G : InfGroup) : Type* :=
pType.mk G.carrier 1

@[hott] instance has_coe_InfGroup_pType : has_coe InfGroup Type* :=
⟨pType_of_InfGroup⟩

@[hott, instance, priority 2000] def InfGroup.struct (G : InfGroup) : inf_group G :=
InfGroup.struct' G

@[hott] structure AbInfGroup :=
(carrier : Type _) (struct' : ab_inf_group carrier)

attribute [instance] AbInfGroup.struct'

@[hott] def InfGroup_of_AbInfGroup (G : AbInfGroup) : InfGroup :=
⟨G.carrier, by apply_instance⟩

@[hott] instance has_coe_AbInfGroup_InfGroup : has_coe AbInfGroup InfGroup :=
⟨InfGroup_of_AbInfGroup⟩

@[hott, instance, priority 2000] def AbInfGroup.struct (G : AbInfGroup) : ab_inf_group G :=
G.struct'

@[hott] def InfGroup_of_Group (G : Group) : InfGroup :=
InfGroup.mk G (by apply_instance)

@[hott] def AbInfGroup_of_AbGroup (G : AbGroup) : AbInfGroup :=
AbInfGroup.mk G (by apply_instance)

/- rings -/
@[hott] structure Ring :=
(carrier : Type _) (struct : ring carrier)

instance has_coe_Ring : has_coe_to_sort Ring.{u} :=
⟨Type u, Ring.carrier⟩
attribute [instance] Ring.struct

end algebra

end hott