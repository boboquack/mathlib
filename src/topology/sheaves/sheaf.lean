/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import topology.sheaves.sheaf_condition.equalizer_products
import category_theory.full_subcategory
import category_theory.limits.unit
import category_theory.sites.sheaf
import category_theory.sites.spaces

/-!
# Sheaves

We define sheaves on a topological space, with values in an arbitrary category with products.

The sheaf condition for a `F : presheaf C X` requires that the morphism
`F.obj U ⟶ ∏ F.obj (U i)` (where `U` is some open set which is the union of the `U i`)
is the equalizer of the two morphisms
`∏ F.obj (U i) ⟶ ∏ F.obj (U i ⊓ U j)`.

We provide the instance `category (sheaf C X)` as the full subcategory of presheaves,
and the fully faithful functor `sheaf.forget : sheaf C X ⥤ presheaf C X`.

## Equivalent conditions

While the "official" definition is in terms of an equalizer diagram,
in `src/topology/sheaves/sheaf_condition/pairwise_intersections.lean`
and in `src/topology/sheaves/sheaf_condition/open_le_cover.lean`
we provide two equivalent conditions (and prove they are equivalent).

The first is that `F.obj U` is the limit point of the diagram consisting of all the `F.obj (U i)`
and `F.obj (U i ⊓ U j)`.
(That is, we explode the equalizer of two products out into its component pieces.)

The second is that `F.obj U` is the limit point of the diagram constisting of all the `F.obj V`,
for those `V : opens X` such that `V ≤ U i` for some `i`.
(This condition is particularly easy to state, and perhaps should become the "official" definition.)

-/

universes w v u

noncomputable theory

open category_theory
open category_theory.limits
open topological_space
open opposite
open topological_space.opens

namespace Top

variables {C : Type u} [category.{v} C]
variables {X : Top.{w}} (F : presheaf C X) {ι : Type v} (U : ι → opens X)

namespace presheaf

open sheaf_condition_equalizer_products

/--
The sheaf condition for a `F : presheaf C X` requires that the morphism
`F.obj U ⟶ ∏ F.obj (U i)` (where `U` is some open set which is the union of the `U i`)
is the equalizer of the two morphisms
`∏ F.obj (U i) ⟶ ∏ F.obj (U i) ⊓ (U j)`.
-/
def is_sheaf (F : presheaf.{w v u} C X) : Prop :=
presheaf.is_sheaf (opens.grothendieck_topology X) F

/--
The presheaf valued in `unit` over any topological space is a sheaf.
-/
lemma is_sheaf_unit (F : presheaf (category_theory.discrete unit) X) : F.is_sheaf :=
λ x U S hS x hx, ⟨eq_to_hom (subsingleton.elim _ _), by tidy, by tidy⟩

lemma is_sheaf_iso_iff {F G : presheaf C X} (α : F ≅ G) : F.is_sheaf ↔ G.is_sheaf :=
presheaf.is_sheaf_of_iso_iff α

/--
Transfer the sheaf condition across an isomorphism of presheaves.
-/
lemma is_sheaf_of_iso {F G : presheaf C X} (α : F ≅ G) (h : F.is_sheaf) : G.is_sheaf :=
(is_sheaf_iso_iff α).1 h

end presheaf

variables (C X)

/--
A `sheaf C X` is a presheaf of objects from `C` over a (bundled) topological space `X`,
satisfying the sheaf condition.
-/
@[derive category]
def sheaf : Type (max u v w) := Sheaf (opens.grothendieck_topology X) C

variables {C X}

/-- The underlying presheaf of a sheaf -/
abbreviation sheaf.presheaf (F : X.sheaf C) : Top.presheaf C X := F.1

variables (C X)

-- Let's construct a trivial example, to keep the inhabited linter happy.
instance sheaf_inhabited : inhabited (sheaf (category_theory.discrete punit) X) :=
⟨⟨functor.star _, presheaf.is_sheaf_unit _⟩⟩

namespace sheaf

/--
The forgetful functor from sheaves to presheaves.
-/
@[derive [full, faithful]]
def forget : Top.sheaf C X ⥤ Top.presheaf C X :=
Sheaf_to_presheaf _ _

@[simp] lemma id_app (F : sheaf C X) (t) : (𝟙 F : F ⟶ F).1.app t = 𝟙 _ := rfl
@[simp] lemma comp_app {F G H : sheaf C X} (f : F ⟶ G) (g : G ⟶ H) (t) :
  (f ≫ g).1.app t = f.1.app t ≫ g.1.app t := rfl

end sheaf

end Top
