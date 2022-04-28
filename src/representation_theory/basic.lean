/-
Copyright (c) 2022 Antoine Labelle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Labelle
-/
import algebra.module.basic
import algebra.module.linear_map
import algebra.monoid_algebra.basic
import linear_algebra.trace
import linear_algebra.dual
import linear_algebra.free_module.basic

/-!
# Monoid representations

This file introduces monoid representations and their characters and defines a few ways to construct
representations.

## Main definitions

  * representation.representation
  * representation.character
  * representation.tprod
  * representation.lin_hom
  * represensation.dual

## Implementation notes

Representations of a monoid `G` on a `k`-module `V` are implemented as
homomorphisms `G →* (V →ₗ[k] V)`.
-/

open monoid_algebra (lift) (of)
open linear_map

section
variables (k G V : Type*) [comm_semiring k] [monoid G] [add_comm_monoid V] [module k V]

/--
A representation of `G` on the `k`-module `V` is an homomorphism `G →* (V →ₗ[k] V)`.
-/
abbreviation representation := G →* (V →ₗ[k] V)

end

namespace representation

section trivial

variables {k G V : Type*} [comm_semiring k] [monoid G] [add_comm_monoid V] [module k V]

/--
The trivial representation of `G` on the one-dimensional module `k`.
-/
def trivial : representation k G k := 1

@[simp]
lemma trivial_def (g : G) (v : k) : trivial g v = v := rfl

end trivial

section monoid_algebra

variables {k G V : Type*} [comm_semiring k] [monoid G] [add_comm_monoid V] [module k V]
variables (ρ : representation k G V)

/--
A `k`-linear representation of `G` on `V` can be thought of as
an algebra map from `monoid_algebra k G` into the `k`-linear endomorphisms of `V`.
-/
noncomputable def as_algebra_hom : monoid_algebra k G →ₐ[k] (module.End k V) :=
(lift k G _) ρ

lemma as_algebra_hom_def : as_algebra_hom ρ = (lift k G _) ρ :=
rfl

@[simp]
lemma as_algebra_hom_single (g : G) (r : k) :
  (as_algebra_hom ρ (finsupp.single g r)) = r • ρ g :=
by simp only [as_algebra_hom_def, monoid_algebra.lift_single]

lemma as_algebra_hom_of (g : G) :
  (as_algebra_hom ρ (of k G g)) = ρ g :=
by simp only [monoid_algebra.of_apply, as_algebra_hom_single, one_smul]

/--
If `ρ : representation k G V`, then `ρ.as_module` is a type synonym for `V`,
which we equip with an instance `module (monoid_algebra k G) ρ.as_module`.

The type synonym is irreducible, as you should use `as_module_equiv : ρ.as_module ≃+ V`
to translate terms.
-/
@[nolint unused_arguments, derive add_comm_monoid]
def as_module (ρ : representation k G V) := V

/--
A `k`-linear representation of `G` on `V` can be thought of as
a module over `monoid_algebra k G`.
-/
noncomputable instance XXXXX : module (monoid_algebra k G) ρ.as_module :=
begin
  change module (monoid_algebra k G) V,
  exact module.comp_hom V (as_algebra_hom ρ).to_ring_hom,
end

def as_module_equiv : ρ.as_module ≃+ V :=
add_equiv.refl _

@[simp]
lemma as_module_equiv_map_smul (r : monoid_algebra k G) (x : ρ.as_module) :
  ρ.as_module_equiv (r • x) = ρ.as_algebra_hom r (ρ.as_module_equiv x) :=
rfl

@[simp]
lemma as_module_equiv_symm_map_smul (r : k) (x : V) :
  ρ.as_module_equiv.symm (r • x) = algebra_map k (monoid_algebra k G) r • (ρ.as_module_equiv.symm x) :=
begin
  apply_fun ρ.as_module_equiv,
  simp,
end

@[simp]
lemma as_module_equiv_symm_map_rho (g : G) (x : V) :
  ρ.as_module_equiv.symm (ρ g x) = monoid_algebra.of k G g • (ρ.as_module_equiv.symm x) :=
begin
  apply_fun ρ.as_module_equiv,
  simp,
end

-- Now that we've checked the actions work as expected,
-- we make `as_module` irreducible for the sake of hygiene.
attribute [irreducible] as_module

/--
Build a `representation k G M` from a `[module (monoid_algebra k G) M]`.

This version is unsatisfactory, as it requires an additional
`[is_scalar_tower k (monoid_algebra k G) M]` instance.

We remedy this below in `of_module`
(with the tradeoff that the representation is defined
only on a type synonym of the original module.)
-/
noncomputable
def of_module' (M : Type*) [add_comm_monoid M] [module k M] [module (monoid_algebra k G) M]
  [is_scalar_tower k (monoid_algebra k G) M] : representation k G M :=
(monoid_algebra.lift k G (M →ₗ[k] M)).symm (algebra.lsmul k M)

section
variables (k G) (M : Type*) [add_comm_monoid M] [module (monoid_algebra k G) M]
-- local attribute [irreducible] restrict_scalars

/--
Build a `representation` from a `[module (monoid_algebra k G) M]`.

Note that the representation is built on `restrict_scalars k (monoid_algebra k G) M`,
rather than on `M` itself.
-/
noncomputable
def of_module :
  representation k G (restrict_scalars k (monoid_algebra k G) M) :=
(monoid_algebra.lift k G
  (restrict_scalars k (monoid_algebra k G) M →ₗ[k] restrict_scalars k (monoid_algebra k G) M)).symm
  (restrict_scalars.lsmul k (monoid_algebra k G) M)

example (r : monoid_algebra k G) (m : restrict_scalars k (monoid_algebra k G) M) :
   ((((of_module k G M).as_algebra_hom) r) m) =
    (restrict_scalars.add_equiv _ _ _).symm (r • restrict_scalars.add_equiv _ _ _ m) :=
begin
  apply monoid_algebra.induction_on r,
  { intros g, simp [of_module, restrict_scalars.lsmul_apply_apply], },
  { intros f g fw gw, simp [fw, gw, add_smul], },
  { intros r f w, simp [w], sorry, }
end

/-!
## `of_module` and `as_module` are inverses.

This requires a little care in both directions:
this is a categorical equivalence, not an isomorphism.

Starting with `ρ : representation k G V`, converting to a module and back again
we have a `representation k G (restrict_scalars k (monoid_algebra k G) ρ.as_module)`.
To compare these, we use the composition of `restrict_scalars_add_equiv` and `ρ.as_module_equiv`.

Starting with `module (monoid_algebra k G) M`, after we convert to a representation and back
to a module, we have `module (monoid_algebra k G) (restrict_scalars k (monoid_algebra k G) M)`
--- FIXME continue
-/

lemma of_module_as_module_act (g : G) (x : restrict_scalars k (monoid_algebra k G) ρ.as_module) :
 (ρ.as_module_equiv) ((restrict_scalars.add_equiv _ _ _) (of_module k G (ρ.as_module) g x)) =
     (ρ g (ρ.as_module_equiv (restrict_scalars.add_equiv _ _ _ x))) :=
begin
  apply_fun ρ.as_module_equiv.symm,
  dsimp [of_module, restrict_scalars.lsmul_apply_apply],
  simp,
end.

local attribute [semireducible] restrict_scalars

lemma as_module_of_module_act (r : monoid_algebra k G)
  (m : restrict_scalars k (monoid_algebra k G) M) :
   (restrict_scalars.add_equiv _ _ _) ((of_module k G M).as_module_equiv (r • ((of_module k G M).as_module_equiv.symm m))) =
     r • (restrict_scalars.add_equiv _ _ _) m :=
begin
  dsimp,
  simp only [add_equiv.apply_symm_apply],
  extract_goal,
  apply monoid_algebra.induction_on r, -- what's wrong here?

end

-- reformulation of the above...?
lemma as_module_of_module_act' (r : monoid_algebra k G)
  (m : (of_module k G M).as_module) :
   (restrict_scalars.add_equiv _ _ _) ((of_module k G M).as_module_equiv (r • m)) =
     r • (restrict_scalars.add_equiv _ _ _) ((of_module k G M).as_module_equiv m) :=
begin
  dsimp,
  apply monoid_algebra.induction_on r,
  { intro g, dsimp, simp, sorry, },
  { sorry, },
  { sorry, },
end


end

end monoid_algebra

section add_comm_group

variables {k G V : Type*} [comm_ring k] [monoid G] [add_comm_group V] [module k V]
variables (ρ : representation k G V)

local attribute [semireducible] as_module

instance : add_comm_group ρ.as_module :=
by { change add_comm_group V, apply_instance, }

end add_comm_group

section group

variables {k G V : Type*} [comm_semiring k] [group G] [add_comm_monoid V] [module k V]
variables (ρ : representation k G V)

/--
When `G` is a group, a `k`-linear representation of `G` on `V` can be thought of as
a group homomorphism from `G` into the invertible `k`-linear endomorphisms of `V`.
-/
def as_group_hom : G →* units (V →ₗ[k] V) :=
monoid_hom.to_hom_units ρ

lemma as_group_hom_apply (g : G) : ↑(as_group_hom ρ g) = ρ g :=
by simp only [as_group_hom, monoid_hom.coe_to_hom_units]

end group

section character

variables {k G V : Type*} [comm_ring k] [group G] [add_comm_group V] [module k V]
variables (ρ : representation k G V)

/--
The character associated to a representation of `G`, which as a map `G → k`
sends each element to the trace of the corresponding linear map.
-/
@[simp]
noncomputable def character (g : G) : k := trace k V (ρ g)

theorem char_mul_comm (g : G) (h : G) : character ρ (h * g) = character ρ (g * h) :=
by simp only [trace_mul_comm, character, map_mul]

/-- The character of a representation is constant on conjugacy classes. -/
theorem char_conj (g : G) (h : G) : (character ρ) (h * g * h⁻¹) = (character ρ) g :=
by simp only [character, ←as_group_hom_apply, map_mul, map_inv, trace_conj]

variables [nontrivial k] [module.free k V] [module.finite k V]

/-- The evaluation of the character at the identity is the dimension of the representation. -/
theorem char_one : character ρ 1 = finite_dimensional.finrank k V :=
by simp only [character, map_one, trace_one]

end character

section tensor_product

variables {k G V W : Type*} [comm_semiring k] [monoid G]
variables [add_comm_monoid V] [module k V] [add_comm_monoid W] [module k W]
variables (ρV : representation k G V) (ρW : representation k G W)

open_locale tensor_product

/--
Given representations of `G` on `V` and `W`, there is a natural representation of `G` on their
tensor product `V ⊗[k] W`.
-/
def tprod : representation k G (V ⊗[k] W) :=
{ to_fun := λ g, tensor_product.map (ρV g) (ρW g),
  map_one' := by simp only [map_one, tensor_product.map_one],
  map_mul' := λ g h, by simp only [map_mul, tensor_product.map_mul] }

notation ρV ` ⊗ ` ρW := tprod ρV ρW

@[simp]
lemma tprod_apply (g : G) : (ρV ⊗ ρW) g = tensor_product.map (ρV g) (ρW g) := rfl

end tensor_product

section linear_hom

variables {k G V W : Type*} [comm_semiring k] [group G]
variables [add_comm_monoid V] [module k V] [add_comm_monoid W] [module k W]
variables (ρV : representation k G V) (ρW : representation k G W)

/--
Given representations of `G` on `V` and `W`, there is a natural representation of `G` on the
module `V →ₗ[k] W`, where `G` acts by conjugation.
-/
def lin_hom : representation k G (V →ₗ[k] W) :=
{ to_fun := λ g,
  { to_fun := λ f, (ρW g) ∘ₗ f ∘ₗ (ρV g⁻¹),
    map_add' := λ f₁ f₂, by simp_rw [add_comp, comp_add],
    map_smul' := λ r f, by simp_rw [ring_hom.id_apply, smul_comp, comp_smul]},
  map_one' := linear_map.ext $ λ x,
    by simp_rw [coe_mk, one_inv, map_one, one_apply, one_eq_id, comp_id, id_comp],
  map_mul' := λ g h,  linear_map.ext $ λ x,
    by simp_rw [coe_mul, coe_mk, function.comp_apply, mul_inv_rev, map_mul, mul_eq_comp,
                comp_assoc ]}

@[simp]
lemma lin_hom_apply (g : G) (f : V →ₗ[k] W) : (lin_hom ρV ρW) g f = (ρW g) ∘ₗ f ∘ₗ (ρV g⁻¹) := rfl

/--
The dual of a representation `ρ` of `G` on a module `V`, given by `(dual ρ) g f = f ∘ₗ (ρ g⁻¹)`,
where `f : module.dual k V`.
-/
def dual : representation k G (module.dual k V) :=
{ to_fun := λ g,
  { to_fun := λ f, f ∘ₗ (ρV g⁻¹),
    map_add' := λ f₁ f₂, by simp only [add_comp],
    map_smul' := λ r f,
      by {ext, simp only [coe_comp, function.comp_app, smul_apply, ring_hom.id_apply]} },
  map_one' :=
    by {ext, simp only [coe_comp, function.comp_app, map_one, one_inv, coe_mk, one_apply]},
  map_mul' := λ g h,
    by {ext, simp only [coe_comp, function.comp_app, mul_inv_rev, map_mul, coe_mk, mul_apply]}}

@[simp]
lemma dual_apply (g : G) (f : module.dual k V) : (dual ρV) g f = f ∘ₗ (ρV g⁻¹) := rfl

end linear_hom

end representation
