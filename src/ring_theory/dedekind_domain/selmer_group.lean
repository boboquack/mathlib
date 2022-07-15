/-
Copyright (c) 2022 David Kurniadi Angdinata. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Kurniadi Angdinata
-/

import data.zmod.quotient
import ring_theory.dedekind_domain.adic_valuation
import ring_theory.localization.basic

/-!
# Selmer groups
-/

open_locale classical discrete_valuation non_zero_divisors

universes u v

noncomputable theory

namespace is_dedekind_domain

variables {R : Type u} [comm_ring R] [is_domain R] [is_dedekind_domain R] {K : Type v} [field K]
  [algebra R K] [is_localization R⁰ K] (v : height_one_spectrum R)

local notation K/n := Kˣ ⧸ (pow_monoid_hom n : Kˣ →* Kˣ).range

/-! ### Valuations of non-zero elements -/

namespace height_one_spectrum

/-- The multiplicative `v`-adic valuation on `Kˣ`. -/
def valuation_of_ne_zero_to_fun (x : Kˣ) : multiplicative ℤ :=
let hx := is_localization.sec R⁰ (x : K) in multiplicative.of_add $
  (-(associates.mk v.as_ideal).count (associates.mk $ ideal.span {hx.fst}).factors : ℤ)
  - (-(associates.mk v.as_ideal).count (associates.mk $ ideal.span {(hx.snd : R)}).factors : ℤ)

lemma valuation_of_ne_zero_to_fun_eq (x : Kˣ) :
  (v.valuation_of_ne_zero_to_fun x : ℤₘ₀) = v.valuation (x : K) :=
begin
  change _ = _ * _,
  rw [units.coe_inv],
  change _ = ite _ _ _ * (ite (coe _ = _) _ _)⁻¹,
  rw [is_localization.to_localization_map_sec,
      if_neg $ is_localization.sec_fst_ne_zero le_rfl x.ne_zero,
      if_neg $ non_zero_divisors.coe_ne_zero _],
  any_goals { exact is_domain.to_nontrivial R },
  refl
end

/-- The multiplicative `v`-adic valuation on `Kˣ`. -/
def valuation_of_ne_zero : Kˣ →* multiplicative ℤ :=
{ to_fun   := v.valuation_of_ne_zero_to_fun,
  map_one' := by { rw [← with_zero.coe_inj, valuation_of_ne_zero_to_fun_eq], exact map_one _ },
  map_mul' := λ x y, by { rw [← with_zero.coe_inj, with_zero.coe_mul],
                          simp only [valuation_of_ne_zero_to_fun_eq], exact map_mul _ _ _ } }

lemma valuation_of_ne_zero_eq (x : Kˣ) : (v.valuation_of_ne_zero x : ℤₘ₀) = v.valuation (x : K) :=
valuation_of_ne_zero_to_fun_eq v x

local attribute [semireducible] mul_opposite

/-- The multiplicative `v`-adic valuation on `Kˣ/(Kˣ)ⁿ`. -/
def valuation_of_ne_zero_mod (n : ℕ) : K/n →* multiplicative (zmod n) :=
(int.quotient_zmultiples_nat_equiv_zmod n).to_multiplicative.to_monoid_hom.comp $
  quotient_group.map _ (add_subgroup.zmultiples (n : ℤ)).to_subgroup v.valuation_of_ne_zero
begin
  rintro _ ⟨x, rfl⟩,
  exact ⟨v.valuation_of_ne_zero x, by simpa only [pow_monoid_hom_apply, map_pow, int.to_add_pow]⟩
end

end height_one_spectrum

/-! ### Selmer groups -/

variables {S S' : set $ height_one_spectrum R} {n : ℕ}

/-- The `S`-Selmer group `K(S, n) = {x(Kˣ)ⁿ ∈ Kˣ/(Kˣ)ⁿ | ∀ v ∉ S, ord_v(x) ≡ 0 mod n}`. -/
def selmer_group : subgroup $ K/n :=
{ carrier  := {x : K/n | ∀ v ∉ S, (v : height_one_spectrum R).valuation_of_ne_zero_mod n x = 1},
  one_mem' := λ _ _, by rw [map_one],
  mul_mem' := λ _ _ hx hy v hv, by rw [map_mul, hx v hv, hy v hv, one_mul],
  inv_mem' := λ _ hx v hv, by rw [map_inv, hx v hv, inv_one] }

notation K`⟮`S, n`⟯` := @selmer_group _ _ _ _ K _ _ _ S n

lemma selmer_group.monotone (hS : S ≤ S') : K⟮S, n⟯ ≤ (K⟮S', n⟯) := λ _ hx v, hx v ∘ mt (@hS v)

/-- The multiplicative `v`-adic valuations on `K(S, n)` for all `v ∈ S`. -/
def selmer_group.valuation : K⟮S, n⟯ →* S → multiplicative (zmod n) :=
{ to_fun   := λ x v, (v : height_one_spectrum R).valuation_of_ne_zero_mod n (x : K/n),
  map_one' := funext $ λ v, map_one _,
  map_mul' := λ x y, funext $ λ v, map_mul _ x y }

lemma selmer_group.valuation_ker :
  selmer_group.valuation.ker = (K⟮(∅ : set $ height_one_spectrum R), n⟯).subgroup_of (K⟮S, n⟯) :=
begin
  ext ⟨_, hx⟩,
  split,
  { intros hx' v _,
    by_cases hv : v ∈ S,
    { exact congr_fun hx' ⟨v, hv⟩ },
    { exact hx v hv } },
  { exact λ hx', funext $ λ v, hx' v $ set.not_mem_empty v }
end

end is_dedekind_domain
