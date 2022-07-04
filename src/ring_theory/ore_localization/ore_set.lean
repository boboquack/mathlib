/-
Copyright (c) 2022 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob von Raumer, Kevin Klinge
-/
import group_theory.subgroup.basic

/-!

# (Right) Ore sets

This defines right Ore sets on arbitrary monoids.

## References

* https://ncatlab.org/nlab/show/Ore+set

-/

namespace ore_localization

section monoid

/-- A submonoid `S` of a monoid `R` is (right) Ore if common factors on the left can be turned
into common factors on the right, and if each pair of `r : R` and `s : S` admits an Ore numerator
`v : R` and an Ore denominator `u : S` such that `r * u = s * v`. -/
class ore_set {R : Type*} [monoid R] (S : submonoid R) :=
  (ore_left_cancel : ∀ (r₁ r₂ : R) (s : S), ↑s * r₁ = s * r₂ → {s' : S // r₁ * s' = r₂ * s'})
  (ore_num : R → S → R)
  (ore_denom : R → S → S)
  (ore_eq : ∀ (r : R) (s : S), r * (ore_denom r s) = s * (ore_num r s))

variables {R : Type*} [monoid R] {S : submonoid R} [ore_set S]

/-- Common factors on the left can be turned into common factors on the right, a weak form of
cancellability. -/
def ore_left_cancel (r₁ r₂ : R) (s : S) (h : ↑s * r₁ = s * r₂) : {s' : S // r₁ * s' = r₂ * s'} :=
ore_set.ore_left_cancel r₁ r₂ s h

/-- The common right factor of an Ore set's weak cancellability property. -/
def ore_left_cancel_factor (r₁ r₂ : R) (s : S) (h : (s : R) * r₁ = s * r₂) : S :=
(ore_left_cancel r₁ r₂ s h).1

/-- The defining equality of an Ore set's weak cancellability. -/
lemma ore_left_cancel_factor_eq (r₁ r₂ : R) (s : S) (h : (s : R) * r₁ = s * r₂) :
  r₁ * (ore_left_cancel_factor r₁ r₂ s h) = r₂ * (ore_left_cancel_factor r₁ r₂ s h) :=
(ore_left_cancel r₁ r₂ s h).2

/-- The Ore numerator of a fraction. -/
def ore_num (r : R) (s : S) : R := ore_set.ore_num r s

/-- The Ore denominator of a fraction. -/
def ore_denom (r : R) (s : S) : S := ore_set.ore_denom r s

/-- The Ore condition of a fraction, expressed in terms of `ore_num` and `ore_denom`. -/
lemma ore_eq (r : R) (s : S) : r * (ore_denom r s) = s * (ore_num r s) := ore_set.ore_eq r s

/-- The Ore condition bundled in a sigma type. This is useful in situations where we want to obtain
both witnesses and the condition for a given fraction. -/
def ore_condition (r : R) (s : S) : Σ' r' : R, Σ' s' : S, r * s' = s * r' :=
⟨ore_num r s, ore_denom r s, ore_eq r s⟩

/-- The trivial submonoid is an Ore set. -/
instance ore_set_bot : ore_set (⊥ : submonoid R) :=
{ ore_left_cancel := λ _ _ s h,
    ⟨1, begin
          rcases s with ⟨s, hs⟩, rw submonoid.mem_bot at hs,subst hs,
          rw [set_like.coe_mk, one_mul, one_mul] at h, subst h
        end⟩,
  ore_num := λ r _, r,
  ore_denom := λ _ _, 1,
  ore_eq := λ _ s, by { rcases s with ⟨s, hs⟩, rw submonoid.mem_bot at hs, simp [hs] } }

/-- Every submonoid of a commutative monoid is an Ore set. -/
def ore_set_comm {R} [comm_monoid R] (S : submonoid R) : ore_set S :=
{ ore_left_cancel := λ m n s h, ⟨s, by rw [mul_comm n s, mul_comm m s, h]⟩,
  ore_num := λ r _, r,
  ore_denom := λ _ s, s,
  ore_eq := λ r s, by rw mul_comm }

attribute [instance, priority 100] ore_set_comm

end monoid

section ring

variables {R : Type*} [ring R] [no_zero_divisors R] {S : submonoid R}

/-- In rings without zero divisors, the first (cancellability) condition is always fulfilled,
it suffices to give a prove for the ore condition itself. -/
def ore_set_of_no_zero_divisors
  (ore_num : R → S → R)
  (ore_denom : R → S → S)
  {ore_eq : ∀ (r : R) (s : S), r * (ore_denom r s) = s * (ore_num r s)} :
  ore_set S :=
{ ore_left_cancel := λ r₁ r₂ s h,
  begin
    cases s with s hs,
    use ⟨s, hs⟩,
    have : s * (r₂ - r₁) = 0,
    { rw [mul_sub], apply sub_eq_zero_of_eq, symmetry, assumption },
    cases eq_zero_or_eq_zero_of_mul_eq_zero this with h0 h0,
    { subst h0, simp },
    { replace h0 := eq_of_sub_eq_zero h0, subst h0 }
  end,
  ore_num := ore_num,
  ore_denom := ore_denom,
  ore_eq := ore_eq }

end ring

end ore_localization
