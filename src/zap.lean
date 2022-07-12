/-
Copyright (c) 2022 Alex J. Best, X.-F. Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:  Alex J. Best, X-F. Roblot
-/

import number_theory.number_field
import analysis.complex.polynomial

section admit
namespace multiset

variables {R : Type*} [comm_ring R]

/-- import from PR15008 -/
def esymm (s : multiset R) (n : ℕ) : R := ((s.powerset_len n).map multiset.prod).sum

/-- import from PR15008 -/
lemma prod_X_sub_C_coeff (s : multiset R) {k : ℕ} (h : k ≤ s.card):
    polynomial.coeff (s.map (λ r, polynomial.X - polynomial.C r)).prod k =
    (-1)^k * s.esymm (s.card - k) :=
begin
  sorry,
end

end multiset

namespace polynomial

variables {F K : Type*} [field F] [nontrivial K] [normed_field K]

open_locale polynomial
open_locale nnreal

lemma coeff_le_of_roots_le {p : F[X]} {f : F →+* K} {B : ℝ} (i : ℕ)
  (h0 : p.monic) (h1 : 0 ≤ B) (h2 : splits f p) (h3 : ∀ z ∈ (map f p).roots, ∥z∥ ≤ B) :
  ∥ (map f p).coeff i ∥ ≤ B^(p.nat_degree - i) * p.nat_degree.choose i  :=
begin
  have hcd :  multiset.card (map f p).roots = p.nat_degree := (nat_degree_eq_card_roots h2).symm,
  by_cases hi : i ≤ p.nat_degree,
  { rw eq_prod_roots_of_splits h2,
    rw [monic.def.mp h0, ring_hom.map_one, ring_hom.map_one, one_mul],
    rw multiset.prod_X_sub_C_coeff,
    swap, rwa hcd,
    rw [norm_mul, (by norm_num : ∥(-1 : K) ^ i∥=  1), one_mul],
    apply le_trans (multiset.le_sum_of_subadditive norm _ _ _ ),
    rotate, exact norm_zero, exact norm_add_le,
    rw multiset.map_map,
    suffices : ∀ r ∈ multiset.map (norm_hom ∘ multiset.prod)
      (multiset.powerset_len (multiset.card (map f p).roots - i) (map f p).roots),
      r ≤ B^(p.nat_degree - i),
    { convert multiset.sum_le_sum_sum _ this,
      simp only [hi, hcd, multiset.map_const, multiset.card_map, multiset.card_powerset_len,
        nat.choose_symm, multiset.sum_repeat, nsmul_eq_mul, mul_comm], },
    intros r hr,
    obtain ⟨t, ht⟩ := multiset.mem_map.mp hr,
    lift B to ℝ≥0 using h1,
    lift (multiset.map norm_hom t) to (multiset ℝ≥0) with normt,
    swap, { intros x hx,
      obtain ⟨z, hz⟩ := multiset.mem_map.mp hx,
      rw ←hz.right,
      exact norm_nonneg z, },
    suffices : ∀ r ∈ normt, r ≤ B,
    { convert multiset.prod_le_sum_prod _ this using 1,
      { rw_mod_cast [←ht.right, function.comp_apply, ←multiset.prod_hom t norm_hom, ←h], },
      { rw [multiset.map_const, multiset.prod_repeat, nnreal.coe_pow],
        congr,
        have card_eq : _, from congr_arg (λ (t : multiset ℝ), t.card) h,
        rw [multiset.card_map, multiset.card_map] at card_eq,
        rw [card_eq, ←hcd],
        exact (multiset.mem_powerset_len.mp ht.left).right.symm, }},
    intros r hr,
    suffices : ∃ z ∈ t, norm z = r,
    { obtain ⟨z, hzt, hzr⟩ := this,
      have zleB : ∥z∥ ≤ B,
      { exact h3 z (multiset.mem_of_le (multiset.mem_powerset_len.mp ht.left).left hzt) },
      rwa hzr at zleB, },
    have rmem : (r : ℝ) ∈ multiset.map coe normt, from multiset.mem_map_of_mem _ hr,
    rw h at rmem,
    obtain ⟨z, hz⟩ := multiset.mem_map.mp rmem,
    use z, exact hz, },
  { push_neg at hi,
    rw [nat.choose_eq_zero_of_lt hi, coeff_eq_zero_of_nat_degree_lt, norm_zero],
    rw_mod_cast mul_zero,
    { rwa monic.nat_degree_map h0,
      apply_instance, }},
end

end polynomial

end admit

section forward

variables {K : Type*} [monoid K] {n : ℕ} (x : K) (hx : x ^ n = 1) (hn : 0 < n)
variables (φ : K →* ℂ)
include hx hn

open complex

lemma absolute_value_one : abs (φ x) = 1 :=
begin
  have h_pow : (φ x)^n = 1, by simp [←monoid_hom.map_pow, hx, monoid_hom.map_one],
  exact norm_eq_one_of_pow_eq_one h_pow (ne_of_gt hn),
end

end forward

section backwards

open set finite_dimensional complex
open_locale classical
open_locale big_operators
open_locale polynomial

variables {K : Type*} [field K] [number_field K] {n : ℕ} (x : K)
open polynomial

noncomputable theory

/-- TODO. Golf this -/
lemma nat_degree_le_finrank {K : Type*} [field K] [number_field K] {x : K}
  (hxi : is_integral ℤ x) :
  (minpoly ℤ x).nat_degree ≤ finrank ℚ K :=
begin
  rw (_ : (minpoly ℤ x).nat_degree = (minpoly ℚ x).nat_degree),
  rw [← intermediate_field.adjoin.finrank (is_separable.is_integral ℚ x),
    ← intermediate_field.finrank_eq_finrank_subalgebra],
  convert submodule.finrank_le (ℚ⟮x⟯.to_subalgebra.to_submodule : submodule _ _),
  have : minpoly ℚ x = (minpoly ℤ x).map (algebra_map ℤ ℚ),
  from minpoly.gcd_domain_eq_field_fractions' ℚ hxi,
  rw [this, nat_degree_map_eq_of_injective _],
  exact is_fraction_ring.injective ℤ ℚ,
end

local attribute [-instance] complex.algebra

lemma minpoly_coeff_le_of_all_abs_eq_one (hx : x ∈ {x : K | ∀ (φ : K →+* ℂ), abs (φ x) = 1})
  (hxi : is_integral ℤ x) (i : ℕ) :
  |(minpoly ℤ x).coeff i| ≤ ((minpoly ℤ x).nat_degree.choose i) :=
begin
  have hmp : minpoly ℚ x = map (algebra_map ℤ ℚ) (minpoly ℤ x),
    from minpoly.gcd_domain_eq_field_fractions' ℚ hxi,
  have hdg : (minpoly ℚ x).nat_degree = (minpoly ℤ x).nat_degree,
  { rw hmp, convert nat_degree_map_eq_of_injective _ _,
    exact (algebra_map ℤ ℚ).injective_int, },
  have hsp : splits (algebra_map ℚ ℂ) (minpoly ℚ x) :=
    is_alg_closed.splits_codomain (minpoly ℚ x),
  suffices : complex.abs ((map (algebra_map ℚ ℂ) (minpoly ℚ x)).coeff i) ≤
          (minpoly ℤ x).nat_degree.choose i,
  { suffices : (|(minpoly ℤ x).coeff i| : ℝ) ≤ ↑((minpoly ℤ x).nat_degree.choose i),
    { exact_mod_cast this, },
    convert this,
    rw hmp,
    simp only [coeff_map, ring_hom.eq_int_cast, ring_hom.map_int_cast, mem_set_of_eq],
    norm_cast, },
  suffices : ∀ z ∈ (map (algebra_map ℚ ℂ) (minpoly ℚ x)).roots, abs z ≤ 1,
  { convert coeff_le_of_roots_le i _ _ hsp this,
    { simp only [hdg, one_pow, one_mul], },
    { rw hmp, exact monic.map (algebra_map ℤ ℚ) (minpoly.monic hxi), },
    { linarith, }},
  intros z hz,
  suffices : ∃ (φ : K →+* ℂ), φ x = z,
  { obtain ⟨φ, hφ⟩ := this, rw ←hφ, exact le_of_eq (hx φ), },
  rw [←set.mem_range, number_field.embeddings.eq_roots, mem_root_set_iff _, aeval_def],
  rwa mem_roots_map at hz,
  repeat { rw hmp, refine monic.ne_zero _,
    exact monic.map (algebra_map ℤ ℚ) (minpoly.monic hxi), },
  apply_instance,
end

/-- TODO. Golf this -/
lemma finite_all_abs_eq_one : {x : K | is_integral ℤ x ∧ ∀ φ : K →+* ℂ, abs (φ x) = 1}.finite :=
begin
  suffices :
    (⋃ (f : polynomial ℤ)
       (hf : f.nat_degree ≤ finrank ℚ K ∧ ∀ i, |f.coeff i| ≤ f.nat_degree.choose i),
       ((f.map (algebra_map ℤ K)).roots.to_finset : set K)).finite,
  { refine this.subset _,
    intros x hx,
    rw mem_Union,
    use minpoly ℤ x,
    -- TODO. remove this simp
    simp only [exists_prop, mem_Union, multiset.mem_to_finset, finset.mem_coe],
    refine ⟨⟨_, _⟩, _⟩,
    { exact nat_degree_le_finrank hx.1, },
    { exact minpoly_coeff_le_of_all_abs_eq_one x hx.2 hx.1, },
    rw [mem_roots, is_root.def, ←polynomial.eval₂_eq_eval_map, ←aeval_def],
    exact minpoly.aeval ℤ x,
    refine monic.ne_zero _,
    exact monic.map (algebra_map ℤ K) (minpoly.monic hx.left), },
  refine finite.bUnion _ _,
  { have : inj_on (λ g : polynomial ℤ, λ d : fin (finrank ℚ K + 1), g.coeff d)
      { f | f.nat_degree ≤ finrank ℚ K
            ∧ ∀ (i : ℕ), |f.coeff i| ≤ f.nat_degree.choose i },
    { intros x hx y hy he,
      ext,
      by_cases n < finrank ℚ K + 1,
      { simpa using congr_fun he ⟨n, h⟩, },
      rw [coeff_eq_zero_of_nat_degree_lt, coeff_eq_zero_of_nat_degree_lt],
      { rcases hy with ⟨hy_left, hy_right⟩,
        linarith, },
      { rcases hx with ⟨hx_left, hx_right⟩,
        linarith, }, },
    { refine finite.of_finite_image _ this,
      have : (set.pi univ (λ d : fin (finrank ℚ K + 1), Icc (-(finrank ℚ K).choose d : ℤ)
              ((finrank ℚ K).choose d))).finite := finite.pi (λ d, finite_Icc _ _),
      refine finite.subset this _,
      simp only [pi_univ_Icc, image_subset_iff],
      intros f hf,
      simp only [pi_univ_Icc, mem_preimage, mem_Icc, pi.le_def] at *,
      rw ← forall_and_distrib,
      intro x,
      rw mem_def at hf,
      rcases hf with ⟨hf_left, hf_right⟩,
      specialize hf_right x,
      rw abs_le at hf_right,
      suffices : f.nat_degree.choose x ≤ (finrank ℚ K).choose x,
      { split; linarith, },
      apply nat.choose_mono _ hf_left, }, },
  { intros p hp,
    -- few possibilites here
    exact polynomial.root_set_finite p K, },
end

/-- TODO. Golf this -/
-- TODO we don't really need K to be a number field here, more general field extensions are fine
-- as long as we keep the condition that x is integral over ℤ
variables (hx : ∀ φ : K →+* ℂ, abs (φ x) = 1) (hxi : is_integral ℤ x)
include hx hxi
/-- Lemma 1.6 of Washington's Introduction to cyclotomic fields -/
lemma mem_roots_of_unity_of_abs_eq_one : ∃ (n : ℕ) (hn : 0 < n), x ^ n = 1 :=
begin
  obtain ⟨a, -, b, -, habne, h⟩ := @infinite.exists_ne_map_eq_of_maps_to _ _ _ _
      ((^) x : ℕ → K) infinite_univ _ (finite_all_abs_eq_one),
  { replace habne := habne.lt_or_lt,
    wlog : a < b := habne using [a b],
    refine ⟨b - a, tsub_pos_of_lt habne, _⟩,
    have hxne : x ≠ 0,
    { contrapose! hx,
      simp only [hx, complex.abs_zero, ring_hom.map_zero, ne.def, not_false_iff, zero_ne_one],
      use (is_alg_closed.lift (number_field.is_algebraic K)).to_ring_hom },
    rw [pow_sub₀ _ hxne habne.le, h, mul_inv_cancel (pow_ne_zero b hxne)] },
  { rw [set.maps_univ_to],
    exact λ a, ⟨hxi.pow a, λ φ, by simp [hx φ, is_absolute_value.abv_pow complex.abs]⟩ },
end
end backwards
