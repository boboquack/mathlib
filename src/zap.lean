/-
Copyright (c) 2022 Alex J. Best, X.-F. Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:  Alex J. Best, X-F. Roblot
-/

import number_theory.number_field
import analysis.complex.polynomial

section admit

variables {R : Type*} [comm_ring R]
variables {F K : Type*} [field F] [nontrivial K] [normed_field K]

open_locale polynomial

/-- import from #15008 -/
def multiset.esymm (s : multiset R) (n : ℕ) : R := ((s.powerset_len n).map multiset.prod).sum

/-- import from #15008 -/
lemma multiset.prod_X_sub_C_coeff (s : multiset R) {k : ℕ} (h : k ≤ s.card):
    polynomial.coeff (s.map (λ r, polynomial.X - polynomial.C r)).prod k =
    (-1)^k * s.esymm (s.card - k) :=
begin
  sorry,
end

/-- import from #15275 -/
lemma polynomial.coeff_le_of_roots_le {p : F[X]} {f : F →+* K} {B : ℝ} (i : ℕ)
  (h1 : p.monic) (h2 : polynomial.splits f p) (h3 : ∀ z ∈ (polynomial.map f p).roots, ∥z∥ ≤ B) :
  ∥ (polynomial.map f p).coeff i ∥ ≤ B^(p.nat_degree - i) * p.nat_degree.choose i  :=
begin
  sorry,
end

end admit

section forward

open complex

variables {K : Type*} [monoid K] {n : ℕ} (x : K)

lemma absolute_value_one  (φ : K →* ℂ) (hx : x ^ n = 1) (hn : 0 < n) : abs (φ x) = 1 :=
begin
  have h_pow : (φ x)^n = 1, by simp [←monoid_hom.map_pow, hx, monoid_hom.map_one],
  exact norm_eq_one_of_pow_eq_one h_pow (ne_of_gt hn),
end

end forward

section backwards

-- variables {K : Type*} [field K] [number_field K] {n : ℕ} (x : K)

open polynomial

open set finite_dimensional complex
open_locale classical big_operators

noncomputable theory

variables {K : Type*} [field K] [number_field K] {x : K}

/-- TODO: Put that in FLT also -/
lemma nat_degree_le_finrank
  (hxi : is_integral ℤ x) :
  (minpoly ℤ x).nat_degree ≤ finrank ℚ K :=
begin
  rw (_ : (minpoly ℤ x).nat_degree = (minpoly ℚ x).nat_degree),
  { rw [← intermediate_field.adjoin.finrank (is_separable.is_integral ℚ x),
      ← intermediate_field.finrank_eq_finrank_subalgebra],
    convert submodule.finrank_le (ℚ⟮x⟯.to_subalgebra.to_submodule : submodule _ _), },
  { rw (_ : minpoly ℚ x = (minpoly ℤ x).map (algebra_map ℤ ℚ)),
    exact (monic.nat_degree_map (minpoly.monic hxi) _).symm,
    exact minpoly.gcd_domain_eq_field_fractions' ℚ hxi, }
end

local attribute [-instance] complex.algebra

lemma minpoly_coeff_le_of_all_abs_le {B : ℝ}
  (hxi : is_integral ℤ x) (hx : x ∈ {x : K | ∀ (φ : K →+* ℂ), abs (φ x) ≤ B})  (i : ℕ) :
  (|(minpoly ℤ x).coeff i| : ℝ) ≤ B^((minpoly ℤ x).nat_degree - i)
    * ((minpoly ℤ x).nat_degree.choose i) :=
begin
  have hmp : minpoly ℚ x = map (algebra_map ℤ ℚ) (minpoly ℤ x),
    from minpoly.gcd_domain_eq_field_fractions' ℚ hxi,
  have hdg : (minpoly ℚ x).nat_degree = (minpoly ℤ x).nat_degree,
  { rw hmp, convert nat_degree_map_eq_of_injective _ _,
    exact (algebra_map ℤ ℚ).injective_int, },
  have hsp : splits (algebra_map ℚ ℂ) (minpoly ℚ x) :=
    is_alg_closed.splits_codomain (minpoly ℚ x),
  suffices : complex.abs ((map (algebra_map ℚ ℂ) (minpoly ℚ x)).coeff i) ≤
          B^((minpoly ℤ x).nat_degree - i) * (minpoly ℤ x).nat_degree.choose i,
  { convert this,
    rw hmp,
    simp only [coeff_map, ring_hom.eq_int_cast, ring_hom.map_int_cast, mem_set_of_eq],
    norm_cast, },
  suffices : ∀ z ∈ (map (algebra_map ℚ ℂ) (minpoly ℚ x)).roots, abs z ≤ B,
  { convert coeff_le_of_roots_le i _ hsp this using 1,
    { simp only [hdg, one_pow, one_mul], },
    { rw hmp, exact monic.map (algebra_map ℤ ℚ) (minpoly.monic hxi), }},
  intros z hz,
  suffices : ∃ (φ : K →+* ℂ), φ x = z,
  { obtain ⟨φ, hφ⟩ := this, rw ←hφ, exact (hx φ), },
  rw [←set.mem_range, number_field.embeddings.eq_roots, mem_root_set_iff _, aeval_def],
  rwa mem_roots_map at hz,
  repeat { rw hmp, refine monic.ne_zero _,
    exact monic.map (algebra_map ℤ ℚ) (minpoly.monic hxi), },
  apply_instance,
end

lemma finite_all_abs_le {B : ℝ} (hB : 1 ≤ B) :
  {x : K | is_integral ℤ x ∧ ∀ φ : K →+* ℂ, abs (φ x) ≤ B}.finite :=
begin
  let C := nat.ceil (B ^ finrank ℚ K) * (finrank ℚ K).choose ((finrank ℚ K)/2),
  suffices :
    (⋃ (f : polynomial ℤ)
       (hf : f.nat_degree ≤ finrank ℚ K ∧ ∀ i, |f.coeff i| ≤ C),
       ((f.map (algebra_map ℤ K)).roots.to_finset : set K)).finite,
  { refine this.subset _,
    intros x hx,
    rw mem_Union,
    use minpoly ℤ x,
    rw [mem_Union, exists_prop, finset.mem_coe, multiset.mem_to_finset],
    refine ⟨⟨_, _⟩, _⟩,
    { exact nat_degree_le_finrank hx.1, },
    { intro i,
      suffices : B ^ ((minpoly ℤ x).nat_degree - i) * ((minpoly ℤ x).nat_degree.choose i) ≤ C,
      { exact_mod_cast le_trans (minpoly_coeff_le_of_all_abs_le hx.left hx.right i) this, },
      calc
        B ^ ((minpoly ℤ x).nat_degree - i) * ((minpoly ℤ x).nat_degree.choose i) ≤
              B ^ (minpoly ℤ x).nat_degree * ((minpoly ℤ x).nat_degree.choose i)
                : mul_le_mul_of_nonneg_right (pow_le_pow hB (nat.sub_le _ _)) _
        ... ≤ B ^ (finrank ℚ K) * ((minpoly ℤ x).nat_degree.choose i)
                : mul_le_mul_of_nonneg_right (pow_le_pow hB _ ) _
        ... ≤ nat.ceil(B ^ finrank ℚ K) * ((minpoly ℤ x).nat_degree.choose i)
                : mul_le_mul_of_nonneg_right (nat.le_ceil _ ) _
        ... ≤ nat.ceil(B ^ finrank ℚ K) * ((finrank ℚ K).choose i)
                : mul_le_mul_of_nonneg_left _ _
        ... ≤ nat.ceil(B ^ finrank ℚ K) * (finrank ℚ K).choose ((finrank ℚ K)/2)
                : mul_le_mul_of_nonneg_left
                   (nat.cast_le.mpr (nat.choose_le_middle i (finrank ℚ K))) _
        ... = C : by norm_cast,
      any_goals { exact nat.cast_nonneg _ },
      any_goals { exact_mod_cast nat.choose_mono _ _ },
      any_goals { exact nat_degree_le_finrank hx.1 }},
    { rw [mem_roots, is_root.def, ←polynomial.eval₂_eq_eval_map, ←aeval_def],
      { exact minpoly.aeval ℤ x, },
      { exact monic.ne_zero (monic.map (algebra_map ℤ K) (minpoly.monic hx.left)), }}},
  refine finite.bUnion _ _,
  { suffices : inj_on (λ g : polynomial ℤ, λ d : fin (finrank ℚ K + 1), g.coeff d)
      { f | f.nat_degree ≤ finrank ℚ K ∧ ∀ (i : ℕ), |f.coeff i| ≤ C},
    { refine finite.of_finite_image _ this,
      have hfin : (set.pi univ (λ d : fin (finrank ℚ K + 1), Icc (- C : ℤ) C )).finite
        := finite.pi (λ d, finite_Icc _ _),
      refine finite.subset hfin _,
      rw [pi_univ_Icc, image_subset_iff],
      intros f hf,
      rw [mem_preimage, mem_Icc, pi.le_def, pi.le_def, forall_and_distrib.symm],
      exact λ i, abs_le.mp (hf.right i), },
    intros x hx y hy he,
    ext,
    by_cases n < finrank ℚ K + 1,
    { simpa using congr_fun he ⟨n, h⟩, },
    { rw [coeff_eq_zero_of_nat_degree_lt, coeff_eq_zero_of_nat_degree_lt],
      { rcases hy with ⟨hy_left, hy_right⟩, linarith, },
      { rcases hx with ⟨hx_left, hx_right⟩, linarith, }}},
  { exact λ p _, polynomial.root_set_finite p K, },
end

/-- Lemma 1.6 of Washington's Introduction to cyclotomic fields -/
lemma mem_roots_of_unity_of_abs_le_one
  (hxi : is_integral ℤ x)  (hx : ∀ φ : K →+* ℂ, abs (φ x) = 1) :
  ∃ (n : ℕ) (hn : 0 < n), x ^ n = 1 :=
begin
  obtain ⟨a, -, b, -, habne, h⟩ := @infinite.exists_ne_map_eq_of_maps_to _ _ _ _
    ((^) x : ℕ → K) infinite_univ _ (finite_all_abs_le (le_refl 1)),
  { replace habne := habne.lt_or_lt,
    wlog : a < b := habne using [a b],
    refine ⟨b - a, tsub_pos_of_lt habne, _⟩,
    have hxne : x ≠ 0,
    { contrapose! hx,
      simp only [hx, complex.abs_zero, ring_hom.map_zero, ne.def, not_false_iff, zero_ne_one],
      use (is_alg_closed.lift (number_field.is_algebraic K)).to_ring_hom },
    rw [pow_sub₀ _ hxne habne.le, h, mul_inv_cancel (pow_ne_zero b hxne)], },
  { rw set.maps_univ_to,
    refine λ a, ⟨hxi.pow a, λ φ, by simp [hx φ, complex.abs_pow, one_pow]⟩, },
end

end backwards
