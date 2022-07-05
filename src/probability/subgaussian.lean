/-
Copyright (c) 2022 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/

import probability.moments

/-! # Sub-Gaussian random variables -/

open measure_theory filter finset

noncomputable theory

open_locale big_operators measure_theory probability_theory ennreal nnreal

namespace probability_theory

variables {Ω : Type*} {m : measurable_space Ω} {X : Ω → ℝ} {μ : measure Ω} {t c ε : ℝ}

include m

def subgaussian_with (X : Ω → ℝ) (μ : measure Ω) (c : ℝ) : Prop :=
∀ t, integrable (λ ω, real.exp (t * X ω)) μ ∧ cgf X μ t ≤ c * t^2 / 2

lemma subgaussian_with.cgf_le (h : subgaussian_with X μ c) (t : ℝ) : cgf X μ t ≤ c * t^2 / 2 :=
(h t).2

lemma subgaussian_with.integrable_exp_mul (h : subgaussian_with X μ c) (t : ℝ) :
  integrable (λ ω, real.exp (t * X ω)) μ := (h t).1

lemma subgaussian_with.mgf_le (h : subgaussian_with X μ c) (t : ℝ) :
  mgf X μ t ≤ real.exp (c * t^2 / 2) :=
calc mgf X μ t ≤ real.exp (cgf X μ t) : real.le_exp_log
... ≤ real.exp (c * t^2 / 2) : real.exp_monotone (h.cgf_le t)

lemma subgaussian_with_zero [is_probability_measure μ] (hc : 0 ≤ c) : subgaussian_with 0 μ c :=
begin
  refine λ t, ⟨_, _⟩,
  { simp only [pi.zero_apply, mul_zero, real.exp_zero],
    exact integrable_const _, },
  { simp only [cgf_zero_fun, measure_univ, ennreal.one_to_real, real.log_one],
    exact div_nonneg (mul_nonneg hc (sq_nonneg _)) zero_le_two, },
end

lemma subgaussian_with.neg (h : subgaussian_with X μ c) :
  subgaussian_with (-X) μ c :=
begin
  refine λ t, ⟨_, _⟩,
  { simp_rw [pi.neg_apply, mul_neg, ← neg_mul],
    exact (h (-t)).1, },
  { rw cgf_neg,
    refine (h.cgf_le (-t)).trans _,
    rw neg_pow_two, },
end

lemma subgaussian_with.add_indep_fun {Y : Ω → ℝ} {cX cY : ℝ} (hX : subgaussian_with X μ cX)
  (hY : subgaussian_with Y μ cY) (hindep : indep_fun X Y μ) :
  subgaussian_with (X + Y) μ (cX + cY) :=
begin
  intros t,
  refine ⟨hindep.integrable_exp_mul_add (hX.integrable_exp_mul t) (hY.integrable_exp_mul t), _⟩,
  rw hindep.cgf_add (hX.integrable_exp_mul t) (hY.integrable_exp_mul t),
  calc cgf X μ t + cgf Y μ t
      ≤ cX * t ^ 2 / 2 + cY * t ^ 2 / 2 : add_le_add (hX.cgf_le t) (hY.cgf_le t)
  ... = (cX + cY) * t ^ 2 / 2 : by ring,
end

lemma Indep_fun.subgaussian_with_sum {ι : Type*} [is_probability_measure μ]
  {X : ι → Ω → ℝ} (h_indep : Indep_fun (λ i, infer_instance) X μ) {c : ι → ℝ}
  {s : finset ι} (h_subg : ∀ i ∈ s, subgaussian_with (X i) μ (c i)) :
  subgaussian_with (∑ i in s, X i) μ (∑ i in s, c i) :=
begin
  refine λ t, ⟨h_indep.integrable_exp_mul_sum (λ i hi, (h_subg i hi).integrable_exp_mul t), _⟩,
  rw [h_indep.cgf_sum (λ i hi, (h_subg i hi).integrable_exp_mul t), sum_mul, sum_div],
  exact sum_le_sum (λ i hi, (h_subg i hi).cgf_le t),
end

lemma subgaussian_with.chernoff_bound [is_finite_measure μ] (hε : 0 ≤ ε)
  (h : subgaussian_with X μ c) (hc : 0 < c) :
  (μ {ω | ε ≤ X ω}).to_real ≤ real.exp(- ε^2 / (2*c)) :=
begin
  have h_le_t : ∀ t : ℝ, 0 ≤ t → (μ {ω | ε ≤ X ω}).to_real ≤ real.exp(- t * ε + c * t^2 / 2),
  { refine λ t ht, (chernoff_bound_cgf ε ht (h.integrable_exp_mul t)).trans _,
    exact real.exp_monotone (add_le_add le_rfl (h.cgf_le t)), },
  refine (h_le_t (ε / c) (div_nonneg hε hc.le)).trans_eq _,
  congr,
  rw [div_pow, pow_two c, mul_div, mul_div_mul_comm, div_self hc.ne', one_mul, neg_mul,
    div_mul_eq_mul_div, ← pow_two, mul_comm, ← div_div],
  ring,
end

lemma Indep_fun.chernoff_sum {ι : Type*} [is_probability_measure μ] (hε : 0 ≤ ε)
  {X : ι → Ω → ℝ} (h_indep : Indep_fun (λ i, infer_instance) X μ) {c : ι → ℝ}
  {s : finset ι} (hs : s.nonempty) (h_subg : ∀ i ∈ s, subgaussian_with (X i) μ (c i))
  (hc : ∀ i ∈ s, 0 < c i) :
  (μ {ω | ε ≤ ∑ i in s, X i ω}).to_real ≤ real.exp(- ε^2 / (2 * (∑ i in s, c i))) :=
begin
  simp_rw ← finset.sum_apply,
  exact (h_indep.subgaussian_with_sum h_subg).chernoff_bound hε (finset.sum_pos hc hs),
end

lemma Indep_fun.chernoff_sum_same {ι : Type*} [is_probability_measure μ] (hε : 0 ≤ ε)
  {X : ι → Ω → ℝ} (h_indep : Indep_fun (λ i, infer_instance) X μ)
  {s : finset ι} (hs : s.nonempty) (h_subg : ∀ i ∈ s, subgaussian_with (X i) μ c)
  (hc : 0 < c) :
  (μ {ω | ε ≤ ∑ i in s, X i ω}).to_real ≤ real.exp(- ε^2 / (2 * c * (card s))) :=
calc (μ {ω | ε ≤ ∑ i in s, X i ω}).to_real
    ≤ real.exp(- ε^2 / (2 * (∑ i in s, c))) : h_indep.chernoff_sum hε hs h_subg (λ _ _, hc)
... = real.exp(- ε^2 / (2 * c * (card s))) :
    by { rw mul_assoc, congr, rw [sum_const, nsmul_eq_mul, mul_comm c], }

lemma Indep_fun.chernoff_sum_range [is_probability_measure μ] (hε : 0 ≤ ε)
  {X : ℕ → Ω → ℝ} (h_indep : Indep_fun (λ i, infer_instance) X μ)
  (h_subg : ∀ i, subgaussian_with (X i) μ c) {n : ℕ} (hn : 1 ≤ n) (hc : 0 < c) :
  (μ {ω | ε ≤ ∑ i in finset.range n, X i ω}).to_real ≤ real.exp(- ε^2 / (2 * c * n)) :=
calc (μ {ω | ε ≤ ∑ i in finset.range n, X i ω}).to_real
    ≤ real.exp(- ε^2 / (2 * c * (card (finset.range n)))) : h_indep.chernoff_sum_same hε
        ⟨0, finset.mem_range.mpr (zero_lt_one.trans_le hn)⟩ (λ i _, h_subg i) hc
... = real.exp(- ε^2 / (2 * c * n)) : by rw card_range


end probability_theory
