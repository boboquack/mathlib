/-
Copyright (c) 2022 Kevin H. Wilson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin H. Wilson
-/
import algebra.group.basic
import analysis.calculus.mean_value
import analysis.normed_space.is_R_or_C

/-!
# Swapping limits and derivatives via uniform convergence

The purpose of this file is to prove that the derivative of the pointwise limit of a sequence of
functions is the pointwise limit of the functions' derivatives when the derivatives converge
_uniformly_. The formal statement appears as `has_fderiv_at_of_tendsto_uniformly_on`.

## Main statements

* `has_fderiv_at_of_tendsto_uniformly_on` : If `f : ℕ → E → G` is a sequence of functions with
  derivatives `f' : ℕ → (E → (E →L[𝕜] G))` and the `f` converge pointwise to `g` and the `f'`
  converge _uniformly_ on some closed ball, then the derivative of `g'` is the pointwise limit
  of the `f'` on the closed ball

## Implementation notes

The primary components of the proof are the mean value theorem (in the guise of
`convex.norm_image_sub_le_of_norm_has_fderiv_within_le`) and then various lemmas about manipulating
uniform Cauchy sequences.

## Tags

uniform convergence, limits of derivatives
-/

section filter_curry

variables {α β γ : Type*}

def filter.curry (f : filter α) (g : filter β) : filter (α × β) :=
{ sets := { s | ∀ᶠ (a : α) in f, ∀ᶠ (b : β) in g, (a, b) ∈ s},
  univ_sets := (by simp only [set.mem_set_of_eq, set.mem_univ, filter.eventually_true]),
  sets_of_superset := begin
    intros x y hx hxy,
    simp only [set.mem_set_of_eq] at hx ⊢,
    apply hx.mono,
    intros a ha,
    apply ha.mono,
    intros b hb,
    calc (a, b) ∈ x : hb ... ⊆ y : hxy,
  end,
  inter_sets := begin
    intros x y hx hy,
    simp only [set.mem_set_of_eq, set.mem_inter_eq] at hx hy ⊢,
    apply (hx.and hy).mono,
    intros a ha,
    apply (ha.1.and ha.2).mono,
    intros b hb,
    exact hb,
  end,
}

lemma filter.eventually_curry_iff {f : filter α} {g : filter β} {p : α × β → Prop} :
  (∀ᶠ (x : α × β) in f.curry g, p x) ↔ ∀ᶠ (x : α) in f, ∀ᶠ (y : β) in g, p (x, y) :=
begin
  simp only [filter.curry],
  rw filter.eventually_iff,
  simp,
end

lemma filter.curry_le_prod {f : filter α} {g : filter β} :
  f.curry g ≤ f.prod g :=
begin
  intros u hu,
  rw ←filter.eventually_mem_set at hu ⊢,
  rw filter.eventually_curry_iff,
  exact hu.curry,
end

lemma filter.tendsto.curry {f : α → β → γ} {la : filter α} {lb : filter β} {lc : filter γ} :
  (∀ᶠ a in la, filter.tendsto (λ b : β, f a b) lb lc) → filter.tendsto ↿f (la.curry lb) lc :=
begin
  intros h,
  rw filter.tendsto_def,
  simp [filter.curry],
  simp_rw filter.tendsto_def at h,
  intros s hs,
  apply h.mono,
  intros a ha,
  specialize ha s hs,
  rw filter.eventually_iff,
  have : ∀ x : β, ↿f (a, x) = f a x, { intros x, simp [function.has_uncurry.uncurry], },
  simp_rw this,
  have : {x : β | f a x ∈ s} = f a ⁻¹' s, {
    ext,
    simp,
  },
  rw this,
  exact ha,
end

open filter
open_locale filter
lemma bah {f : filter α} {f' : filter β} {g : filter γ} {p : (α × β) × γ × γ → Prop} :
  (∀ᶠ x in (f ×ᶠ f' ×ᶠ (g ×ᶠ g)), p x) → (∀ᶠ (x : (α × β) × γ) in (f ×ᶠ f' ×ᶠ g), p ((x.1.1, x.1.2), x.2, x.2)) :=
begin
  intros h,
  obtain ⟨t, ht, s, hs, hst⟩ := eventually_prod_iff.1 h,
  apply (ht.prod_mk hs.diag_of_prod).mono,
  intros x hx,
  simp only [hst hx.1 hx.2, prod.mk.eta],
end

end filter_curry

open filter
open_locale uniformity filter topological_space

section limits_of_derivatives

variables {E : Type*} [normed_group E] [normed_space ℝ E]
  {𝕜 : Type*} [is_R_or_C 𝕜] [normed_space 𝕜 E]
  {G : Type*} [normed_group G] [normed_space 𝕜 G]
  {f : ℕ → E → G} {g : E → G} {f' : ℕ → (E → (E →L[𝕜] G))} {g' : E → (E →L[𝕜] G)}
  {s : set E} {x : E} {C : ℝ}

/-- If `f_n → g` pointwise and the derivatives `(f_n)' → h` _uniformly_ converge, then
in fact for a fixed `y`, the difference quotients `∥z - y∥⁻¹ • (f_n z - f_n y)` converge
_uniformly_ to `∥z - y∥⁻¹ • (g z - g y)` -/
lemma difference_quotients_converge_uniformly
  (hf : ∀ᶠ (n : ℕ × E) in (at_top ×ᶠ 𝓝 x), has_fderiv_at (f n.fst) (f' n.fst n.snd) n.snd)
  (hfg : ∀ᶠ (y : E) in 𝓝 x, tendsto (λ n, f n y) at_top (𝓝 (g y)))
  (hfg' : tendsto (λ n : ℕ × E, f' n.fst n.snd - g' n.snd) (at_top ×ᶠ 𝓝 x) (𝓝 0)) :
  tendsto (λ n : ℕ × E, (∥n.snd - x∥⁻¹ : 𝕜) • ((g n.snd) - (g x) - ((f n.fst n.snd) - (f n.fst x)))) (at_top ×ᶠ 𝓝 x) (𝓝 0) :=
begin
  suffices : tendsto (λ n : ℕ × ℕ × E, (∥n.2.2 - x∥⁻¹ : 𝕜) • ((f n.1 - f n.2.1) n.2.2 - (f n.1 - f n.2.1) x)) (at_top ×ᶠ (at_top ×ᶠ 𝓝 x)) (𝓝 0),
  {
    sorry,
  },
  have hfg'' : tendsto (λ n : (ℕ × ℕ) × E, f' n.fst.fst n.snd - f' n.fst.snd n.snd) (at_top ×ᶠ at_top ×ᶠ 𝓝 x) (𝓝 0), sorry,
  have := tendsto_swap4_prod.eventually (hf.prod_mk hf),
  have := tendsto_prod_assoc_symm.eventually (bah this),
  simp_rw [metric.tendsto_nhds, dist_eq_norm, sub_zero] at hfg'' ⊢,
  intros ε hε,
  obtain ⟨q, hqpos, hqε⟩ := exists_pos_rat_lt hε,
  have hold := (hfg'' (q : ℝ) (by simp [hqpos])),
  have hold := tendsto_prod_assoc_symm.eventually hold,
  have hold := hold.and this,
  -- simp only [equiv.prod_assoc_symm_apply] at hold,
  obtain ⟨a, b, c, d, e⟩ := eventually_prod_iff.1 hold,
  obtain ⟨a', b', c', d', e'⟩ := eventually_prod_iff.1 d,
  obtain ⟨r, hr, hr'⟩ := metric.nhds_basis_ball.eventually_iff.mp d',
  rw eventually_prod_iff,
  use [a, b, (λ n : ℕ × E, a' n.fst ∧ metric.ball x r n.snd)],
  split,
  sorry,
  intros n hn n' hn',

  rw [norm_smul, norm_inv, is_R_or_C.norm_coe_norm],
  refine lt_of_le_of_lt _ hqε,
  by_cases hyz' : x = n'.snd, { simp [hyz', hqpos.le], },
  have hyz : 0 < ∥n'.snd - x∥,
  {rw norm_pos_iff, intros hy', exact hyz' (eq_of_sub_eq_zero hy').symm, },
  rw [inv_mul_le_iff hyz, mul_comm],

  refine convex.norm_image_sub_le_of_norm_has_fderiv_within_le
    (λ y hy, ((e hn (e' hn'.1 (hr' hy))).2.1.sub (e hn (e' hn'.1 (hr' hy))).2.2).has_fderiv_within_at)
    (λ y hy, (e hn (e' hn'.1 (hr' hy))).1.le)
    (convex_ball x r) (metric.mem_ball_self hr) hn'.2,

end

/-- (d/dx) lim_{n → ∞} f_n x = lim_{n → ∞} f'_n x on a closed ball when the f'_n
converge _uniformly_ to their limit.

In words the assumptions mean the following:
  * `hf`: There is a neighborhood of `x` such that for all sufficiently large `n`, `f' n` is the
    derivative of `f n` **and** for all sufficiently large `N`, there is a neighborhood of `x`
    such that for all `n ≥ N`, `f' n` is the derivative of `f n`
  * `hfg`: The `f n` converge pointwise to `g` on a neighborhood of `x`
  * `hfg'`: The `f'` converge "uniformly at" `x` to `g'`. This does not mean that the `f' n` even
    converge away from `x`! --/
lemma has_fderiv_at_of_tendsto_uniformly_on
  (hf : ∀ᶠ (n : ℕ × E) in (at_top ×ᶠ 𝓝 x), has_fderiv_at (f n.fst) (f' n.fst n.snd) n.snd)
  (hfg : ∀ᶠ y in 𝓝 x, tendsto (λ n, f n y) at_top (𝓝 (g y)))
  (hfg' : tendsto (λ n : ℕ × E, f' n.fst n.snd - g' n.snd) (at_top ×ᶠ 𝓝 x) (𝓝 0)) :
  has_fderiv_at g (g' x) x :=
begin
  -- The proof strategy follows several steps:
  --   1. The quantifiers in the definition of the derivative are
  --      `∀ ε > 0, ∃δ > 0, ∀y ∈ B_δ(x)`. We will introduce a quantifier in the middle:
  --      `∀ ε > 0, ∃N, ∀n ≥ N, ∃δ > 0, ∀y ∈ B_δ(x)` which will allow us to introduce the `f(') n`
  --   2. The order of the quantifiers `hfg` are opposite to what we need. We will be able to swap
  --      the quantifiers using the uniform convergence assumption
  rw has_fderiv_at_iff_tendsto,

  -- To prove that ∀ε > 0, ∃δ > 0, ∀y ∈ B_δ(x), we will need to introduce a quantifier:
  -- ∀ε > 0, ∃N, ∀ n ≥ N, ∃δ > 0, ∀y ∈ B_δ(x). This is done by inserting the `curried` filter
  suffices : tendsto (λ (y : ℕ × E), ∥y.snd - x∥⁻¹ * ∥g y.snd - g x - (g' x) (y.snd - x)∥) (at_top.curry (𝓝 x)) (𝓝 0), {
    -- NOTE (khw): This is a more generic fact, but is easier for now to prove in the metric case
    rw metric.tendsto_nhds at this ⊢,
    intros ε hε,
    specialize this ε hε,
    rw eventually_curry_iff at this,
    simp only at this,
    rw eventually_const at this,
    apply this.mono,
    simp,
  },

  -- With the new quantifier in hand, we can perform the famous `ε/3` proof. Specifically,
  -- we will break up the limit (the difference functions minus the derivative go to 0) into 3:
  --   * The difference functions of the `f n` converge *uniformly* to the difference functions of the `g n`
  --   * The `f' n` are the derivatives of the `f n`
  --   * The `f' n` converge to `g'` at `x`
  conv
  { congr, funext, rw [←norm_norm, ←norm_inv, ←@is_R_or_C.norm_of_real 𝕜 _ _, is_R_or_C.of_real_inv, ←norm_smul], },
  rw ←tendsto_zero_iff_norm_tendsto_zero,
  have : (λ a : ℕ × E, (∥a.snd - x∥⁻¹ : 𝕜) • (g a.snd - g x - (g' x) (a.snd - x))) =
    (λ a : ℕ × E, (∥a.snd - x∥⁻¹ : 𝕜) • (g a.snd - g x - (f a.fst a.snd - f a.fst x))) +
    (λ a : ℕ × E, (∥a.snd - x∥⁻¹ : 𝕜) • ((f a.fst a.snd - f a.fst x) - ((f' a.fst x) a.snd - (f' a.fst x) x))) +
    (λ a : ℕ × E, (∥a.snd - x∥⁻¹ : 𝕜) • ((f' a.fst x - g' x) (a.snd - x))),
  { ext, simp only [pi.add_apply], rw [←smul_add, ←smul_add], congr,
  simp only [map_sub, sub_add_sub_cancel, continuous_linear_map.coe_sub', pi.sub_apply], },
  simp_rw this,
  have : 𝓝 (0 : G) = 𝓝 (0 + 0 + 0), simp,
  rw this,
  refine tendsto.add (tendsto.add _ _) _,
  { -- Difference quotients converge uniformly
    exact (difference_quotients_converge_uniformly hf hfg hfg').mono_left curry_le_prod,
  },
  { -- (Almost) the definition of the derivatives
    simp only,
    rw metric.tendsto_nhds,
    intros ε hε,
    rw eventually_curry_iff,
    apply hf.curry.mono,
    intros n hn,
    have := hn.self_of_nhds,
    rw [has_fderiv_at_iff_tendsto, metric.tendsto_nhds] at this,
    specialize this ε hε,
    apply this.mono,
    intros y hy,
    rw dist_eq_norm at hy ⊢,
    simp at hy ⊢,
    rw [norm_smul, norm_inv, is_R_or_C.norm_coe_norm],
    exact hy,
  },
  { -- hfg' after specializing to `x` and applying the definition of the operator norm
    simp only,
    suffices : tendsto (λ (i : ℕ × E), (↑∥i.snd - x∥)⁻¹ • (f' i.fst x - g' x) (i.snd - x)) (at_top ×ᶠ (𝓝 x)) (𝓝 0), {
      exact this.mono_left (curry_le_prod),
    },
    have : continuous (λ _x : E, x), exact continuous_const,
    have := this.tendsto x,
    have hproj := hfg'.comp (tendsto_id.prod_map this),
    rw tendsto_zero_iff_norm_tendsto_zero at hproj,
    refine squeeze_zero_norm _ hproj,
    simp_rw [norm_smul, norm_inv, is_R_or_C.norm_coe_norm],
    intros n,

    by_cases hx : x = n.snd, { simp [hx], },
    have hnx : 0 < ∥n.snd - x∥,
    {rw norm_pos_iff, intros hx', exact hx (eq_of_sub_eq_zero hx').symm, },
    rw [inv_mul_le_iff hnx, mul_comm],
    exact (f' n.fst x - g' x).le_op_norm (n.snd - x),
  },
end

end limits_of_derivatives
