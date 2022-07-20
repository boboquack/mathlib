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
_uniformly_. The formal statement appears as `has_fderiv_at_of_tendsto_locally_uniformly_at`.

## Main statements

* `has_fderiv_at_of_tendsto_locally_uniformly_at` : If
  1. `f : ℕ → E → G` is a sequence of functions which have derivatives `f' : ℕ → (E → (E →L[𝕜] G))`
    on a neighborhood of `x`,
  2.the `f` converge pointwise to `g` on a neighborhood of `x`, and
  3. the `f'` converge _locally uniformly_ at `x` to `g'`
then the derivative of `g` is `g'` at `x`

## Implementation notes

Our technique for proving the main result is the famous "`ε / 3` proof." In words, you can find it
explained, for instance, at [this StackExchange post](https://math.stackexchange.com/questions/214218/uniform-convergence-of-derivatives-tao-14-2-7).
The subtlety is that we want to prove that the difference quotients of the `g` converge to the `g'`.
That is, we want to prove something like:

```
∀ ε > 0, ∃ δ > 0, ∀ y ∈ B_δ(x), |y - x|⁻¹ * |(g y - g x) - g' x (y - x)| < ε.
```

To do so, we will need to introduce a pair of quantifers

```lean
∀ ε > 0, ∃ N, ∀ n ≥ N, ∃ δ > 0, ∀ y ∈ B_δ(x), |y - x|⁻¹ * |(g y - g x) - g' x (y - x)| < ε.
```

So how do we write this in terms of filters? Well, the initial definition of the derivative is

```lean
tendsto (|y - x|⁻¹ * |(g y - g x) - g' x (y - x)|) (𝓝 x) (𝓝 0)
```

There are two ways we might introduce `n`. We could do:

```lean
∀ᶠ (n : ℕ) in at_top, tendsto (|y - x|⁻¹ * |(g y - g x) - g' x (y - x)|) (𝓝 x) (𝓝 0)
```

but this is equivalent to the quantifier order `∃ N, ∀ n ≥ N, ∀ ε > 0, ∃ δ > 0, ∀ y ∈ B_δ(x)`,
which _implies_ our desired `∀ ∃ ∀ ∃ ∀` but is _not_ equivalent to it. On the other hand, we might
try

```lean
tendsto (|y - x|⁻¹ * |(g y - g x) - g' x (y - x)|) (at_top ×ᶠ 𝓝 x) (𝓝 0)
```

but this is equivalent to the quantifer order `∀ ε > 0, ∃ N, ∃ δ > 0, ∀ n ≥ N, ∀ y ∈ B_δ(x)`, which
again _implies_ our desired `∀ ∃ ∀ ∃ ∀` but is not equivalent to it.

So to get the quantifier order we want, we need to introduce a new filter construction, which we
call a "curried filter"

```lean
tendsto (|y - x|⁻¹ * |(g y - g x) - g' x (y - x)|) (at_top.curry (𝓝 x)) (𝓝 0)
```

Then the above implications are `filter.tendsto.curry` and
`filter.tendsto.mono_left filter.curry_le_prod`. We will use both of these deductions as part of
our proof.

We note that if you loosen the assumptions of the main theorem then the proof becomes quite a bit
easier. In particular, if you assume there is a common neighborhood `s` where all of the three
assumptions of `has_fderiv_at_of_tendsto_locally_uniformly_at` hold and that the `f'` are
continuous, then you can avoid the mean value theorem and much of the work around curried fitlers.

## Tags

uniform convergence, limits of derivatives
-/

section filter_curry

variables {α β γ : Type*}

def filter.curry (f : filter α) (g : filter β) : filter (α × β) :=
{ sets := { s | ∀ᶠ (a : α) in f, ∀ᶠ (b : β) in g, (a, b) ∈ s },
  univ_sets := (by simp only [set.mem_set_of_eq, set.mem_univ, filter.eventually_true]),
  sets_of_superset := begin
    intros x y hx hxy,
    simp only [set.mem_set_of_eq] at hx ⊢,
    exact hx.mono (λ a ha, ha.mono(λ b hb, set.mem_of_subset_of_mem hxy hb)),
  end,
  inter_sets := begin
    intros x y hx hy,
    simp only [set.mem_set_of_eq, set.mem_inter_eq] at hx hy ⊢,
    exact (hx.and hy).mono (λ a ha, (ha.1.and ha.2).mono (λ b hb, hb)),
  end, }

lemma filter.eventually_curry_iff {f : filter α} {g : filter β} {p : α × β → Prop} :
  (∀ᶠ (x : α × β) in f.curry g, p x) ↔ ∀ᶠ (x : α) in f, ∀ᶠ (y : β) in g, p (x, y) :=
begin
  simp only [filter.curry],
  rw filter.eventually_iff,
  simp only [filter.mem_mk, set.mem_set_of_eq],
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

variables {ι : Type*} {l : filter ι}
  {E : Type*} [normed_group E] [normed_space ℝ E]
  {𝕜 : Type*} [is_R_or_C 𝕜] [normed_space 𝕜 E]
  {G : Type*} [normed_group G] [normed_space 𝕜 G]
  {f : ι → E → G} {g : E → G} {f' : ι → (E → (E →L[𝕜] G))} {g' : E → (E →L[𝕜] G)}
  {s : set E} {x : E} {C : ℝ}

/-- If `f_n → g` pointwise and the derivatives `(f_n)' → h` _uniformly_ converge, then
in fact for a fixed `y`, the difference quotients `∥z - y∥⁻¹ • (f_n z - f_n y)` converge
_uniformly_ to `∥z - y∥⁻¹ • (g z - g y)` -/
lemma difference_quotients_converge_uniformly
  (hf : ∀ᶠ (n : ι × E) in (l ×ᶠ 𝓝 x), has_fderiv_at (f n.fst) (f' n.fst n.snd) n.snd)
  (hfg : ∀ᶠ (y : E) in 𝓝 x, tendsto (λ n, f n y) l (𝓝 (g y)))
  (hfg' : tendsto (λ n : ι × E, f' n.fst n.snd - g' n.snd) (l ×ᶠ 𝓝 x) (𝓝 0)) :
  tendsto (λ n : ι × E, (∥n.snd - x∥⁻¹ : 𝕜) • ((g n.snd) - (g x) - ((f n.fst n.snd) - (f n.fst x)))) (l ×ᶠ 𝓝 x) (𝓝 0) :=
begin
  suffices : tendsto (λ n : ι × ι × E, (∥n.2.2 - x∥⁻¹ : 𝕜) • ((f n.1 - f n.2.1) n.2.2 - (f n.1 - f n.2.1) x)) (l ×ᶠ (l ×ᶠ 𝓝 x)) (𝓝 0),
  {
    sorry,
  },
  have hfg'' : tendsto (λ n : (ι × ι) × E, f' n.fst.fst n.snd - f' n.fst.snd n.snd) (l ×ᶠ l ×ᶠ 𝓝 x) (𝓝 0), sorry,
  have := tendsto_swap4_prod.eventually (hf.prod_mk hf),
  have := tendsto_prod_assoc_symm.eventually (bah this),
  simp_rw [metric.tendsto_nhds, dist_eq_norm, sub_zero] at hfg'' ⊢,
  intros ε hε,
  obtain ⟨q, hqpos, hqε⟩ := exists_pos_rat_lt hε,
  have hold := tendsto_prod_assoc_symm.eventually (hfg'' (q : ℝ) (by simp [hqpos])),
  obtain ⟨a, b, c, d, e⟩ := eventually_prod_iff.1 (hold.and this),
  obtain ⟨a', b', c', d', e'⟩ := eventually_prod_iff.1 d,
  obtain ⟨r, hr, hr'⟩ := metric.nhds_basis_ball.eventually_iff.mp d',
  rw eventually_prod_iff,
  refine ⟨a, b, (λ n : ι × E, a' n.fst ∧ metric.ball x r n.snd),
    b'.prod_mk (eventually_mem_set.mpr (metric.nhds_basis_ball.mem_of_mem hr)), λ n hn n' hn', _⟩,

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
lemma has_fderiv_at_of_tendsto_locally_uniformly_at [l.ne_bot]
  (hf : ∀ᶠ (n : ι × E) in (l ×ᶠ 𝓝 x), has_fderiv_at (f n.fst) (f' n.fst n.snd) n.snd)
  (hfg : ∀ᶠ y in 𝓝 x, tendsto (λ n, f n y) l (𝓝 (g y)))
  (hfg' : tendsto (λ n : ι × E, f' n.fst n.snd - g' n.snd) (l ×ᶠ 𝓝 x) (𝓝 0)) :
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
  suffices : tendsto (λ (y : ι × E), ∥y.snd - x∥⁻¹ * ∥g y.snd - g x - (g' x) (y.snd - x)∥) (l.curry (𝓝 x)) (𝓝 0), {
    -- NOTE (khw): This is a more generic fact, but is easier for now to prove in the metric case
    rw metric.tendsto_nhds at this ⊢,
    intros ε hε,
    specialize this ε hε,
    rw eventually_curry_iff at this,
    simp only at this,
    exact (eventually_const.mp this).mono (by simp only [imp_self, forall_const]), },

  -- With the new quantifier in hand, we can perform the famous `ε/3` proof. Specifically,
  -- we will break up the limit (the difference functions minus the derivative go to 0) into 3:
  --   * The difference functions of the `f n` converge *uniformly* to the difference functions of the `g n`
  --   * The `f' n` are the derivatives of the `f n`
  --   * The `f' n` converge to `g'` at `x`
  conv
  { congr, funext, rw [←norm_norm, ←norm_inv, ←@is_R_or_C.norm_of_real 𝕜 _ _, is_R_or_C.of_real_inv, ←norm_smul], },
  rw ←tendsto_zero_iff_norm_tendsto_zero,
  have : (λ a : ι × E, (∥a.snd - x∥⁻¹ : 𝕜) • (g a.snd - g x - (g' x) (a.snd - x))) =
    (λ a : ι × E, (∥a.snd - x∥⁻¹ : 𝕜) • (g a.snd - g x - (f a.fst a.snd - f a.fst x))) +
    (λ a : ι × E, (∥a.snd - x∥⁻¹ : 𝕜) • ((f a.fst a.snd - f a.fst x) - ((f' a.fst x) a.snd - (f' a.fst x) x))) +
    (λ a : ι × E, (∥a.snd - x∥⁻¹ : 𝕜) • ((f' a.fst x - g' x) (a.snd - x))),
  { ext, simp only [pi.add_apply], rw [←smul_add, ←smul_add], congr,
  simp only [map_sub, sub_add_sub_cancel, continuous_linear_map.coe_sub', pi.sub_apply], },
  simp_rw this,
  have : 𝓝 (0 : G) = 𝓝 (0 + 0 + 0), simp only [add_zero],
  rw this,
  refine tendsto.add (tendsto.add _ _) _,
  simp only,
  { exact (difference_quotients_converge_uniformly hf hfg hfg').mono_left curry_le_prod, },
  { -- (Almost) the definition of the derivatives
    rw metric.tendsto_nhds,
    intros ε hε,
    rw eventually_curry_iff,
    refine hf.curry.mono (λ n hn, _),
    have := hn.self_of_nhds,
    rw [has_fderiv_at_iff_tendsto, metric.tendsto_nhds] at this,
    refine (this ε hε).mono (λ y hy, _),
    rw dist_eq_norm at hy ⊢,
    simp only [sub_zero, map_sub, norm_mul, norm_inv, norm_norm] at hy ⊢,
    rw [norm_smul, norm_inv, is_R_or_C.norm_coe_norm],
    exact hy, },
  { -- hfg' after specializing to `x` and applying the definition of the operator norm
    refine tendsto.mono_left _ curry_le_prod,
    have : continuous (λ _x : E, x) := continuous_const,
    have hproj := hfg'.comp (tendsto_id.prod_map (this.tendsto x)),
    refine squeeze_zero_norm _ (tendsto_zero_iff_norm_tendsto_zero.mp hproj),
    simp_rw [norm_smul, norm_inv, is_R_or_C.norm_coe_norm],
    intros n,

    by_cases hx : x = n.snd, { simp [hx], },
    have hnx : 0 < ∥n.snd - x∥,
    { rw norm_pos_iff, intros hx', exact hx (eq_of_sub_eq_zero hx').symm, },
    rw [inv_mul_le_iff hnx, mul_comm],
    exact (f' n.fst x - g' x).le_op_norm (n.snd - x), },
end

end limits_of_derivatives
