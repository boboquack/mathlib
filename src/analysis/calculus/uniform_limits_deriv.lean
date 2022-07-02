/-
Copyright (c) 2022 Kevin H. Wilson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin H. Wilson
-/
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

section generic

lemma ball_mem_mono
{α : Type*}
{s s' : set α}
{p : α → Prop}
(hs : s' ⊆ s) :
(∀ x : α, x ∈ s → p x) → (∀ x : α, x ∈ s' → p x) :=
λ h x hx, h x (calc x ∈ s' : hx ... ⊆ s : hs)

open filter
open_locale topological_space filter

lemma tendsto_prod_nhds_within_iff
  {α β ι : Type*} [uniform_space β] [topological_space α]
  {F : ι → α → β} {c : β} {p : filter ι} {s : set α} :
  ∀ y : α, y ∈ s → tendsto ↿F (p ×ᶠ (𝓝[s] y)) (𝓝 c) ↔
  tendsto_locally_uniformly_on F (λ _x, c) p s :=
begin
  sorry,
end



lemma filter.eventually.ne_bot_of_prop
  {ι : Type*} (l : filter ι) [l.ne_bot] (p : Prop)
  (hl : ∀ᶠ i in l, p) : p :=
begin
  rw filter.eventually_iff at hl,
  rcases set.eq_empty_or_nonempty {x : ι | p} with hs | hs,
  exfalso,
  have := filter.empty_not_mem l,
  rw ← hs at this,
  exact this hl,
  rcases hs with ⟨ x, hx ⟩,
  simp at hx,
  exact hx,
end

lemma tendsto_uniformly_on.tendsto_at
  {ι : Type*}
  {α : Type*}
  {β : Type*}
  [uniform_space β]
  {l : filter ι}
  {s : set α}
  {f : ι → α → β}
  {g : α → β}
  (hfg' : tendsto_uniformly_on f g l s) {x : α} (hx : x ∈ s) :
  filter.tendsto (λ n, f n x) l (nhds (g x)) :=
begin
  sorry,
end

lemma blah {α : Type*} {α' : Type*} {β : Type*} {f : α → β} {l : filter α} {l' : filter α'} {p : filter β}:
  filter.tendsto (λ a : α × α', f a.fst) (l.prod l') p ↔ filter.tendsto f l p :=
begin
  split,
  intros h,
  sorry,
  intros h,
  have := @filter.tendsto_id _ l',
  exact filter.tendsto_fst.comp (h.prod_map this),

end

lemma blah' {α : Type*} {α' : Type*} {β : Type*} {f : α → β} {l : filter α} {l' : filter α'} {p : filter β}:
  filter.tendsto (λ a : α' × α, f a.snd) (l'.prod l) p ↔ filter.tendsto f l p :=
begin
  split,
  intros h,
  sorry,
  intros h,
  have := @filter.tendsto_id _ l',
  exact filter.tendsto_snd.comp (this.prod_map h),

end

lemma tendsto_prod_principal_iff
  {ι : Type*}
  {α : Type*}
  {β : Type*}
  [uniform_space β]
  {l : filter ι}
  {s : set α}
  {f : ι → α → β}
  {c : β} : filter.tendsto ↿f (l.prod (filter.principal s)) (nhds c) ↔ tendsto_uniformly_on f (λ _, c) l s :=
begin
  sorry,
end


end generic

open filter
open_locale uniformity filter topological_space

lemma blah'' {ι : Type*} {p : Prop} {l : filter ι} [l.ne_bot] :
  (∀ᶠ i in l, p) → p :=
begin
  simp only [eventually_const, imp_self],
end

section limits_of_derivatives

variables {E : Type*} [normed_group E] [normed_space ℝ E]
  {𝕜 : Type*} [is_R_or_C 𝕜] [normed_space 𝕜 E]
  {G : Type*} [normed_group G] [normed_space 𝕜 G]
  {f : ℕ → E → G} {g : E → G} {f' : ℕ → (E → (E →L[𝕜] G))} {g' : E → (E →L[𝕜] G)}
  {s : set E} {x : E} {C : ℝ}

/-- A convenience theorem for utilizing the mean value theorem for differences of
differentiable functions -/
lemma mean_value_theorem_for_differences
  {f : E → G} {f' : E → (E →L[𝕜] G)}
  (hf : ∀ᶠ y in 𝓝 x, has_fderiv_at f (f' y) y)
  (hg : ∀ᶠ y in 𝓝 x, has_fderiv_at g (g' y) y)
  (hbound : ∀ᶠ y in 𝓝 x, ∥f' y - g' y∥ ≤ C) :
  ∀ᶠ y in 𝓝 x, ∥y - x∥⁻¹ * ∥(f y - g y) - (f x - g x)∥ ≤ C :=
begin

  obtain ⟨r, hr, h⟩ := nhds_basis_closed_ball.eventually_iff.mp (((hf.and hg).and hbound)),
  rw nhds_basis_closed_ball.eventually_iff,
  use [r, hr],
  intros y hy,

  have hxx : x ∈ closed_ball x r, simp only [hr.le, mem_closed_ball, dist_self],

  -- Differences of differentiable functions are differentiable
  have hderiv : ∀ (y : E), y ∈ closed_ball x r →
    has_fderiv_within_at (f - g) ((f' - g') y) (closed_ball x r) y,
  { intros y hy,
    obtain ⟨⟨hf, hg⟩, hbound⟩ := h hy,
    exact (hf.sub hg).has_fderiv_within_at, },

  -- Apply the mean value theorem
  have := convex.norm_image_sub_le_of_norm_has_fderiv_within_le
    hderiv (λ y hy, (h hy).right) (convex_closed_ball x r) hxx hy,

  -- Auxiliary lemmas necessary for algebraic manipulation
  have h_le : ∥y - x∥⁻¹ ≤ ∥y - x∥⁻¹, { exact le_refl _, },
  have C_nonneg : 0 ≤ C,
  { calc 0 ≤ ∥f' y - g' y∥ : norm_nonneg _ ... ≤ C : (h hy).right, },
  have h_le' : 0 ≤ C * ∥y - x∥, exact mul_nonneg C_nonneg (by simp),

  -- The case y = z is degenerate. Eliminate it
  by_cases h : y = x,
  { simp only [h, C_nonneg, sub_self, norm_zero, mul_zero], },
  have h_ne_zero : ∥y - x∥ ≠ 0,
  { simp only [ne.def, norm_eq_zero],
    exact λ hh, h (sub_eq_zero.mp hh), },

  -- Final manipulation
  have := mul_le_mul this h_le (by simp) h_le',
  simp only [pi.sub_apply] at this,
  rw mul_inv_cancel_right₀ h_ne_zero at this,
  rwa mul_comm,
end

/-- If `f_n → g` pointwise and the derivatives `(f_n)' → h` _uniformly_ converge, then
in fact for a fixed `y`, the difference quotients `∥z - y∥⁻¹ • (f_n z - f_n y)` converge
_uniformly_ to `∥z - y∥⁻¹ • (g z - g y)` -/
lemma difference_quotients_converge_uniformly (hs : convex ℝ s)
  (hf : ∀ (y : E), y ∈ s → ∀ᶠ (n : ℕ) in at_top, has_fderiv_at (f n) (f' n y) y)
  (hfg : ∀ (y : E), y ∈ s → tendsto (λ n, f n y) at_top (𝓝 (g y)))
  (hfg' : tendsto_uniformly_on f' g' at_top s) :
  ∀ y : E, y ∈ s →
    tendsto_uniformly_on
      (λ n : ℕ, λ z : E, (∥z - y∥⁻¹ : 𝕜) • ((f n z) - (f n y)))
      (λ z : E, (∥z - y∥⁻¹ : 𝕜) • ((g z) - (g y))) at_top s :=
begin
  -- Rewrite the Cauchy sequence as a difference quotient of the difference of functions
  intros y hy,
  refine uniform_cauchy_seq_on.tendsto_uniformly_on_of_tendsto _
    (λ z hz, ((hfg z hz).sub (hfg y hy)).const_smul _),
  simp_rw [normed_group.uniform_cauchy_seq_on_iff_tendsto_uniformly_on_zero, ←smul_sub],
  have : ∀ a b c d : G, a - b - (c - d) = a - c - (b - d),
  { intros a b c d,
    rw [←sub_add, ←sub_add, sub_sub, sub_sub],
    conv { congr, congr, congr, skip, rw add_comm, }, },
  conv { congr, funext, rw this, },

  -- We'll show this difference quotient is uniformly arbitrarily small
  rw normed_group.tendsto_uniformly_on_zero,
  intros ε hε,

  -- The uniform convergence of the derivatives allows us to invoke the mean value theorem
  have := tendsto_uniformly_on.uniform_cauchy_seq_on hfg',
  rw [normed_group.uniform_cauchy_seq_on_iff_tendsto_uniformly_on_zero, normed_group.tendsto_uniformly_on_zero] at this,

  have two_inv_pos : 0 < (2 : ℝ)⁻¹, simp,
  have ε_over_two_pos : 0 < (2⁻¹ * ε),
  { exact mul_pos two_inv_pos hε.lt, },

  refine ((this (2⁻¹ * ε) ε_over_two_pos.gt).mono (λ N h y hy, (h y hy).le)).mono _,
  intros N h z hz,

  have mvt := mean_value_theorem_for_differences hs (hf N.fst) (hf N.snd) h hz hy,
  rw [norm_smul, norm_inv, is_R_or_C.norm_coe_norm],
  refine lt_of_le_of_lt mvt _,
  rw ←div_eq_inv_mul,
  exact half_lt_self hε.lt,
end

lemma foobar {ι : Type*}
  {f : ι → E → G} {g : E → 𝕜} {l : filter ι}
  (hf : tendsto_uniformly_on f 0 l s) (hg : ∀ x : E, x ∈ s → ∥g x∥ ≤ C) :
  tendsto_uniformly_on (λ n : ι, λ z : E, (g z) • f n z) 0 l s :=
begin
  rw metric.tendsto_uniformly_on_iff at hf ⊢,
  intros ε hε,

  -- We can assume that C is positive
  let C' := max C 1,
  have hg' : ∀ x : E, x ∈ s → ∥g x∥ ≤ C',
  { exact (λ x hx, le_trans (hg x hx) (by simp)), },
  have hC : 0 < C', simp [C'],

  apply (hf (C'⁻¹ * ε) ((mul_pos (inv_pos.mpr hC) hε.lt).gt)).mono,
  intros i hf' x hx,
  have := mul_lt_mul' (hg' x hx) (hf' x hx) (by simp) hC,
  rw [mul_inv_cancel_left₀ hC.ne.symm] at this,
  rw [pi.zero_apply, dist_zero_left, norm_smul],
  simpa using this,
end

lemma uniform_convergence_of_uniform_convergence_derivatives
  {s : set E} (hs : bounded s) (hsc : convex ℝ s)
  (hf : ∀ (n : ℕ), ∀ (y : E), y ∈ s → has_fderiv_at (f n) (f' n y) y)
  (hfg : ∀ (y : E), y ∈ s → tendsto (λ n, f n y) at_top (𝓝 (g y)))
  (hfg' : tendsto_uniformly_on f' g' at_top s) :
  tendsto_uniformly_on f g at_top s :=
begin
  -- The case s is empty is trivial. Elimintate it and extract a base point `x`
  rcases set.eq_empty_or_nonempty s with rfl | ⟨x, hx⟩,
  { exact tendsto_uniformly_on_of_empty, },

  -- Get a bound on s and get it into the format we need it in
  cases hs with C hC,
  specialize hC x hx,
  have hC : ∀ (y : E), y ∈ s → ∥(λ y, ∥y - x∥) y∥ ≤ C,
  { intros y hy,
    specialize hC y hy,
    rw [dist_comm, dist_eq_norm, ←norm_norm] at hC,
    exact hC, },

  -- Study (λ n y, f n y - f n x) instead of f
  refine uniform_cauchy_seq_on.tendsto_uniformly_on_of_tendsto _ hfg,
  have : f = (λ n : ℕ, λ y : E, f n y - f n x) + (λ n : ℕ, λ y : E, f n x),
  { ext, simp, },
  rw this,
  have := (tendsto.tendsto_uniformly_on_const (hfg x hx) s).uniform_cauchy_seq_on,
  refine uniform_cauchy_seq_on.add _ this,

  -- We'll use the lemma we already prove and multiply it by a uniform constant
  have := (difference_quotients_converge_uniformly hsc hf hfg hfg' x hx).uniform_cauchy_seq_on,
  rw normed_group.uniform_cauchy_seq_on_iff_tendsto_uniformly_on_zero at this,
  have := foobar this hC,
  rw normed_group.uniform_cauchy_seq_on_iff_tendsto_uniformly_on_zero,
  refine this.congr_fun (λ n y hy, _),
  simp only,
  rw [←smul_sub, ←smul_assoc],
  norm_cast,

  -- The trivial case must be eliminated to allow for cancellation
  by_cases h : y = x,
  { simp [h], },
  rw mul_inv_cancel (λ h', h (sub_eq_zero.mp (norm_eq_zero.mp h'))),
  simp,
end

lemma normed_group.fooooo
  {ι : Type*}
  {f : ι → E → G} {g : E → G} {s : set E} {l : filter ι} :
  tendsto_uniformly_on f g l s ↔ tendsto_uniformly_on (λ n, λ z, f n z - g z) 0 l s :=
begin
  sorry,
  -- split,
  -- intros hf u hu,
  -- specialize hf u hu,
  -- { intros hf u hu,
  --   obtain ⟨ε, hε, H⟩ := uniformity_basis_dist.mem_uniformity_iff.mp hu,
  --   have : {p : G × G | dist p.fst p.snd < ε} ∈ (𝓤 G),
  --   { rw uniformity_basis_dist.mem_uniformity_iff,
  --     use ε,
  --     exact ⟨hε, by simp [H]⟩, },

  --   refine (hf {p : G × G | dist p.fst p.snd < ε} this).mono (λ N h x hx, H _ _ _),
  --   specialize h x hx,
  --   simp at h,
  --   rw dist_eq_norm at h,
  --   simp [h], },

  -- { intros hf u hu,
  --   obtain ⟨ε, hε, H⟩ := uniformity_basis_dist.mem_uniformity_iff.mp hu,
  --   have : {p : G × G | dist p.fst p.snd < ε} ∈ (𝓤 G),
  --   { rw uniformity_basis_dist.mem_uniformity_iff,
  --     use ε,
  --     exact ⟨hε, by simp [H]⟩, },
  --   refine (hf {p : G × G | dist p.fst p.snd < ε} this).mono (λ N h x hx, H _ _ _),
  --   specialize h x hx,
  --   simp only [set.mem_set_of_eq, dist_eq_norm] at h ⊢,
  --   rw norm_sub_rev at h,
  --   simpa using h, },
end

lemma filter.tendsto.mono_left_congr
  {α : Type*} {β : Type*} {f g : α → β} {x y : filter α} {z : filter β}
  (hx : tendsto f x z) (hfg : f = g) (h : y ≤ x) : tendsto g y z :=
begin
  sorry,
end

lemma asdfasdf {f : E → G} {l : filter E} {l' : filter G} {p : filter ℕ} :
  tendsto f l l' → tendsto (λ x : (ℕ × E), f x.snd) (p ×ᶠ l) l' :=
begin
  intros h,
  unfold tendsto at h ⊢,
  have : map f l = map (λ (x : ℕ × E), f x.snd) (p ×ᶠ l), {
    ext,
    split,
    simp,
    intros hh,
    rw mem_prod_iff,
    use set.univ,
    simp,
    use  f ⁻¹' s,
    simp [hh],
    rw set.subset_def,
    intros x hx,
    simp at hx,
    simp,
    exact hx,

    simp,
    intros hh,
    rw mem_prod_iff at hh,
    rcases hh with ⟨a, b, c, d, e⟩,
    rw set.subset_def at e,
    rw pr
  },
  rw tendsto_iff_eventually at h ⊢,
  intros prop hp,
  specialize h hp,

  sorry,
end

/-- (d/dx) lim_{n → ∞} f_n x = lim_{n → ∞} f'_n x on a closed ball when the f'_n
converge _uniformly_ to their limit.

TODO (khw): This statement ends up being a bit awkward because we have to explicitly include
a set `s ∈ 𝓝 x` in the assumptions. This could be obviated if we defined a notion of
`tendsto_uniformly_at` which would be equivalent to
`tendsto (λ a, f a.fst a.snd - g.snd) (l ×ᶠ 𝓝 x) (𝓝 0)`. However, I'm not certain of its utility.
-/
lemma has_fderiv_at_of_tendsto_uniformly_on
  {s : set E} {hs : s ∈ 𝓝 x}
  (hf : ∀ᶠ y in 𝓝 x, ∀ᶠ (n:ℕ) in at_top, has_fderiv_at (f n) (f' n y) y)
  (hfg : ∀ᶠ y in 𝓝 x, tendsto (λ n, f n y) at_top (𝓝 (g y)))
  (hfg' : tendsto_uniformly_on f' g' at_top s) :
  has_fderiv_at g (g' x) x :=
begin
  -- We do the famous "ε / 3 proof" which will involve several bouts of utilizing
  -- uniform continuity. First, we setup our goal for easier algebraic manipulation
  rw has_fderiv_at_iff_tendsto,
  conv
  { congr, funext, rw [←norm_norm, ←norm_inv, ←@is_R_or_C.norm_of_real 𝕜 _ _, is_R_or_C.of_real_inv, ←norm_smul], },
  rw ←tendsto_zero_iff_norm_tendsto_zero,

  -- Next we need to shrink `s` until `hf` and `hfg` apply, and that `s` is bounded and convex
  -- so that we can apply the mean value theorem.
  obtain ⟨r', hr', h'⟩ := metric.nhds_basis_closed_ball.eventually_iff.mp (hf.and hfg),
  obtain ⟨r, hr, h⟩ := metric.nhds_basis_closed_ball.mem_iff.mp hs,
  let s' := metric.closed_ball x (min r r'),
  have hs' : s' ∈ 𝓝 x, sorry,
  have hxs : x ∈ s', sorry,
  have hss' : s' ⊆ s, sorry,
  have hss'' : s' ⊆ metric.closed_ball x r', sorry,
  have hsc : convex ℝ s', sorry,
  have hsb : metric.bounded s', sorry,
  have hfg' : tendsto_uniformly_on f' g' at_top s', sorry,
  obtain ⟨hf1, hfg1⟩ := ball_and_distrib.mp (ball_mem_mono hss'' h'),

  -- Next we replace 𝓝 x with 𝓝[s] x and upgrade our goal to include `N`
  refine tendsto.mono_left _ (le_inf rfl.le (le_principal_iff.mpr hs')),
  -- apply (@eventually_const _ (at_top : filter ℕ) _ _).mp,
  suffices :
    tendsto_uniformly_on (λ n : ℕ, λ y : E, (∥y - x∥⁻¹ : 𝕜) • (g y - g x - (f n y - f n x))) (λ _x, 0) at_top s'
    -- ∧ tendsto_uniformly_on (λ n : ℕ, λ e : E, (∥e - x∥⁻¹ : 𝕜) • ((f n x - f n x) - ((f' n x) e - (f' n x) x))) (λ _x, 0) at_top s'
    ∧ tendsto_uniformly_on (λ n : ℕ, λ e : E, (∥e - x∥⁻¹ : 𝕜) • ((f' n x - g' x) (e - x))) (λ _x, 0) at_top s',

    -- ∧ (∀ᶠ (n : ℕ) in at_top, tendsto (λ e : E, (∥e - x∥⁻¹ : 𝕜) • ((f' n x - g' x) (e - x))) (𝓝[s] x) (𝓝 0)),
  {
    rcases this with ⟨h1, h2⟩,
    have := h1.add h2,
    rw ←tendsto_prod_principal_iff at h1 h2,
    specialize hf1 x hxs,
    rw tendsto_iff_eventually,
    intros prop,
    intros hh,
    have := (h1.eventually hh).and (h2.eventually hh),
    apply (@eventually_const _ (at_top : filter ℕ) _ _).mp,
    sorry,
    -- suffices : ∀ᶠ (a : ℕ × E) in (at_top ×ᶠ (𝓝 x ⊓ 𝓟 s')), (λ a : ℕ × E, prop ((↑∥a.snd - x∥)⁻¹ • (g a.snd - g x - (g' x) (a.snd - x)))) a, {
    --   sorry,
    -- },
    -- sorry,
    -- -- apply eventually.curry,
    -- -- have := h2.eventually hh,
  },
  split,
  {
    have hdiff := difference_quotients_converge_uniformly hsc hf1 hfg1 hfg' x hxs,
    rw normed_group.fooooo at hdiff,
    apply hdiff.congr_fun,
    apply eventually_of_forall,
    intros n,
    intros z hz, simp,
    sorry,
  },
  split,
  {
    sorry,
  },
  {
    rw eventually_iff at hf,
    rw mem_nhds_iff at hf,
    rcases hf with ⟨t, ht, ht', ht''⟩,
    have := set.mem_of_mem_of_subset ht'' ht,
    simp only [set.mem_set_of_eq] at this,
    apply this.mono,
    intros n hn,
    have := hn.has_fderiv_within_at,
    rw has_fderiv_within_at_iff_tendsto at this,
    simp_rw has_fderiv_within_at_iff_tendsto at this,
    sorry,
  },

  -- Now break the goal into each of the `ε/3` components
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

  -- convergence of the primal and uniform convergence of the derivatives implies
  -- uniform convergence of the difference quotients
  have hdiff := difference_quotients_converge_uniformly hsc hf hfg hfg' x hxs,
  rw normed_group.fooooo at hdiff,
  have : (0 : E → G) = (λ x:E, 0), ext, simp,
  rw this at hdiff,
  simp only at hdiff ⊢,
  rw ←tendsto_prod_principal_iff at hdiff,
  -- norm_cast at hdiff,
  rw tendsto_zero_iff_norm_tendsto_zero,
  conv { congr, funext, rw smul_sub, rw norm_sub_rev, },
  rw ←tendsto_zero_iff_norm_tendsto_zero,
  refine hdiff.mono_left_congr _ _,
  ext, simp only [function.has_uncurry.uncurry, id.def], refine filter.prod_mono rfl.le inf_le_right,

  simp only,
  simp_rw has_fderiv_at_iff_tendsto at hf,
  sorry,
  -- rw ←tendsto_prod_principal_iff at hfg',


  -- The first (ε / 3) comes from the convergence of the derivatives
  -- have hfg' := hfg'.uniform_cauchy_seq_on,
  -- use filter.tendsto.mono_left on 𝓟 s ⊓ 𝓝 y = 𝓝[s] y
  rw normed_group.fooooo at hfg',
  have : (0 : E → (E →L[𝕜] G)) = (λ x:E, 0), ext, simp,
  rw this at hfg',
  rw ←tendsto_prod_principal_iff at hfg',
  simp only at hfg' ⊢,
  refine hfg'.mono_left_congr _ _,

  have := (hfg'.tendsto_at hyc),

  -- The second (ε / 3) comes from the uniform convergence of the difference quotients
  rw normed_group.fooooo at hdiff,

  -- These two N determine our final N
  let N := 10, -- max N1 N2,

  -- The final (ε / 3) comes from the definition of a derivative
  specialize hf N y hyc,
  rw [has_fderiv_at_iff_tendsto] at hf, --, tendsto_nhds_nhds] at hf,
  specialize hf (3⁻¹ * ε) ε_over_three_pos.gt,
  rcases hf with ⟨δ', hδ', hf⟩,

  -- Choose our final δ
  let δ := min (r - dist y x) δ',
  have hδ : δ > 0,
  { refine lt_min _ hδ'.lt,
    rw sub_pos,
    exact hy, },

  -- Start the final manipulation
  use [δ, hδ],
  intros x' hx',
  have hxc : x' ∈ closed_ball x r,
  { have foo := calc dist x' y < δ : hx' ... ≤ r - dist y x : by simp [δ],
    calc dist x' x ≤ dist x' y + dist y x : dist_triangle _ _ _ ... ≤ r : by linarith, },
  have hxy : dist x' y < δ', calc dist x' y < δ : hx' ... ≤ δ' : by simp [δ],
  specialize hf hxy,

  -- There's a technical issue where we need to rule out the case y = x'
  by_cases hy' : y = x',
  { simp [hy', hε.lt], },
  have hx'y : x' - y ≠ 0, exact λ H, hy' (sub_eq_zero.mp H).symm,
  have hx'yy : 0 < ∥x' - y∥, simp only [hx'y, norm_pos_iff, ne.def, not_false_iff],

  -- Our three inequalities come from `hf`, `hN1`, and `hN2`. Get them and the goal in
  -- shape for the final triangle inequality application
  specialize hN1 N (by simp) y hyc,
  rw dist_comm at hN1,
  have hN1 := (f' N y - g' y).le_of_op_norm_le hN1.le (x' - y),
  rw [←mul_inv_le_iff' hx'yy, mul_comm] at hN1,

  specialize hN2 N (by simp) x' hxc,
  rw [dist_eq_norm, ←smul_sub, norm_smul] at hN2,
  simp only [norm_inv, is_R_or_C.norm_coe_norm] at hN2,

  rw dist_eq_norm at hf ⊢,
  simp only [map_sub, sub_zero, norm_mul, norm_inv, norm_norm] at hf,
  simp only [algebra.id.smul_eq_mul, sub_zero, norm_mul, norm_inv, norm_norm],

  -- Final calculation
  calc  ∥x' - y∥⁻¹ * ∥g x' - g y - (g' y) (x' - y)∥ =
    ∥x' - y∥⁻¹ * ∥(g x' - g y - (f N x' - f N y)) +
    ((f N x' - f N y) - ((f' N y) x' - (f' N y) y)) +
    ((f' N y - g' y) (x' - y))∥ : by simp
  ... ≤ ∥x' - y∥⁻¹ * ∥(g x' - g y - (f N x' - f N y))∥ +
    ∥x' - y∥⁻¹ * ∥((f N x' - f N y) - ((f' N y) x' - (f' N y) y))∥ +
    ∥x' - y∥⁻¹ * ∥((f' N y - g' y) (x' - y))∥ : begin
      rw [←mul_add (∥x' - y∥⁻¹) _ _, ←mul_add (∥x' - y∥⁻¹) _ _],
      have : ∥x' - y∥⁻¹ ≤ ∥x' - y∥⁻¹, exact le_refl _,
      refine mul_le_mul this _ (by simp) (by simp),
      exact norm_add₃_le _ _ _,
    end
  ... < 3⁻¹ * ε + 3⁻¹ * ε + 3⁻¹ * ε : add_lt_add_of_lt_of_le (add_lt_add hN2 hf) hN1
  ... = ε : by ring,
end

end limits_of_derivatives
