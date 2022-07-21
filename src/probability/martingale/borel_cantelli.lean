/-
Copyright (c) 2022 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying
-/
import probability.martingale.convergence

/-!

# Generalized Borel-Cantelli lemma

-/

open topological_space filter
open_locale nnreal ennreal measure_theory probability_theory big_operators topological_space

namespace measure_theory

variables {α : Type*} {m0 : measurable_space α} {μ : measure α}
  {ℱ : filtration ℕ m0} {f : ℕ → α → ℝ}

/-
for a (sub)martingale `f` with bounded difference,
`∀ᵐ x ∂μ, f n x converges ↔ (f n x) is bounded in n`
-/

noncomputable
def least_ge (f : ℕ → α → ℝ) (r : ℝ) (n : ℕ) := hitting f (set.Ici r) 0 n

lemma adapted.is_stopping_time_least_ge (r : ℝ) (n : ℕ) (hf : adapted ℱ f) :
  is_stopping_time ℱ (least_ge f r n) :=
hitting_is_stopping_time hf measurable_set_Ici

section move

lemma eventually_le.add_le_add {α β : Type*} [ordered_semiring β] {l : filter α}
  {f₁ f₂ g₁ g₂ : α → β} (hf : f₁ ≤ᶠ[l] f₂) (hg : g₁ ≤ᶠ[l] g₂) : f₁ + g₁ ≤ᶠ[l] f₂ + g₂ :=
by filter_upwards [hf, hg] with x hfx hgx using add_le_add hfx hgx

variables {β : Type*}
variables {u : ℕ → α → β} {τ : α → ℕ}

lemma stopped_process_eq' [add_comm_monoid β] (n : ℕ) :
  stopped_process u τ n =
  set.indicator {a | n + 1 ≤ τ a} (u n) +
    ∑ i in finset.range (n + 1), set.indicator {a | τ a = i} (u i) :=
begin
  have : {a | n ≤ τ a}.indicator (u n) =
    {a | n + 1 ≤ τ a}.indicator (u n) + {a | τ a = n}.indicator (u n),
  { ext x,
    rw [add_comm, pi.add_apply, ← set.indicator_union_of_not_mem_inter],
    { simp_rw [@eq_comm _ _ n, @le_iff_eq_or_lt _ _ n, nat.succ_le_iff],
      refl },
    { rintro ⟨h₁, h₂⟩,
      exact (nat.succ_le_iff.1 h₂).ne h₁.symm } },
  rw [stopped_process_eq, this, finset.sum_range_succ_comm, ← add_assoc],
end

lemma not_mem_of_lt_hitting {ι : Type*}
  [conditionally_complete_linear_order ι] [is_well_order ι (<)]
  {u : ι → α → β} {s : set β} {x : α} {n m k : ι}
  (hk₁ : k < hitting u s n m x) (hk₂ : n ≤ k) :
  u k x ∉ s :=
begin
  classical,
  intro h,
  have hexists : ∃ j ∈ set.Icc n m, u j x ∈ s,
  refine ⟨k, ⟨hk₂, le_trans hk₁.le $ hitting_le _⟩, h⟩,
  refine not_le.2 hk₁ _,
  simp_rw [hitting, if_pos hexists],
  exact cInf_le bdd_below_Icc.inter_of_left ⟨⟨hk₂, le_trans hk₁.le $ hitting_le _⟩, h⟩,
end

lemma hitting_eq_end_iff {ι : Type*} [conditionally_complete_linear_order ι]
  {u : ι → α → β} {s : set β} {n m : ι} {x : α} :
  hitting u s n m x = m ↔ (∃ j ∈ set.Icc n m, u j x ∈ s) →
    Inf (set.Icc n m ∩ {i : ι | u i x ∈ s}) = m :=
by rw [hitting, ite_eq_right_iff]

end move

lemma stopped_value_least_ge_eq (i : ℕ) (r : ℝ) :
  stopped_value f (least_ge f r i) = stopped_process f (least_ge f r i) i :=
begin
  ext x,
  exact congr_arg2 _ (min_eq_right (hitting_le x : least_ge f r i x ≤ i)).symm rfl
end

lemma least_ge_le {i : ℕ} {r : ℝ} (x : α) : least_ge f r i x ≤ i :=
hitting_le x

lemma nat.eq_zero_or_eq_one_of_le {a : ℕ} (h : a ≤ 1) : a = 0 ∨ a = 1 :=
by { rw ← nat.lt_one_iff, exact lt_or_eq_of_le h }

lemma submartingale.stopped_value_least_ge_zero [is_finite_measure μ]
  (hf : submartingale f ℱ μ) (r : ℝ) :
  stopped_value f (least_ge f r 0) ≤ᵐ[μ] μ[stopped_value f (least_ge f r 1)|ℱ 0] :=
begin
  have hlge0 : least_ge f r 0 = 0,
  { ext x,
    simp only [least_ge, hitting, set.Icc_self],
    split_ifs with hx,
    { by_cases hmem : 0 ∈ {i | f i x ∈ set.Ici r},
      { rw [set.inter_eq_left_iff_subset.2 (set.singleton_subset_iff.2 hmem),
          cInf_singleton, pi.zero_apply] },
      { rw [set.singleton_inter_eq_empty.2 hmem, nat.Inf_empty, pi.zero_apply] } },
    { refl } },
  simp_rw [hlge0, stopped_value_eq least_ge_le, finset.sum_range_succ,
    finset.range_zero, finset.sum_empty, zero_add, stopped_value, pi.zero_apply],
  refine eventually_le.trans _ (condexp_add
    ((hf.integrable 0).indicator $ ℱ.le _ _ $
      (hf.adapted.is_stopping_time_least_ge r 1).measurable_set_eq 0)
    ((hf.integrable 1).indicator $ ℱ.le _ _ $
      (hf.adapted.is_stopping_time_least_ge r 1).measurable_set_eq 1)).symm.le,
  calc f 0 = {x : α | least_ge f r 1 x = 0}.indicator (f 0)
            + {x : α | least_ge f r 1 x = 1}.indicator (f 0) :
  begin
    ext x,
    obtain heq | heq := nat.eq_zero_or_eq_one_of_le (@least_ge_le _ f 1 r x),
    { rw [pi.add_apply, set.indicator_of_mem, set.indicator_of_not_mem, add_zero];
      simp [heq] },
    { rw [pi.add_apply, set.indicator_of_not_mem, set.indicator_of_mem, zero_add];
      simp [heq] }
  end
        ... ≤ᵐ[μ] {x : α | least_ge f r 1 x = 0}.indicator (f 0)
            + {x : α | least_ge f r 1 x = 1}.indicator (μ[f 1|ℱ 0]) :
  begin
    refine eventually_le.add_le_add (eventually_le.refl _ _) (_ : _ ≤ᵐ[μ] _),
    filter_upwards [hf.2.1 0 1 zero_le_one] with x hx using set.indicator_le_indicator hx,
  end
        ... =ᵐ[μ] μ[{x : α | least_ge f r 1 x = 0}.indicator (f 0)|ℱ 0]
            + μ[{x : α | least_ge f r 1 x = 1}.indicator (f 1)|ℱ 0] :
  begin
    refine eventually_eq.add _ _,
    { rw (condexp_of_strongly_measurable (ℱ.le 0) _ ((hf.integrable _).indicator $
        ℱ.le _ _ ((hf.adapted.is_stopping_time_least_ge _ _).measurable_set_eq _))),
      exact strongly_measurable.indicator (hf.adapted 0)
        ((hf.adapted.is_stopping_time_least_ge _ _).measurable_set_eq _) },
    { rw (_ : {x | least_ge f r 1 x = 1} = {x : α | least_ge f r 1 x = 0}ᶜ),
      { exact (condexp_indicator (hf.integrable 1)
          ((hf.adapted.is_stopping_time_least_ge _ _).measurable_set_eq _).compl).symm },
      { ext x,
        rw [set.mem_set_of_eq, set.mem_compl_eq, set.mem_set_of_eq, ← ne.def,
          ← nat.one_le_iff_ne_zero],
        exact ⟨λ h, h.symm ▸ le_rfl, λ h, le_antisymm (least_ge_le x) h⟩ } }
  end
end

lemma aux_1 {n : ℕ} {r : ℝ} {k : ℕ} (hk : k < n) {x : α} :
  least_ge f r n x = k ↔ least_ge f r (n + 1) x = k :=
begin
  sorry,
end

lemma aux_2 (n : ℕ) {r : ℝ} {x : α} :
  least_ge f r n x = n ∧ r ≤ f n x ↔ least_ge f r (n + 1) x = n :=
begin
  sorry
end

lemma aux_3 (n : ℕ) {r : ℝ} {x : α} :
  least_ge f r n x = n ∧ ¬ r ≤ f n x ↔ least_ge f r (n + 1) x = n + 1 :=
begin
  sorry
end

lemma submartingale.stopped_value_least_ge [is_finite_measure μ]
  (hf : submartingale f ℱ μ) (r : ℝ) :
  submartingale (λ i, stopped_value f (least_ge f r i)) ℱ μ :=
begin
  classical,
  refine submartingale_nat (λ N, strongly_measurable_stopped_value_of_le
      hf.adapted.prog_measurable_of_nat
      (hf.adapted.is_stopping_time_least_ge _ _) (λ x, hitting_le _))
    (λ i, integrable_stopped_value (hf.adapted.is_stopping_time_least_ge _ _)
      hf.integrable (λ x, hitting_le _)) (λ i, _),
  by_cases hi : i = 0,
  { rw [hi, zero_add],
    exact hf.stopped_value_least_ge_zero r },
  rw [stopped_value_eq least_ge_le, finset.sum_range_succ],
  swap, { apply_instance },
  simp_rw [least_ge, hitting_eq_end_iff, imp_iff_not_or, set.set_of_or],
  rw set.indicator_union_of_disjoint,
  { have heq₁ : {x | Inf (set.Icc 0 i ∩ {i : ℕ | f i x ∈ set.Ici r}) = i} =
      {x | least_ge f r (i + 1) x = i},
    { ext x,
      rw [set.mem_set_of, set.mem_set_of, ← aux_2],
      refine ⟨λ h, _, _⟩,
      { rw [least_ge, hitting, ite_eq_right_iff],
        exact ⟨λ _, h, h ▸ (set.inter_subset_right _ _ (nat.Inf_mem $
          set.ne_empty_iff_nonempty.1 (λ hemp, hi $ h ▸ hemp.symm ▸ nat.Inf_empty)) :
          Inf (set.Icc 0 i ∩ {i | f i x ∈ set.Ici r}) ∈ {i | f i x ∈ set.Ici r})⟩ },
      { rintro ⟨h₁, h₂⟩,
        exact hitting_eq_end_iff.1 h₁ ⟨i, ⟨zero_le _, le_rfl⟩, h₂⟩ } },
    have heq₂ : {x | ¬∃ j ∈ set.Icc 0 i, f j x ∈ set.Ici r} =
      {x | least_ge f r (i + 1) x = i + 1},
    { ext x,
      rw [set.mem_set_of, set.mem_set_of, ← aux_3],
      refine ⟨λ h, ⟨if_neg h, λ hneq, h ⟨i, ⟨zero_le _, le_rfl⟩, hneq⟩⟩, _⟩,
      rintro ⟨h₁, h₂⟩ h,
      rw [least_ge, hitting_eq_end_iff] at h₁,
      rw ← h₁ h at h₂,
      exact h₂ (set.inter_subset_right _ _ (nat.Inf_mem $
        set.ne_empty_iff_nonempty.1 (λ hemp, hi $ h₁ h ▸ hemp.symm ▸ nat.Inf_empty)) :
        Inf (set.Icc 0 i ∩ {i | f i x ∈ set.Ici r}) ∈ {i | f i x ∈ set.Ici r}) },
    have heq₃ : ∑ j in finset.range i, {x | least_ge f r i x = j}.indicator (f j) =
      ∑ j in finset.range i, {x | least_ge f r (i + 1) x = j}.indicator (f j),
    { refine finset.sum_congr rfl (λ j hj, _),
      simp_rw [aux_1 (finset.mem_range.1 hj)] },
    calc ∑ j in finset.range i, {x : α | hitting f (set.Ici r) 0 i x = j}.indicator (f j)
           + (λ x, {x | ¬∃ (j : ℕ) (H : j ∈ set.Icc 0 i), f j x ∈ set.Ici r}.indicator (f i) x
           + {x | Inf (set.Icc 0 i ∩ {i : ℕ | f i x ∈ set.Ici r}) = i}.indicator (f i) x)
           = ∑ j in finset.range (i + 1), {x | least_ge f r (i + 1) x = j}.indicator (f j)
           + {x | least_ge f r (i + 1) x = i + 1}.indicator (f i) :
    begin
      rw [heq₁, heq₂, ← least_ge, heq₃, finset.sum_range_succ],
      ext x,
      simp only [pi.add_apply, finset.sum_apply],
      ring,
    end
       ... = {x | least_ge f r (i + 1) x = i + 1}.indicator (f i)
           + μ[∑ j in finset.range (i + 1), {x | least_ge f r (i + 1) x = j}.indicator (f j)|ℱ i] :
    begin
      rw add_comm,
      refine congr_arg2 _ rfl (condexp_of_strongly_measurable (ℱ.le _) _ _).symm,
      refine finset.strongly_measurable_sum' _ (λ j hj, _),
      { exact ((hf.adapted j).mono (ℱ.mono (nat.lt_succ_iff.1 $ finset.mem_range.1 hj))).indicator
          (ℱ.mono (nat.lt_succ_iff.1 $ finset.mem_range.1 hj) _
          ((hf.adapted.is_stopping_time_least_ge r (i + 1)).measurable_set_eq j)) },
      { exact integrable_finset_sum' _ (λ j hj, (hf.integrable _).indicator $
          ℱ.le j _ ((hf.adapted.is_stopping_time_least_ge r (i + 1)).measurable_set_eq j)) },
    end
       ... ≤ᵐ[μ] μ[{x | least_ge f r (i + 1) x = i + 1}.indicator (f (i + 1))|ℱ i]
           + μ[∑ j in finset.range (i + 1), {x | least_ge f r (i + 1) x = j}.indicator (f j)|ℱ i] :
    begin
      change _ ≤ᵐ[μ] _,
      refine eventually_le.add_le_add _ (eventually_le.refl _ _),
      refine eventually_le.trans _ (condexp_indicator (hf.integrable (i + 1)) _).symm.le,
      { filter_upwards [hf.2.1 i (i + 1) i.le_succ] with x hx using set.indicator_le_indicator hx },
      { rw (_ : {x | least_ge f r (i + 1) x = i + 1} = {x : α | least_ge f r (i + 1) x ≤ i}ᶜ),
        { exact ((hf.adapted.is_stopping_time_least_ge r (i + 1)) i).compl },
        { ext x,
          simp only [set.mem_set_of_eq, set.mem_compl_eq, not_le],
          exact ⟨λ h, h.symm ▸ i.lt_succ_self, λ h,
            nat.eq_of_le_of_lt_succ (nat.succ_le_iff.2 h) (nat.lt_succ_iff.2 (least_ge_le x))⟩ } }
    end
       ... =ᵐ[μ] μ[stopped_value f (least_ge f r (i + 1))|ℱ i] :
    begin
      refine (condexp_add ((hf.integrable _).indicator $ ℱ.le _ _
        ((hf.adapted.is_stopping_time_least_ge r (i + 1)).measurable_set_eq _))
        (integrable_finset_sum' _ (λ j hj, _))).symm.trans _,
      { exact (hf.integrable _).indicator (ℱ.le j _
          ((hf.adapted.is_stopping_time_least_ge r (i + 1)).measurable_set_eq j)) },
      { refine condexp_congr_ae (eventually_of_forall $ λ x, _),
        rw [stopped_value_eq least_ge_le, add_comm],
        swap, { apply_instance },
        conv_rhs { rw [finset.sum_range_succ] } }
    end },
  { rintro x ⟨hx₁, hx₂⟩,
    rw [set.mem_set_of, (_ : set.Icc 0 i ∩ {i | f i x ∈ set.Ici r} = ∅), nat.Inf_empty] at hx₂,
    { exact false.elim (hi hx₂.symm) },
    { exact set.eq_empty_of_forall_not_mem (λ j ⟨hj₁, hj₂⟩, hx₁ ⟨j, hj₁, hj₂⟩) } },
end

variables {r : ℝ} {R : ℝ≥0}

lemma norm_stopped_value_least_ge_le [is_finite_measure μ]
  {r : ℝ} (hr : 0 ≤ r) (hf : 0 ≤ f) (hbdd : ∀ᵐ x ∂μ, ∀ i, f (i + 1) x - f i x ≤ R) (i : ℕ) :
  ∀ᵐ x ∂μ, ∥stopped_value f (least_ge f r i) x∥ ≤ r + R + f 0 x :=
begin
  filter_upwards [hbdd] with x hbddx,
  change ∥f (least_ge f r i x) x∥ ≤ r + R + f 0 x,
  rw [real.norm_eq_abs, abs_of_nonneg (hf (least_ge f r i x) x)],
  by_cases heq : least_ge f r i x = 0,
  { exact heq ▸ le_add_of_nonneg_left (add_nonneg hr R.coe_nonneg) },
  { obtain ⟨k, hk⟩ := nat.exists_eq_succ_of_ne_zero heq,
    exact hk.symm ▸ (sub_le_iff_le_add.1 $ hbddx k).trans
      ((add_le_add_left (not_le.1 $ not_mem_of_lt_hitting
        (hk.symm ▸ k.lt_succ_self : k < least_ge f r i x) (zero_le _)).le _).trans
        (add_comm ↑R r ▸ le_add_of_nonneg_right (hf 0 x))) }
end

lemma stopped_value_least_ge_snorm_le [is_finite_measure μ]
  {r : ℝ} (hr : 0 ≤ r) (hf : 0 ≤ f) (hf0 : f 0 = 0)
  (hbdd : ∀ᵐ x ∂μ, ∀ i, f (i + 1) x - f i x ≤ R) (i : ℕ) :
  snorm (stopped_value f (least_ge f r i)) 1 μ ≤ μ set.univ * ennreal.of_real (r + R) :=
begin
  have hbound := norm_stopped_value_least_ge_le hr hf hbdd i,
  simp only [hf0, pi.zero_apply, add_zero] at hbound,
  refine le_trans (snorm_le_of_ae_bound hbound) _,
  rw [ennreal.one_to_real, inv_one, ennreal.rpow_one],
  exact le_rfl,
end

lemma stopped_value_least_ge_snorm_le' [is_finite_measure μ]
  {r : ℝ} (hr : 0 ≤ r) (hf : 0 ≤ f) (hf0 : f 0 = 0)
  (hbdd : ∀ᵐ x ∂μ, ∀ i, f (i + 1) x - f i x ≤ R) (i : ℕ) :
  snorm (stopped_value f (least_ge f r i)) 1 μ ≤
    ennreal.to_nnreal (μ set.univ * ennreal.of_real (r + R)) :=
begin
  refine (stopped_value_least_ge_snorm_le hr hf hf0 hbdd i).trans _,
  rw [ennreal.coe_to_nnreal (ennreal.mul_ne_top (measure_ne_top μ _) (ennreal.of_real_ne_top))],
  exact le_rfl,
end

lemma submartingale.exists_tendsto_of_bdd_above [is_finite_measure μ]
  (hf : submartingale f ℱ μ) (hlef : 0 ≤ f) (hf0 : f 0 = 0)
  (hbdd : ∀ᵐ x ∂μ, ∀ i, f (i + 1) x - f i x ≤ R) :
  ∀ᵐ x ∂μ, bdd_above (set.range $ λ n, f n x) → ∃ c, tendsto (λ n, f n x) at_top (𝓝 c) :=
begin
  have ht : ∀ᵐ x ∂μ, ∀ i : ℕ, ∃ c, tendsto (λ n, stopped_value f (least_ge f i n) x) at_top (𝓝 c),
  { rw ae_all_iff,
    exact λ i, submartingale.exists_ae_tendsto_of_bdd (hf.stopped_value_least_ge i)
      (stopped_value_least_ge_snorm_le' i.cast_nonneg hlef hf0 hbdd) },
  filter_upwards [ht] with x hx hxb,
  rw bdd_above at hxb,
  obtain ⟨i, hi⟩ := exists_nat_gt hxb.some,
  have hib : ∀ n, f n x < i,
  { intro n,
    exact lt_of_le_of_lt ((mem_upper_bounds.1 hxb.some_mem) _ ⟨n, rfl⟩) hi },
  have heq : ∀ n, stopped_value f (least_ge f i n) x = f n x,
  { intro n,
    rw [least_ge, hitting, stopped_value],
    simp only,
    rw if_neg,
    push_neg,
    exact λ j _ hj, not_le.2 (hib j) hj },
  simp only [← heq, hx i],
end
#check condexp_mono

end measure_theory
