import ring_theory.valuation.valuation_subring
import ring_theory.integrally_closed
import linear_algebra.quotient
import ring_theory.nakayama

.

variables (R : Type*) [comm_ring R] (K : Type*) [field K]
variables [algebra R K] [is_fraction_ring R K]

lemma valuation_ring.of_surjective {R S : Type*} [comm_ring R] [is_domain R]
  [valuation_ring R] [comm_ring S] [is_domain S] (f : R →+* S) (hf : function.surjective f) :
    valuation_ring S :=
⟨λ a b, begin
  obtain ⟨⟨a, rfl⟩, ⟨b, rfl⟩⟩ := ⟨hf a, hf b⟩,
  obtain ⟨c, rfl|rfl⟩ := valuation_ring.cond a b,
  exacts [⟨f c, or.inl $ (map_mul _ _ _).symm⟩, ⟨f c, or.inr $ (map_mul _ _ _).symm⟩],
end⟩

lemma valuation_ring.iff_div_total [is_domain R] :
  valuation_ring R ↔ is_total R (∣) :=
begin
  classical,
  refine ⟨λ H, ⟨λ a b, _⟩, λ H, ⟨λ a b, _⟩⟩; resetI,
  { obtain ⟨c,rfl|rfl⟩ := @@valuation_ring.cond _ _ H a b; simp },
  { obtain (⟨c, rfl⟩|⟨c, rfl⟩) := @is_total.total _ _ H a b; use c; simp }
end

lemma valuation_ring.iff_total [is_domain R] :
  valuation_ring R ↔ is_total (ideal R) (≤) :=
begin
  classical,
  refine ⟨λ _, by exactI ⟨le_total⟩, λ H, (valuation_ring.iff_div_total R).mpr ⟨λ a b, _⟩⟩,
  have := @is_total.total _ _ H (ideal.span {a}) (ideal.span {b}),
  simp_rw ideal.span_singleton_le_span_singleton at this,
  exact this.symm
end

lemma submodule.fg_induction (R M : Type*) [semiring R] [add_comm_monoid M] [module R M]
  (P : submodule R M → Prop)
  (h₁ : ∀ x, P (submodule.span R {x})) (h₂ : ∀ M₁ M₂, P M₁ → P M₂ → P (M₁ ⊔ M₂))
  (N : submodule R M) (hN : N.fg) : P N :=
begin
  classical,
  obtain ⟨s, rfl⟩ := hN,
  induction s using finset.induction,
  { rw [finset.coe_empty, submodule.span_empty, ← submodule.span_zero_singleton], apply h₁ },
  { rw [finset.coe_insert, submodule.span_insert], apply h₂; apply_assumption }
end

class is_bezout : Prop :=
(is_principal_of_fg : ∀ I : ideal R, I.fg → I.is_principal)

lemma is_bezout.span_pair_is_principal {R : Type*} [comm_ring R] [is_bezout R] (x y : R) :
  (ideal.span {x, y} : ideal R).is_principal :=
by { classical, exact is_bezout.is_principal_of_fg (ideal.span {x, y}) ⟨{x, y}, by simp⟩ }

lemma is_bezout_iff_sup_span_singleton :
  is_bezout R ↔ (∀ x y : R, (ideal.span {x} ⊔ ideal.span {y} : ideal R).is_principal) :=
begin
  classical,
  split,
  { introsI H x y,
    rw ← ideal.span_insert,
    apply is_bezout.span_pair_is_principal },
  { intro H,
    constructor,
    apply submodule.fg_induction,
    { exact λ _, ⟨⟨_, rfl⟩⟩ },
    { rintro _ _ ⟨⟨x, rfl⟩⟩ ⟨⟨y, rfl⟩⟩, exact H _ _ } },
end

noncomputable
def is_bezout.gcd {R : Type*} [comm_ring R] [is_bezout R]  (x y : R) : R :=
(is_bezout.span_pair_is_principal x y).1.some

lemma is_bezout.gcd_prop {R : Type*} [comm_ring R] [is_bezout R] (x y : R) :
  (ideal.span {is_bezout.gcd x y} : ideal R) = ideal.span {x, y} :=
(is_bezout.span_pair_is_principal x y).1.some_spec.symm

lemma is_bezout.gcd_dvd_left {R : Type*} [comm_ring R] [is_bezout R] (x y : R) :
  is_bezout.gcd x y ∣ x :=
ideal.span_singleton_le_span_singleton.mp
  (by { rw is_bezout.gcd_prop, apply ideal.span_mono, simp })

lemma is_bezout.gcd_dvd_right {R : Type*} [comm_ring R] [is_bezout R] (x y : R) :
  is_bezout.gcd x y ∣ y :=
ideal.span_singleton_le_span_singleton.mp
  (by { rw is_bezout.gcd_prop, apply ideal.span_mono, simp })

lemma is_bezout.dvd_gcd {R : Type*} [comm_ring R] [is_bezout R] {x y z : R}
  (hx : z ∣ x) (hy : z ∣ y) : z ∣ is_bezout.gcd x y :=
begin
  rw [← ideal.span_singleton_le_span_singleton] at hx hy ⊢,
  rw [is_bezout.gcd_prop, ideal.span_insert, sup_le_iff],
  exact ⟨hx, hy⟩
end

lemma is_bezout.gcd_eq_sum {R : Type*} [comm_ring R] [is_bezout R] (x y : R) :
  ∃ a b : R, a * x + b * y = is_bezout.gcd x y :=
ideal.mem_span_pair.mp (by { rw ← is_bezout.gcd_prop, apply ideal.subset_span, simp })

noncomputable
def is_bezout.to_gcd_domain (R : Type*) [comm_ring R] [is_domain R] [is_bezout R] [decidable_eq R] :
  gcd_monoid R :=
gcd_monoid_of_gcd is_bezout.gcd is_bezout.gcd_dvd_left is_bezout.gcd_dvd_right
  (λ _ _ _, is_bezout.dvd_gcd)

instance gcd_monoid.to_unique_factorization_monoid [is_domain R] [is_noetherian_ring R]
  [gcd_monoid R] : unique_factorization_monoid R :=
ufm_of_gcd_of_wf_dvd_monoid

lemma valuation_ring.dvd_total {R : Type*} [comm_ring R] [is_domain R] [h : valuation_ring R] (x y : R) :
  x ∣ y ∨ y ∣ x := @@is_total.total _ ((valuation_ring.iff_div_total R).mp h) x y

lemma valuation_ring.unique_irreducible {R : Type*} [comm_ring R] [is_domain R] [valuation_ring R] ⦃p q : R⦄
  (hp : irreducible p) (hq : irreducible q) : associated p q :=
begin
  have := valuation_ring.dvd_total p q,
  rw [irreducible.dvd_comm hp hq, or_self] at this,
  exact associated_of_dvd_dvd (irreducible.dvd_symm hq hp this) this,
end

instance valuation_ring.is_bezout [is_domain R] [valuation_ring R] : is_bezout R :=
begin
  classical,
  rw is_bezout_iff_sup_span_singleton R,
  intros x y,
  cases le_total (ideal.span {x} : ideal R) (ideal.span {y}),
  { erw sup_eq_right.mpr h, exact ⟨⟨_, rfl⟩⟩ },
  { erw sup_eq_left.mpr h, exact ⟨⟨_, rfl⟩⟩ }
end

lemma valuation_ring.iff_local_bezout_domain [is_domain R] :
  valuation_ring R ↔ local_ring R ∧ is_bezout R :=
begin
  classical,
  split,
  { introI H, exact ⟨infer_instance, infer_instance⟩ },
  { rintro ⟨h₁, h₂⟩,
    resetI,
    refine (valuation_ring.iff_div_total R).mpr ⟨λ a b, _⟩,
    obtain ⟨g, e : _ = ideal.span _⟩ := is_bezout.span_pair_is_principal a b,
    obtain ⟨a, rfl⟩ := ideal.mem_span_singleton'.mp
      (show a ∈ ideal.span {g}, by { rw [← e], exact ideal.subset_span (by simp) }),
    obtain ⟨b, rfl⟩ := ideal.mem_span_singleton'.mp
      (show b ∈ ideal.span {g}, by { rw [← e], exact ideal.subset_span (by simp) }),
    obtain ⟨x, y, e'⟩ := ideal.mem_span_pair.mp
      (show g ∈ ideal.span {a * g, b * g}, by { rw e, exact ideal.subset_span (by simp) }),
    cases eq_or_ne g 0 with h h, { simp [h] },
    have : x * a + y * b = 1,
    { apply mul_left_injective₀ h, convert e'; ring_nf },
    cases local_ring.is_unit_or_is_unit_of_add_one this with h' h',
    left, swap, right,
    all_goals
    { exact mul_dvd_mul_right (is_unit_iff_forall_dvd.mp (is_unit_of_mul_is_unit_right h') _) _ } },
end
.


open_locale discrete_valuation
open local_ring

variables (M : Type*) [add_comm_group M] [module R M] (I : ideal R)

def ideal.quotient_module_of_le_ann (h : I ≤ (⊤ : submodule R M).annihilator) :
  module (R ⧸ I) M :=
{ smul := λ r m, r.lift_on' (• m) (λ r s e, begin
    have : (r - s) • m = 0,
    { injection linear_map.congr_fun (h (I.quotient_rel_r_def.mp e)) ⟨m, trivial⟩ },
    rwa [sub_smul, sub_eq_zero] at this
  end),
  one_smul := λ m, one_smul R m,
  mul_smul := λ x y b, quotient.induction_on₂' x y $ λ _ _, mul_smul _ _ _,
  smul_add := λ x a b, quotient.induction_on' x $ λ _, smul_add _ _ _,
  smul_zero := λ x, quotient.induction_on' x $ λ _, smul_zero _,
  add_smul := λ x y b, quotient.induction_on₂' x y $ λ _ _, add_smul _ _ _,
  zero_smul := λ m, zero_smul R m }

instance ideal.quotient_is_scalar_tower_of_le_ann (h : I ≤ (⊤ : submodule R M).annihilator) :
  @@is_scalar_tower R (R ⧸ I) M _ (ideal.quotient_module_of_le_ann R M I h).to_has_scalar _ :=
{ smul_assoc := λ r y m, quotient.induction_on' y $ λ y, mul_smul _ _ _ }

instance : module (R ⧸ I) (M ⧸ I • (⊤ : submodule R M)) :=
ideal.quotient_module_of_le_ann R _ I (λ r hr, begin
  ext ⟨x, _⟩,
  dsimp, clear_,
  induction x using quotient.induction_on,
  refine (submodule.quotient.mk_eq_zero _).mpr (submodule.smul_mem_smul hr _),
  trivial,
end)

instance : is_scalar_tower R (R ⧸ I) (M ⧸ I • (⊤ : submodule R M)) := infer_instance

local attribute[reducible] residue_field

@[derive [add_comm_group, module R, module (residue_field R),
  is_scalar_tower R (residue_field R)]]
def local_ring.vector_space [local_ring R] : Type* :=
  maximal_ideal R ⧸ maximal_ideal R • (⊤ : submodule R (maximal_ideal R))

lemma valuation_ring.exists_algebra_map_eq [is_domain R] [valuation_ring R] (x : K) :
  ∃ c : R, algebra_map R K c = x ∨ algebra_map R K c = x⁻¹ :=
begin
  obtain ⟨x : R, y, hy, rfl⟩ := is_fraction_ring.div_surjective x,
  any_goals { apply_instance },
  have := (map_ne_zero_iff _ (is_fraction_ring.injective R K)).mpr (non_zero_divisors.ne_zero hy),
  obtain ⟨s, rfl|rfl⟩ := valuation_ring.cond x y,
  { exact ⟨s, or.inr $ eq_inv_of_mul_eq_one_left $
      by rwa [mul_div, div_eq_one_iff_eq, map_mul, mul_comm]⟩ },
  { exact ⟨s, or.inl $ by rwa [eq_div_iff, map_mul, mul_comm]⟩ }
end

open_locale big_operators

instance valuation_ring.is_integrally_closed [is_domain R] [valuation_ring R] :
  is_integrally_closed R :=
begin
  constructor,
  rintro x ⟨p, hp₁, hp₂⟩,
  change x ∈ (algebra_map R (fraction_ring R)).range,
  obtain ⟨c, rfl|e⟩ := valuation_ring.exists_algebra_map_eq R _ x,
  { exact ⟨c, rfl⟩ },
  by_cases x = 0, { exact ⟨0, (map_zero _).trans h.symm⟩ },
  have hp₃ : 1 ≤ p.nat_degree,
  { rw nat.one_le_iff_ne_zero,
    by_contra hp₃,
    have := polynomial.eq_C_of_nat_degree_eq_zero hp₃,
    rw [this, ← hp₃, hp₁.coeff_nat_degree] at hp₂,
    exfalso,
    simpa using hp₂ },
  have := p.sum_monomial_eq.symm.trans (p.sum_over_range $ λ _, map_zero _),
  rw [finset.sum_range_succ, hp₁.coeff_nat_degree] at this,
  rw this at hp₂,
  rw ← mul_right_inj' (pow_ne_zero (p.nat_degree - 1) (inv_ne_zero h)) at hp₂,
  simp only [polynomial.eval₂_add, polynomial.eval₂_monomial, map_one, one_mul,
    polynomial.eval₂_finset_sum, mul_zero, mul_add, finset.mul_sum] at hp₂,
  nth_rewrite 2 ← tsub_add_cancel_of_le hp₃ at hp₂,
  rw [pow_add, pow_one, ← mul_assoc _ _ x, ← mul_pow, inv_mul_cancel h, one_pow, one_mul,
    add_eq_zero_iff_neg_eq] at hp₂,
  rw ← hp₂,
  apply neg_mem,
  apply sum_mem,
  intros c hc,
  rw [mul_comm, mul_assoc],
  apply mul_mem (ring_hom.mem_range_self _ _),
  rw finset.mem_range at hc,
  rw [← tsub_add_cancel_of_le ((nat.le_sub_iff_right hp₃).mpr (nat.succ_le_of_lt hc)),
    pow_add, mul_comm, mul_assoc, ← mul_pow, inv_mul_cancel h, ← e, one_pow, mul_one, ← map_pow],
  exact ring_hom.mem_range_self _ _,
  apply_instance
end

lemma local_ring.jacobson_eq_maximal_ideal [local_ring R] (h : I ≠ ⊤) :
  I.jacobson = local_ring.maximal_ideal R :=
begin
  apply le_antisymm,
  { exact Inf_le ⟨local_ring.le_maximal_ideal h, local_ring.maximal_ideal.is_maximal R⟩ },
  { exact le_Inf (λ J (hJ : I ≤ J ∧ J.is_maximal),
      le_of_eq (local_ring.eq_maximal_ideal hJ.2).symm) }
end

lemma submodule.mem_smul_top_iff {M : Type*} [add_comm_monoid M] [module R M]
  (I : ideal R) (N : submodule R M) (x : N) : x ∈ I • (⊤ : submodule R N) ↔ (x : M) ∈ I • N :=
begin
  change _ ↔ N.subtype x ∈ I • N,
  have : submodule.map N.subtype (I • ⊤) = I • N,
  { rw [submodule.map_smul'', submodule.map_top, submodule.range_subtype] },
  rw ← this,
  convert (function.injective.mem_set_image N.injective_subtype).symm using 1,
  refl,
end

theorem irreducible_of_span_eq_maximal_ideal {R : Type*} [comm_ring R] [local_ring R] [is_domain R]
  (ϖ : R) (hϖ : ϖ ≠ 0) (h : ideal.span {ϖ} = maximal_ideal R) : irreducible ϖ :=
begin
  have h2 : ¬(is_unit ϖ) := show ϖ ∈ maximal_ideal R,
    from h ▸ submodule.mem_span_singleton_self ϖ,
  refine ⟨h2, _⟩,
  intros a b hab,
  by_contra' h,
  obtain ⟨ha : a ∈ maximal_ideal R, hb : b ∈ maximal_ideal R⟩ := h,
  rw [← h, ideal.mem_span_singleton'] at ha hb,
  rcases ha with ⟨a, rfl⟩,
  rcases hb with ⟨b, rfl⟩,
  rw (show a * ϖ * (b * ϖ) = ϖ * (ϖ * (a * b)), by ring) at hab,
  apply hϖ,
  apply eq_zero_of_mul_eq_self_right _ hab.symm,
  exact λ hh, h2 (is_unit_of_dvd_one ϖ ⟨_, hh.symm⟩)
end

lemma exists_maximal_ideal_pow_eq_of_principal [is_noetherian_ring R] [local_ring R] [is_domain R]
  (h : ¬ is_field R) (h' : (maximal_ideal R).is_principal) (I : ideal R) (hI : I ≠ ⊥) :
    ∃ n : ℕ, I = (maximal_ideal R) ^ n :=
begin
  unfreezingI { obtain ⟨x, hx : _ = ideal.span _⟩ := h' },
  by_cases hI' : I = ⊤, { use 0, rw [pow_zero, hI', ideal.one_eq_top] },
  have H : ∀ r : R, ¬ (is_unit r) ↔ x ∣ r :=
    λ r, (set_like.ext_iff.mp hx r).trans ideal.mem_span_singleton,
  have : x ≠ 0,
  { rintro rfl,
    apply ring.ne_bot_of_is_maximal_of_not_is_field (maximal_ideal.is_maximal R) h,
    simp [hx] },
  have hx' : irreducible x := irreducible_of_span_eq_maximal_ideal x this hx.symm,
  have H' : ∀ r : R, r ≠ 0 → r ∈ nonunits R → ∃ (n : ℕ), associated (x ^ n) r,
  { intros r hr₁ hr₂,
    obtain ⟨f, hf₁, rfl, hf₂⟩ := (wf_dvd_monoid.not_unit_iff_exists_factors_eq r hr₁).mp hr₂,
    have : ∀ b ∈ f, associated x b,
    { intros b hb,
      exact irreducible.associated_of_dvd hx' (hf₁ b hb) ((H b).mp (hf₁ b hb).1) },
    clear hr₁ hr₂ hf₁,
    induction f using multiset.induction with fa fs fh,
    { exact (hf₂ rfl).elim },
    rcases eq_or_ne fs ∅ with rfl|hf',
    { use 1,
      rw [pow_one, multiset.prod_cons, multiset.empty_eq_zero, multiset.prod_zero, mul_one],
      exact this _ (multiset.mem_cons_self _ _) },
    { obtain ⟨n, hn⟩ := fh hf' (λ b hb, this _ (multiset.mem_cons_of_mem hb)),
      use n + 1,
      rw [pow_add, multiset.prod_cons, mul_comm, pow_one],
      exact associated.mul_mul (this _ (multiset.mem_cons_self _ _)) hn } },
  have : ∃ n : ℕ, x ^ n ∈ I,
  { obtain ⟨r, hr₁, hr₂⟩ : ∃ r : R, r ∈ I ∧ r ≠ 0,
    { by_contra h, push_neg at h, apply hI, rw eq_bot_iff, exact h },
    obtain ⟨n, u, rfl⟩ := H' r hr₂ (le_maximal_ideal hI' hr₁),
    use n,
    rwa [← I.unit_mul_mem_iff_mem u.is_unit, mul_comm] },
  use nat.find this,
  apply le_antisymm,
  { change ∀ s ∈ I, s ∈ _,
    by_contra hI'',
    push_neg at hI'',
    obtain ⟨s, hs₁, hs₂⟩ := hI'',
    apply hs₂,
    by_cases hs₃ : s = 0, { rw hs₃, exact zero_mem _ },
    obtain ⟨n, u, rfl⟩ := H' s hs₃ (le_maximal_ideal hI' hs₁),
    rw [mul_comm, ideal.unit_mul_mem_iff_mem _ u.is_unit] at ⊢ hs₁,
    apply ideal.pow_le_pow (nat.find_min' this hs₁),
    apply ideal.pow_mem_pow,
    exact (H _).mpr (dvd_refl _) },
  { rw [hx, ideal.span_singleton_pow, ideal.span_le, set.singleton_subset_iff],
    exact nat.find_spec this }
end

lemma discrete_valuation_ring.tfae [is_noetherian_ring R] [local_ring R] [is_domain R]
  (h : ¬ is_field R) :
  tfae [discrete_valuation_ring R,
    valuation_ring R,
    is_integrally_closed R ∧ ∃! P : ideal R, P ≠ ⊥ ∧ P.is_prime, -- integrally closed with dim = 1
    (maximal_ideal R).is_principal,
    finite_dimensional.finrank (residue_field R) (local_ring.vector_space R) = 1,
    ∀ I ≠ ⊥, ∃ n : ℕ, I = (maximal_ideal R) ^ n] :=
begin
  rw finrank_eq_one_iff',
  tfae_have : 1 → 2,
  { introI _, apply_instance },
  tfae_have : 2 → 1,
  { introI _,
    haveI := is_bezout.to_gcd_domain R,
    apply discrete_valuation_ring.of_ufd_of_unique_irreducible,
    { obtain ⟨x, hx₁, hx₂⟩ := ring.exists_not_is_unit_of_not_is_field h,
      obtain ⟨p, hp₁, hp₂⟩ := wf_dvd_monoid.exists_irreducible_factor hx₂ hx₁,
      exact ⟨p, hp₁⟩ },
    { exact valuation_ring.unique_irreducible } },
  tfae_have : 1 → 3,
  { introI H,
    exact ⟨infer_instance, ((discrete_valuation_ring.iff_pid_with_one_nonzero_prime R).mp H).2⟩ },
  tfae_have : 3 → 4,
  { sorry },
  tfae_have : 4 → 5,
  { rintro ⟨x, hx⟩,
    have : x ∈ maximal_ideal R := by { rw hx, exact submodule.subset_span (set.mem_singleton x) },
    let x' : maximal_ideal R := ⟨x, this⟩,
    use submodule.quotient.mk x',
    split,
    { intro e,
      rw submodule.quotient.mk_eq_zero at e,
      apply ring.ne_bot_of_is_maximal_of_not_is_field (maximal_ideal.is_maximal R) h,
      apply submodule.eq_bot_of_le_smul_of_le_jacobson_bot (maximal_ideal R),
      { exact ⟨{x}, (finset.coe_singleton x).symm ▸ hx.symm⟩ },
      { conv_lhs { rw hx },
        rw submodule.mem_smul_top_iff at e,
        rwa [submodule.span_le, set.singleton_subset_iff] },
      { rw local_ring.jacobson_eq_maximal_ideal _ _ _,
        exacts [le_refl _, bot_ne_top] } },
    { refine λ _w, quotient.induction_on' _w $ λ y, _,
      obtain ⟨y, hy⟩ := y,
      rw [hx, submodule.mem_span_singleton] at hy,
      obtain ⟨a, rfl⟩ := hy,
      exact ⟨ideal.quotient.mk _ a, rfl⟩ } },
  tfae_have : 5 → 4,
  { rintro ⟨x, hx, hx'⟩,
    induction x using quotient.induction_on',
    use x,
    apply le_antisymm,
    swap, { rw [submodule.span_le, set.singleton_subset_iff], exact x.prop },
    have h₁ : (ideal.span {x} : ideal R) ⊔ maximal_ideal R ≤
      ideal.span {x} ⊔ (maximal_ideal R) • (maximal_ideal R),
    { refine sup_le le_sup_left _,
      rintros m hm,
      obtain ⟨c, hc⟩ := hx' (submodule.quotient.mk ⟨m, hm⟩),
      induction c using quotient.induction_on',
      rw ← sub_sub_cancel (c * x) m,
      apply sub_mem _ _,
      { apply_instance },
      { refine ideal.mem_sup_left (ideal.mem_span_singleton'.mpr ⟨c, rfl⟩) },
      { have := (submodule.quotient.eq _).mp hc,
        rw [submodule.mem_smul_top_iff] at this,
        exact ideal.mem_sup_right this } },
    have h₂ : maximal_ideal R ≤ (⊥ : ideal R).jacobson,
    { rw local_ring.jacobson_eq_maximal_ideal, exacts [le_refl _, bot_ne_top] },
    have := submodule.smul_sup_eq_smul_sup_of_le_smul_of_le_jacobson
      (is_noetherian.noetherian _) h₂ h₁,
    rw [submodule.bot_smul, sup_bot_eq] at this,
    rw [← sup_eq_left, eq_comm],
    exact le_sup_left.antisymm (h₁.trans $ le_of_eq this) },
  tfae_have : 4 → 6,
  { exact exists_maximal_ideal_pow_eq_of_principal R h },
  tfae_have : 6 → 2,
  { rw valuation_ring.iff_total,
    intro H,
    constructor,
    intros I J,
    by_cases hI : I = ⊥, { subst hI,  left, exact bot_le },
    by_cases hJ : J = ⊥, { subst hJ, right, exact bot_le },
    obtain ⟨n, rfl⟩ := H I hI,
    obtain ⟨m, rfl⟩ := H J hJ,
    cases le_total m n with h' h',
    {  left, exact ideal.pow_le_pow h' },
    { right, exact ideal.pow_le_pow h' } },
  tfae_finish,
end
