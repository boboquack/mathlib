import ring_theory.ideal.operations
import algebra.module.torsion
import algebra.ring.idempotents
import linear_algebra.finite_dimensional
import ring_theory.ideal.local_ring
import ring_theory.nakayama

namespace ideal

variables {R S : Type*} [comm_ring R] [comm_semiring S] [algebra S R] (I : ideal R)

@[derive [add_comm_group, module (R ⧸ I)]]
def cotangent := I ⧸ (I • ⊤ : submodule R I)

instance cotangent.module_of_tower : module S I.cotangent :=
submodule.quotient.module' _

instance : is_scalar_tower S R I.cotangent := by { delta cotangent, apply_instance }

instance [is_noetherian R I] : is_noetherian R I.cotangent := by { delta cotangent, apply_instance }

@[simps apply (lemmas_only)]
def to_cotangent : I →ₗ[R] I.cotangent := submodule.mkq _

lemma map_to_cotangent_ker : I.to_cotangent.ker.map I.subtype = I ^ 2 :=
by simp [ideal.to_cotangent, submodule.map_smul'', pow_two]

lemma mem_to_cotangent_ker {x : I} : x ∈ I.to_cotangent.ker ↔ (x : R) ∈ I ^ 2 :=
begin
  rw ← I.map_to_cotangent_ker,
  simp,
end

lemma to_cotangent_eq {x y : I} : I.to_cotangent x = I.to_cotangent y ↔ (x - y : R) ∈ I ^ 2 :=
begin
  rw [← sub_eq_zero, ← map_sub],
  exact I.mem_to_cotangent_ker
end

lemma to_cotangent_eq_zero (x : I) : I.to_cotangent x = 0 ↔ (x : R) ∈ I ^ 2 :=
I.mem_to_cotangent_ker

lemma to_cotangent_surjective : function.surjective I.to_cotangent :=
submodule.mkq_surjective _

lemma cotangent_subsingleton_iff :
  subsingleton I.cotangent ↔ I = I ^ 2 :=
begin
  split,
  { introI H,
    refine antisymm _ (ideal.pow_le_self two_ne_zero),
    exact λ x hx, (I.to_cotangent_eq_zero ⟨x, hx⟩).mp (subsingleton.elim _ _) },
  { exact λ e, ⟨λ x y, quotient.induction_on₂' x y $ λ x y,
      I.to_cotangent_eq.mpr $ e ▸ I.sub_mem x.prop y.prop⟩ }
end

theorem _root_.submodule.exists_mem_and_smul_eq_self_of_fg_of_le_smul {R : Type*} [comm_ring R]
  {M : Type*} [add_comm_group M] [module R M]
  (I : ideal R) (N : submodule R M) (hn : N.fg) (hin : N ≤ I • N) :
  ∃ r ∈ I, ∀ n ∈ N, r • n = n :=
begin
  obtain ⟨r, hr, hr'⟩ := N.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul I hn hin,
  exact ⟨-(r-1), I.neg_mem hr, λ n hn, by simpa [sub_smul] using hr' n hn⟩,
end

lemma eq_square_iff_of_fg (h : I.fg) :
  I = I ^ 2 ↔ ∃ e : R, is_idempotent_elem e ∧ I = R ∙ e :=
begin
  split,
  { intro e,
    obtain ⟨r, hr, hr'⟩ := submodule.exists_mem_and_smul_eq_self_of_fg_of_le_smul I I h
      (by { rw [smul_eq_mul, ← pow_two], exact e.le }),
    simp_rw smul_eq_mul at hr',
    refine ⟨r, hr' r hr, antisymm _ ((submodule.span_singleton_le_iff_mem _ _).mpr hr)⟩,
    intros x hx,
    rw ← hr' x hx,
    exact mem_span_singleton'.mpr ⟨_, mul_comm _ _⟩ },
  { rintros ⟨e, he, rfl⟩, simp [pow_two, span_singleton_pow, he.eq] }
end

lemma eq_square_iff_eq_bot_or_top [is_domain R] (h : I.fg) :
  I = I ^ 2 ↔ I = ⊥ ∨ I = ⊤ :=
begin
  split,
  { intro H,
    obtain ⟨e, he, rfl⟩ := (I.eq_square_iff_of_fg h).mp H,
    simp only [ideal.submodule_span_eq, ideal.span_singleton_eq_bot],
    apply or_of_or_of_imp_of_imp (is_idempotent_elem.iff_eq_zero_or_one.mp he) id,
    rintro rfl,
    simp },
  { rintro (rfl|rfl); simp [pow_two] }
end

lemma _root_.submodule.is_principal.of_restrict_scalars (R : Type*) {S M : Type*} [comm_ring R] [comm_ring S] [algebra R S]
  [add_comm_group M] [module R M] [module S M]
  [is_scalar_tower R S M] (N : submodule S M) [h : (N.restrict_scalars R).is_principal] :
    N.is_principal :=
begin
  refine ⟨⟨(N.restrict_scalars R)^.is_principal.generator, le_antisymm _
    ((submodule.span_singleton_le_iff_mem _ _).mpr $ submodule.is_principal.generator_mem _)⟩⟩,
  rw [← submodule.span_span_of_tower R, submodule.is_principal.span_singleton_generator],
  exact submodule.subset_span
end

instance _root_.submodule.is_principal.map {R M₁ M₂ : Type*} [comm_ring R]
  [add_comm_group M₁] [add_comm_group M₂] [module R M₁] [module R M₂]
  (N : submodule R M₁) (f : M₁ →ₗ[R] M₂) [N.is_principal] :
    (N.map f).is_principal :=
begin
  refine ⟨⟨f N^.is_principal.generator, _⟩⟩,
  conv_lhs { rw ← N^.is_principal.span_singleton_generator },
  rw [submodule.map_span, set.image_singleton],
end

lemma _root_.submodule.is_principal.map_iff {R M₁ M₂ : Type*} [comm_ring R]
  [add_comm_group M₁] [add_comm_group M₂] [module R M₁] [module R M₂]
  (N : submodule R M₁) (f : M₁ →ₗ[R] M₂) (hf : function.injective f) :
   (N.map f).is_principal ↔ N.is_principal :=
begin
  symmetry,
  split,
  { exact λ _, by exactI infer_instance },
  { introI,
    obtain ⟨g, hg, e⟩ := (N.map f)^.is_principal.generator_mem,
  refine ⟨⟨g, _⟩⟩,
  rw [← (submodule.map_injective_of_injective hf).eq_iff, submodule.map_span, set.image_singleton,
    e, submodule.is_principal.span_singleton_generator] }
end

instance cotangent_is_principal [I.is_principal] :
  (⊤ : submodule (R ⧸ I) I.cotangent).is_principal :=
begin
  apply_with (submodule.is_principal.of_restrict_scalars R) { instances := ff },
  rw [submodule.restrict_scalars_top,
    ← linear_map.range_eq_top.mpr (submodule.mkq_surjective _), ← submodule.map_top],
  any_goals { apply_instance },
  apply_with submodule.is_principal.map { instances := ff },
  rw ← submodule.is_principal.map_iff _ _ I.injective_subtype,
  simpa
end

end ideal

attribute [mk_iff] submodule.is_principal

lemma submodule.rank_le_one_iff_is_principal {R M : Type*} [division_ring R] [add_comm_group M] [module R M]
  (N : submodule R M) :
  module.rank R N ≤ 1 ↔ N.is_principal :=
begin
  rw dim_le_one_iff,
  split,
  { rintro ⟨m, hm⟩,
    refine ⟨⟨m, le_antisymm _ ((submodule.span_singleton_le_iff_mem _ _).mpr m.prop)⟩⟩,
    intros x hx,
    obtain ⟨r, hr⟩ := hm ⟨x, hx⟩,
    exact submodule.mem_span_singleton.mpr ⟨r, congr_arg subtype.val hr⟩ },
  { rintro ⟨⟨a, rfl⟩⟩,
    refine ⟨⟨a, submodule.mem_span_singleton_self a⟩, _⟩,
    rintro ⟨m, hm⟩,
    obtain ⟨r, hr⟩ := submodule.mem_span_singleton.mp hm,
    exact ⟨r, subtype.ext hr⟩ }
end

lemma module.rank_le_one_iff_top_is_principal {R M : Type*} [division_ring R] [add_comm_group M]
  [module R M] :
  module.rank R M ≤ 1 ↔ (⊤ : submodule R M).is_principal :=
by rw [← submodule.rank_le_one_iff_is_principal, dim_top]

lemma submodule.finrank_le_one_iff_is_principal {R M : Type*}
  [division_ring R] [add_comm_group M] [module R M] (N : submodule R M) [finite_dimensional R N] :
  finite_dimensional.finrank R N ≤ 1 ↔ N.is_principal :=
by rw [← N.rank_le_one_iff_is_principal, ← finite_dimensional.finrank_eq_dim,
  ← cardinal.nat_cast_le, nat.cast_one]

lemma module.finrank_le_one_iff_top_is_principal {R M : Type*} [division_ring R] [add_comm_group M]
  [module R M] [finite_dimensional R M] :
  finite_dimensional.finrank R M ≤ 1 ↔ (⊤ : submodule R M).is_principal :=
by rw [← module.rank_le_one_iff_top_is_principal, ← finite_dimensional.finrank_eq_dim,
  ← cardinal.nat_cast_le, nat.cast_one]

namespace local_ring

variables (R : Type*) [comm_ring R] [local_ring R]

abbreviation cotangent_space : Type* := (maximal_ideal R).cotangent

instance : module (residue_field R) (cotangent_space R) :=
ideal.cotangent.module _

instance : is_scalar_tower R (residue_field R) (cotangent_space R) :=
module.is_torsion_by_set.is_scalar_tower _

instance [is_noetherian_ring R] : finite_dimensional (residue_field R) (cotangent_space R) :=
module.finite.of_restrict_scalars_finite R _ _

lemma _root_.ring.is_field_iff_eq_bot_of_is_maximal (R : Type*) [comm_ring R] [nontrivial R] {M : ideal R} [h : M.is_maximal] :
  is_field R ↔ M = ⊥ :=
begin
  split,
  { intro H, letI := H.to_field, exact M.eq_bot_of_prime },
  { intro e, by_contra h', exact ring.ne_bot_of_is_maximal_of_not_is_field h h' e },
end

lemma dim_cotangent_space_eq_zero_iff [is_domain R] [is_noetherian_ring R] :
  finite_dimensional.finrank (residue_field R) (cotangent_space R) = 0 ↔ is_field R :=
by rw [finite_dimensional.finrank_zero_iff, ideal.cotangent_subsingleton_iff,
    ideal.eq_square_iff_eq_bot_or_top _ (is_noetherian.noetherian _),
    or_iff_left (maximal_ideal.is_maximal R).ne_top, ← ring.is_field_iff_eq_bot_of_is_maximal];
  apply_instance
lemma _root_.submodule.map_smul_top {M : Type*} [add_comm_monoid M] [module R M]
  (I : ideal R) (N : submodule R M) (x : N) : submodule.map N.subtype (I • ⊤) = I • N :=
by rw [submodule.map_smul'', submodule.map_top, submodule.range_subtype]

lemma _root_.submodule.mem_smul_top_iff {M : Type*} [add_comm_monoid M] [module R M]
  (I : ideal R) (N : submodule R M) (x : N) : x ∈ I • (⊤ : submodule R N) ↔ (x : M) ∈ I • N :=
begin
  change _ ↔ N.subtype x ∈ I • N,
  have : submodule.map N.subtype (I • ⊤) = I • N,
  { rw [submodule.map_smul'', submodule.map_top, submodule.range_subtype] },
  rw ← this,
  convert (function.injective.mem_set_image N.injective_subtype).symm using 1,
  refl,
end
lemma local_ring.jacobson_eq_maximal_ideal (I : ideal R) (h : I ≠ ⊤) :
  I.jacobson = local_ring.maximal_ideal R :=
begin
  apply le_antisymm,
  { exact Inf_le ⟨local_ring.le_maximal_ideal h, local_ring.maximal_ideal.is_maximal R⟩ },
  { exact le_Inf (λ J (hJ : I ≤ J ∧ J.is_maximal),
      le_of_eq (local_ring.eq_maximal_ideal hJ.2).symm) }
end
lemma foobar {R M : Type*} [comm_ring R] [add_comm_group M] [module R M]
  (I : ideal R) (hI : I ≤ (⊥ : ideal R).jacobson) (N : submodule R M) (hN : N.fg)
    [h : (⊤ : submodule (R ⧸ I) (N ⧸ I • (⊤ : submodule R N))).is_principal] :
    N.is_principal :=
begin
  unfreezingI { obtain ⟨x, hx'⟩ := h },
  obtain ⟨x, rfl⟩ := submodule.mkq_surjective _ x,
  rw [← set.image_singleton, ← submodule.restrict_scalars_inj R,
    submodule.restrict_scalars_top, ← submodule.span_eq_restrict_scalars,
    ← submodule.map_span, eq_comm, submodule.map_mkq_eq_top,
    ← (submodule.map_injective_of_injective N.injective_subtype).eq_iff,
    submodule.map_sup, submodule.map_smul'', submodule.map_top, submodule.range_subtype,
    submodule.map_span, set.image_singleton, N.subtype_apply] at hx',
  have : submodule.span R {↑x} ⊔ N = submodule.span R {↑x} ⊔ I • N,
  { rw [@sup_comm _ _ _ (I • N), hx', sup_eq_right], exact le_sup_right.trans hx'.le },
  have := submodule.smul_sup_eq_smul_sup_of_le_smul_of_le_jacobson hN hI this.le,
  rw [submodule.bot_smul, sup_bot_eq, sup_eq_left] at this,
  rw sup_eq_right.mpr this at hx',
  exacts [⟨⟨x, hx'.symm⟩⟩, ideal.quotient.mk_surjective],
end


lemma dim_cotangent_space_eq_one_iff [is_domain R] [is_noetherian_ring R] :
  finite_dimensional.finrank (residue_field R) (cotangent_space R) ≤ 1 ↔
    (maximal_ideal R).is_principal :=
begin
  rw module.finrank_le_one_iff_top_is_principal,
  split,
  { rintro ⟨x, hx'⟩,
    obtain ⟨x, rfl⟩ := submodule.mkq_surjective _ x,
    rw [← set.image_singleton, ← submodule.restrict_scalars_inj R,
      submodule.restrict_scalars_top, ← submodule.span_eq_restrict_scalars,
      ← submodule.map_span, eq_comm, submodule.map_mkq_eq_top] at hx',
    have := submodule.span_eq_restrict_scalars,
    -- ← submodule.span_span_of_tower R,
      -- ← submodule.map_span
  --   -- change _ = submodule.span _ ({submodule.mk} : set (cotangent_space R)),
  --   use x,
  --   apply le_antisymm,
  --   swap, { rw [submodule.span_le, set.singleton_subset_iff], exact x.prop },
  --   have h₁ : (ideal.span {x} : ideal R) ⊔ maximal_ideal R ≤
  --     ideal.span {x} ⊔ (maximal_ideal R) • (maximal_ideal R),
  --   { refine sup_le le_sup_left _,
  --     rintros m hm,
  --     obtain ⟨c, hc⟩ := submodule.mem_span_singleton.mp ((hx'.le : _) (show submodule.quotient.mk
  --     (⟨m, hm⟩ : maximal_ideal R) ∈ ⊤, by triv)),
  --     induction c using quotient.induction_on',
  --     rw ← sub_sub_cancel (c * x) m,
  --     apply sub_mem _ _,
  --     { apply_instance },
  --     { refine ideal.mem_sup_left (ideal.mem_span_singleton'.mpr ⟨c, rfl⟩) },
  --     { have := (submodule.quotient.eq _).mp hc,
  --       rw submodule.mem_smul_top_iff at this,
  --       exact ideal.mem_sup_right this } },
  --   have h₂ : maximal_ideal R ≤ (⊥ : ideal R).jacobson,
  --   { rw local_ring.jacobson_eq_maximal_ideal, exacts [le_refl _, bot_ne_top] },
  --   have := submodule.smul_sup_eq_smul_sup_of_le_smul_of_le_jacobson
  --     (is_noetherian.noetherian _) h₂ h₁,
  --   rw [submodule.bot_smul, sup_bot_eq] at this,
  --   rw [← sup_eq_left, eq_comm],
    -- exact le_sup_left.antisymm (h₁.trans $ le_of_eq this)
     },
  { introI, apply_instance }
end


end local_ring
