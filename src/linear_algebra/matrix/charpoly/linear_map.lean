/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import linear_algebra.matrix.charpoly.coeff
import linear_algebra.matrix.to_lin

/-!

# Calyley-Hamilton theorem for f.g. modules.

Given a fixed finite spanning set `v : ι → M` of a `R`-module `M`, we say that a matrix `M`
represents an endomorphism `f : M →ₗ[R] M` if the matrix as an endomorphism of `ι → R` commutes
with `f` via the projection `(ι → R) →ₗ[R] M` given by `v`.

We show that every endomorphism has a matrix representation, and if `f.range ≤ I • ⊤` for some
ideal `I`, we may furthermore obtain a matrix representation whose entries fall in `I`.

This is used to conclue the Calyley-Hamilton theorem for f.g. modules over arbitrary rings.
-/

variables {ι : Type*} [decidable_eq ι] [fintype ι]
variables {M : Type*} [add_comm_group M] (R : Type*) [comm_ring R] [module R M] (I : ideal R)
variables (v : ι → M) (hv : submodule.span R (set.range v) = ⊤)

open_locale big_operators

/-- Matrices, being endomorphisms of `ι → R`, acts on `(ι → R) →ₗ[R] M`, and takes the projection
to a `(ι → R) →ₗ[R] M`.  -/
def pi_to_module.from_matrix : matrix ι ι R →ₗ[R] (ι → R) →ₗ[R] M :=
(linear_map.llcomp R _ _ _ (fintype.total ι M R v)).comp alg_equiv_matrix'.symm.to_linear_map

lemma pi_to_module.from_matrix_apply (A : matrix ι ι R) (w : ι → R) :
  pi_to_module.from_matrix R v A w = fintype.total ι M R v (A.mul_vec w) := rfl

lemma pi_to_module.from_matrix_apply_single_one (A : matrix ι ι R) (i : ι) :
  pi_to_module.from_matrix R v A (pi.single i 1) = ∑ (x : ι), A x i • v x :=
begin
  rw [pi_to_module.from_matrix_apply, fintype.total_apply, matrix.mul_vec_single],
  simp_rw [mul_one]
end

/-- The endomorphisms of `M` acts on `(ι → R) →ₗ[R] M`, and takes the projection
to a `(ι → R) →ₗ[R] M`. -/
def pi_to_module.from_End : (module.End R M) →ₗ[R] (ι → R) →ₗ[R] M :=
linear_map.lcomp _ _ (fintype.total ι M R v)

lemma pi_to_module.from_End_apply (f : module.End R M) (w : ι → R) :
  pi_to_module.from_End R v f w = f (fintype.total ι M R v w) := rfl

lemma pi_to_module.from_End_apply_single_one (f : module.End R M) (i : ι) :
  pi_to_module.from_End R v f (pi.single i 1) = f (v i) :=
begin
  rw pi_to_module.from_End_apply,
  congr,
  convert fintype.total_apply_single R i 1,
  rw one_smul,
end

lemma pi_to_module.from_End_injective (hv : submodule.span R (set.range v) = ⊤) :
  function.injective (pi_to_module.from_End R v) :=
begin
  intros x y e,
  ext m,
  obtain ⟨m, rfl⟩ : m ∈ (fintype.total ι M R v).range,
  { rw (fintype.range_total R).trans hv, trivial },
  exact (linear_map.congr_fun e m : _)
end

variables {R}

/-- We say that a matrix represents an endomorphism of `M` if the matrix acting on `ι → R` is
equal to `f ` via the projection `(ι → R) →ₗ[R] M` given by a fixed (spanning) set.  -/
def matrix_represents (A : matrix ι ι R) (f : module.End R M) : Prop :=
pi_to_module.from_matrix R v A = pi_to_module.from_End R v f

variables {v}

lemma matrix_represents.congr_fun {A : matrix ι ι R} {f : module.End R M}
  (h : matrix_represents v A f) (x) :
  fintype.total ι M R v (A.mul_vec x) = f (fintype.total ι M R v x) :=
linear_map.congr_fun h x

lemma matrix_represents.iff {A : matrix ι ι R} {f : module.End R M} :
  matrix_represents v A f ↔
    ∀ x, fintype.total ι M R v (A.mul_vec x) = f (fintype.total ι M R v x) :=
⟨λ e x, e.congr_fun x, λ H, linear_map.ext $ λ x, H x⟩

lemma matrix_represents.iff' {A : matrix ι ι R} {f : module.End R M} :
  matrix_represents v A f ↔ ∀ j, ∑ (i : ι), A i j • v i = f (v j) :=
begin
  split,
  { intros h i,
    have := linear_map.congr_fun h (pi.single i 1),
    rwa [pi_to_module.from_End_apply_single_one,
      pi_to_module.from_matrix_apply_single_one] at this },
  { intros h,
    ext,
    simp_rw [linear_map.comp_apply, linear_map.coe_single, pi_to_module.from_End_apply_single_one,
      pi_to_module.from_matrix_apply_single_one],
    apply h }
end

lemma matrix_represents.mul {A A' : matrix ι ι R} {f f' : module.End R M}
  (h : matrix_represents v A f) (h' : matrix_represents v A' f') :
  matrix_represents v (A * A') (f * f') :=
begin
  delta matrix_represents pi_to_module.from_matrix at ⊢,
  rw [linear_map.comp_apply, alg_equiv.to_linear_map_apply, map_mul],
  ext,
  dsimp [pi_to_module.from_End],
  rw [← h'.congr_fun, ← h.congr_fun],
  refl,
end

lemma matrix_represents.one : matrix_represents v (1 : matrix ι ι R) 1 :=
begin
  delta matrix_represents pi_to_module.from_matrix,
  rw [linear_map.comp_apply, alg_equiv.to_linear_map_apply, map_one],
  ext,
  refl
end

lemma matrix_represents.add {A A' : matrix ι ι R} {f f' : module.End R M}
  (h : matrix_represents v A f) (h' : matrix_represents v A' f') :
  matrix_represents v (A + A') (f + f') :=
begin
  delta matrix_represents at ⊢ h h', rw [map_add, map_add, h, h'],
end

lemma matrix_represents.zero :
  matrix_represents v (0 : matrix ι ι R) 0 :=
begin
  delta matrix_represents, rw [map_zero, map_zero],
end

lemma matrix_represents.smul {A : matrix ι ι R} {f : module.End R M}
  (h : matrix_represents v A f) (r : R) :
  matrix_represents v (r • A) (r • f) :=
begin
  delta matrix_represents at ⊢ h, rw [map_smul, map_smul, h],
end

lemma matrix_represents.eq {A : matrix ι ι R} {f f' : module.End R M}
  (h : matrix_represents v A f) (h' : matrix_represents v A f') : f = f' :=
pi_to_module.from_End_injective R v hv (h.symm.trans h')

variables [decidable_eq ι]

variables (v R)

def matrix_represents_subring : subalgebra R (matrix ι ι R) :=
{ carrier := { A | ∃ f : module.End R M, matrix_represents v A f },
  mul_mem' := λ A₁ A₂ ⟨f₁, e₁⟩ ⟨f₂, e₂⟩, ⟨f₁ * f₂, e₁.mul e₂⟩,
  one_mem' := ⟨1, matrix_represents.one⟩,
  add_mem' := λ A₁ A₂ ⟨f₁, e₁⟩ ⟨f₂, e₂⟩, ⟨f₁ + f₂, e₁.add e₂⟩,
  zero_mem' := ⟨0, matrix_represents.zero⟩,
  algebra_map_mem' := λ r, ⟨r • 1, matrix_represents.one.smul r⟩ }

noncomputable
def matrix_represents_subring.to_End : matrix_represents_subring R v →ₐ[R] module.End R M :=
{ to_fun := λ A, A.2.some,
  map_one' := (1 : matrix_represents_subring R v).2.some_spec.eq hv matrix_represents.one,
  map_mul' := λ A₁ A₂, (A₁ * A₂).2.some_spec.eq hv (A₁.2.some_spec.mul A₂.2.some_spec),
  map_zero' := (0 : matrix_represents_subring R v).2.some_spec.eq hv matrix_represents.zero,
  map_add' := λ A₁ A₂, (A₁ + A₂).2.some_spec.eq hv (A₁.2.some_spec.add A₂.2.some_spec),
  commutes' := λ r, (r • 1 : matrix_represents_subring R v).2.some_spec.eq
    hv (matrix_represents.one.smul r) }

lemma matrix_represents_subring.to_End_represents (A : matrix_represents_subring R v) :
  matrix_represents v (A : matrix ι ι R) (matrix_represents_subring.to_End R v hv A) :=
A.2.some_spec

lemma matrix_represents_subring.eq_to_End_of_represents (A : matrix_represents_subring R v)
  {f : module.End R M} (h : matrix_represents v (A : matrix ι ι R) f) :
    matrix_represents_subring.to_End R v hv A = f :=
A.2.some_spec.eq hv h

lemma matrix_represents_subring.to_End_exists_mem_ideal
  (f : module.End R M) (I : ideal R) (hI : f.range ≤ I • ⊤) :
  ∃ M, matrix_represents_subring.to_End R v hv M = f ∧ ∀ i j, M.1 i j ∈ I :=
begin
  have : ∀ x, f x ∈ (ideal.finsupp_total ι M I v).range,
  { rw [ideal.range_finsupp_total, hv], exact λ x, hI (f.mem_range_self x) },
  choose bM' hbM',
  let A : matrix ι ι R := λ i j, bM' (v j) i,
  have : matrix_represents v A f,
  { rw matrix_represents.iff',
    dsimp [A],
    intro j,
    specialize hbM' (v j),
    rwa ideal.finsupp_total_apply_eq_of_fintype at hbM' },
  exact ⟨⟨A, f, this⟩, matrix_represents_subring.eq_to_End_of_represents R v hv ⟨A, f, this⟩ this,
    λ i j, (bM' (v j) i).prop⟩,
end

lemma matrix_represents_subring.to_End_surjective :
  function.surjective (matrix_represents_subring.to_End R v hv) :=
begin
  intro f,
  obtain ⟨M, e, -⟩ := matrix_represents_subring.to_End_exists_mem_ideal R v hv f ⊤ _,
  exact ⟨M, e⟩,
  simp,
end

/--
The **Cayley-Hamilton Theorem** for f.g. modules over arbirary rings, states that for each
`R`-endomorphism `φ` of an `R`-module `M` such that `φ(M) ≤ I • M` for some ideal `I`, then there
exists some `n` and some `aᵢ ∈ Iⁱ` such that `φⁿ + a₁ φⁿ⁻¹ + ⋯ + aₙ = 0`.

This is the version found in Eisenbud 4.3, which is slightly weaker than Matsumura 2.1
(this lacks the constraint on `n`), and is slightly stonger than Atiyah-Macdonald 2.4.
-/
lemma linear_map.exists_monic_and_coeff_mem_pow_and_aeval_eq_zero_of_range_le_smul
  [module.finite R M] (f : module.End R M) (I : ideal R) (hI : f.range ≤ I • ⊤) :
  ∃ p : polynomial R, p.monic ∧
    (∀ k, p.coeff k ∈ I ^ (p.nat_degree - k)) ∧
      polynomial.aeval f p = 0 :=
begin
  classical,
  cases subsingleton_or_nontrivial R,
  { exactI ⟨0, polynomial.monic_of_subsingleton _, by simp⟩ },
  resetI,
  obtain ⟨s : finset M, hs : submodule.span R (s : set M) = ⊤⟩ := module.finite.out,
  obtain ⟨A, rfl, h⟩ := matrix_represents_subring.to_End_exists_mem_ideal R (coe : s → M)
    (by rw [subtype.range_coe_subtype, finset.set_of_mem, hs]) f I hI,
  refine ⟨A.1.charpoly, A.1.charpoly_monic, _, _⟩,
  { rw A.1.charpoly_nat_degree_eq_dim,
    exact coeff_charpoly_mem_ideal_pow h },
  { rw [polynomial.aeval_alg_hom_apply, ← map_zero (matrix_represents_subring.to_End R coe _)],
    congr' 1,
    ext1,
    rw [polynomial.aeval_subalgebra_coe, subtype.val_eq_coe, matrix.aeval_self_charpoly,
      subalgebra.coe_zero] },
  { apply_instance }
end

lemma linear_map.exists_monic_and_aeval_eq_zero [module.finite R M]
  (f : module.End R M) : ∃ p : polynomial R, p.monic ∧ polynomial.aeval f p = 0 :=
begin
  obtain ⟨p, hp₁, -, hp₂⟩ :=
    linear_map.exists_monic_and_coeff_mem_pow_and_aeval_eq_zero_of_range_le_smul R f ⊤ (by simp),
  exact ⟨p, hp₁, hp₂⟩
end
