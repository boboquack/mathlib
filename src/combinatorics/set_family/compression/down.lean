/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import combinatorics.set_family.compression.basic
import data.fintype.basic

/-!
# Down-compressions

This file defines down-compression. It is an operation on a set family that reduces the number of
sets it shatters.

Down-compressing `𝒜 : finset (finset α)` along `a : α` means removing `a` from the elements of `𝒜`,
when the resulting set is not already in `𝒜`.

## Main declarations

* `finset.non_member_section`: `𝒜.non_member_section a` is the subfamily of sets not containing `a`.
* `finset.member_section`: `𝒜.member_section a` is the image of the subfamily of sets containing
  `a` under removing `a`.
* `down.compression`: Down-compression.

## Notation

`𝓓 a 𝒜` is notation for `down.compress a 𝒜` in locale `set_family`.

## References

* https://github.com/b-mehta/maths-notes/blob/master/iii/mich/combinatorics.pdf

## Tags

compression, down-compression
-/

namespace finset
variables {α : Type*} [decidable_eq α] {s : finset α} {a : α}

@[simp] lemma erase_eq_self : s.erase a = s ↔ a ∉ s :=
⟨λ h, h ▸ not_mem_erase _ _, erase_eq_of_not_mem⟩

lemma erase_ne_self : s.erase a ≠ s ↔ a ∈ s := erase_eq_self.not_left

@[simp] lemma insert_eq_self : insert a s = s ↔ a ∈ s :=
⟨λ h, h ▸ mem_insert_self _ _, insert_eq_of_mem⟩

lemma insert_ne_self : insert a s ≠ s ↔ a ∉ s := insert_eq_self.not

end finset

variables {α : Type*} [decidable_eq α] {𝒜 ℬ : finset (finset α)} {s : finset α} {a : α}

namespace finset

/-- ELements of `𝒜` that do not contain `a`. -/
def non_member_section (a : α) (𝒜 : finset (finset α)) : finset (finset α) :=
𝒜.filter $ λ s, a ∉ s

/-- Image of the elements of `𝒜` which contain `a` under removing `a`. Finsets that do not contain
`a` such that `insert a s ∈ 𝒜`. -/
def member_section (a : α) (𝒜 : finset (finset α)) : finset (finset α) :=
(𝒜.filter $ λ s, a ∈ s).image $ λ s, erase s a

@[simp] lemma mem_non_member_section : s ∈ 𝒜.non_member_section a ↔ s ∈ 𝒜 ∧ a ∉ s := mem_filter
@[simp] lemma mem_member_section : s ∈ 𝒜.member_section a ↔ insert a s ∈ 𝒜 ∧ a ∉ s :=
begin
  simp_rw [member_section, mem_image, mem_filter],
  refine ⟨_, λ h, ⟨insert a s, ⟨h.1, mem_insert_self _ _⟩, erase_insert h.2⟩⟩,
  rintro ⟨s, hs, rfl⟩,
  rw insert_erase hs.2,
  exact ⟨hs.1, not_mem_erase _ _⟩,
end

lemma non_member_section_inter (a : α) (𝒜 ℬ : finset (finset α)) :
  (𝒜 ∩ ℬ).non_member_section a = 𝒜.non_member_section a ∩ ℬ.non_member_section a :=
filter_inter_distrib _ _ _

lemma member_section_inter (a : α) (𝒜 ℬ : finset (finset α)) :
  (𝒜 ∩ ℬ).member_section a = 𝒜.member_section a ∩ ℬ.member_section a :=
begin
  unfold member_section,
  rw [filter_inter_distrib, image_inter_of_inj_on _ _ ((erase_inj_on' _).mono _)],
  rw [←coe_union, ←filter_union, coe_filter],
  exact set.inter_subset_right _ _,
end

lemma non_member_section_union (a : α) (𝒜 ℬ : finset (finset α)) :
  (𝒜 ∪ ℬ).non_member_section a = 𝒜.non_member_section a ∪ ℬ.non_member_section a :=
filter_union _ _ _

lemma member_section_union (a : α) (𝒜 ℬ : finset (finset α)) :
  (𝒜 ∪ ℬ).member_section a = 𝒜.member_section a ∪ ℬ.member_section a :=
by simp_rw [member_section, filter_union, image_union]

lemma card_member_section_add_card_non_member_section (a : α) (𝒜 : finset (finset α)) :
  (𝒜.member_section a).card + (𝒜.non_member_section a).card = 𝒜.card :=
begin
  rw [member_section, non_member_section, card_image_of_inj_on,
    filter_card_add_filter_neg_card_eq_card],
  exact (erase_inj_on' _).mono (λ s hs, (mem_filter.1 hs).2),
end

lemma member_section_union_non_member_section (a : α) (𝒜 : finset (finset α)) :
  𝒜.member_section a ∪ 𝒜.non_member_section a = 𝒜.image (λ s, s.erase a) :=
begin
  ext s,
  simp only [mem_union, mem_member_section, mem_non_member_section, mem_image, exists_prop],
  split,
  { rintro (h | h),
    { exact ⟨_, h.1, erase_insert h.2⟩ },
    { exact ⟨_, h.1, erase_eq_of_not_mem h.2⟩ } },
  { rintro ⟨s, hs, rfl⟩,
    by_cases ha : a ∈ s,
    { exact or.inl ⟨by rwa insert_erase ha, not_mem_erase _ _⟩ },
    { exact or.inr ⟨by rwa erase_eq_of_not_mem ha, not_mem_erase _ _⟩ } }
end

@[simp] lemma member_section_member_section : (𝒜.member_section a).member_section a = ∅ :=
by { ext, simp }

@[simp] lemma member_section_non_member_section : (𝒜.non_member_section a).member_section a = ∅ :=
by { ext, simp }

@[simp] lemma non_member_section_member_section :
  (𝒜.member_section a).non_member_section a = 𝒜.member_section a :=
by { ext, simp }

@[simp] lemma non_member_section_non_member_section :
  (𝒜.non_member_section a).non_member_section a = 𝒜.non_member_section a :=
by { ext, simp }

end finset

open finset

-- The namespace is here to distinguish from other compressions.
namespace down

/-- `a`-down-compressing `𝒜` means removing `a` from the elements of `𝒜` that contain it. -/
def compression (a : α) (𝒜 : finset (finset α)) : finset (finset α) :=
𝒜.compression $ λ s, s.erase a

localized "notation `𝓓 ` := down.compression" in finset_family

/-- `a` is in the down-compressed family iff it's in the original and its compression is in the
original, or it's not in the original but it's the compression of something in the original. -/
lemma mem_compression : s ∈ 𝓓 a 𝒜 ↔ s ∈ 𝒜 ∧ s.erase a ∈ 𝒜 ∨ s ∉ 𝒜 ∧ insert a s ∈ 𝒜 :=
mem_compression.trans $ or_congr_right' $ and_congr_right $ λ hs, begin
  refine ⟨_, λ h, ⟨_, h, erase_insert $ insert_ne_self.1 $ ne_of_mem_of_not_mem h hs⟩⟩,
  rintro ⟨t, ht, rfl⟩,
  rwa insert_erase (erase_ne_self.1 (ne_of_mem_of_not_mem ht hs).symm),
end

lemma erase_mem_compression : s ∈ 𝒜 → s.erase a ∈ 𝓓 a 𝒜 := apply_mem_compression $ λ _, erase_idem

-- This is a special case of `erase_mem_compression` once we have `compression_idem`.
lemma erase_mem_compression_of_mem_compression : s ∈ 𝓓 a 𝒜 → s.erase a ∈ 𝓓 a 𝒜 :=
apply_mem_compression_of_mem_compression $ λ _, erase_idem

/-- Down-compressing a family is idempotent. -/
@[simp] lemma compression_idem (a : α) (𝒜 : finset (finset α)) : 𝓓 a (𝓓 a 𝒜) = 𝓓 a 𝒜 :=
compression_idem $ λ a, erase_idem

/-- Down-compressing a family doesn't change its size. -/
@[simp] lemma card_compression (a : α) (𝒜 : finset (finset α)) : (𝓓 a 𝒜).card = 𝒜.card :=
card_compression $ (erase_inj_on' _).mono $ λ s, not_imp_comm.1 erase_eq_of_not_mem

end down
