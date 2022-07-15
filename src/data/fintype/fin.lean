/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
import data.fin.interval

/-!
# The structure of `fintype (fin n)`

This file contains some basic results about the `fintype` instance for `fin`,
especially properties of `finset.univ : finset (fin n)`.
-/


open finset
open fintype

namespace fin

variables {α β : Type*} {n : ℕ}

@[simp] lemma Ioi_zero_eq_map :
  Ioi (0 : fin n.succ) = univ.map (fin.succ_embedding _).to_embedding :=
begin
  ext i,
  simp only [mem_Ioi, mem_map, mem_univ, function.embedding.coe_fn_mk, exists_true_left],
  split,
  { refine cases _ _ i,
    { rintro ⟨⟨⟩⟩ },
    { intros j _, exact ⟨j, rfl⟩ } },
  { rintro ⟨i, _, rfl⟩,
    exact succ_pos _ },
end

@[simp] lemma Ioi_succ (i : fin n) :
  Ioi i.succ = (Ioi i).map (fin.succ_embedding _).to_embedding :=
begin
  ext i,
  simp only [mem_filter, mem_Ioi, mem_map, mem_univ, true_and,
  function.embedding.coe_fn_mk, exists_true_left],
  split,
  { refine cases _ _ i,
    { rintro ⟨⟨⟩⟩ },
    { intros i hi,
      refine ⟨i, succ_lt_succ_iff.mp hi, rfl⟩ } },
  { rintro ⟨i, hi, rfl⟩, simpa },
end

lemma card_filter_univ_fin (p : (fin (n + 1)) → Prop) [decidable_pred p] :
  (univ.filter p).card = (ite (p 0) 1 0) + (univ.filter (p ∘ fin.succ)).card :=
begin
  rw [fin.univ_succ, filter_cons, card_disj_union, map_filter, card_map],
  split_ifs; simp,
end

lemma card_filter_univ_eq_nth_eq_count [decidable_eq α] (a : α) (v : vector α n) :
  (univ.filter $ λ i, a = v.nth i).card = v.to_list.count a :=
begin
  refine vector.induction_on v (by simp) (_),
  intros n' x xs hxs,
  simp_rw [card_filter_univ_fin, vector.nth_cons_zero, vector.to_list_cons,
    function.comp, vector.nth_cons_succ, hxs, list.count_cons', add_comm (ite (a = x) 1 0)]
end

end fin
