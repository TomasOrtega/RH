import Mathlib
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Statements
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsSchur
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open Finset

/- English proof (translation)
Introduce `k nu hk hanti hsum hhook`. Take `⟨n, rfl⟩ : ∃ n, k = n + 1` from `⟨k - 1, by omega⟩`. Use `set s := univ.filter fun i : Fin (n + 1) => (i : ℕ) ≠ 0 ∧ nu i = 1 with hs`. Use `set t := s.card with ht`. Establish `down : ∀ i j : Fin (n + 1), (i : ℕ) ≠ 0 → i ≤ j → j ∈ s → i ∈ s`.

Introduce `i j hi hij hj`. Simplify using `only [hs, mem_filter, mem_univ, true_and] at hj ⊢`. Establish `h1` using `hanti hij`. Establish `h2` using `hhook i hi`. Conclude with `⟨hi, by omega⟩`.

Establish `hA : ∀ j ∈ s, (j : ℕ) ≤ t`. Introduce `j hj`. Establish `hsub : Finset.Icc 1 (j : ℕ) ⊆ s.map Fin.valEmbedding`. Introduce `m hm`. Rewrite `hm` using `[Finset.mem_Icc]`.

Rewrite using `[Finset.mem_map]`. Use `⟨⟨m, by omega⟩, down _ j (show m ≠ 0 by omega) (by rw [Fin.le_iff_val_le_val]; show m ≤ (j : ℕ); omega) hj, rfl⟩` and prove the remaining obligations. Use `Finset.card_le_card hsub` as an intermediate fact. Simplify using `at this`. Use linear arithmetic over natural numbers and integers.

Establish `hB : ∀ i : Fin (n + 1), (i : ℕ) ≠ 0 → (i : ℕ) ≤ t → i ∈ s`. Introduce `i hi hit`. Assume the negation of the conclusion as `hni`. Establish `hsub : s.map Fin.valEmbedding ⊆ Finset.Ico 1 (i : ℕ)`. Introduce `m hm`.

Rewrite `hm` using `[Finset.mem_map]`. Take `⟨j, hj, rfl⟩` from `hm`. Establish `hj'` using `hj`. Simplify using `only [hs, mem_filter, mem_univ, true_and] at hj'`. Rewrite using `[Finset.mem_Ico]`.

Use `⟨by simp only [Fin.valEmbedding_apply]; omega, ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hle`. Conclude with `hni (down i j hi (by rw [Fin.le_iff_val_le_val]; simp at hle; omega) hj)`. Use `Finset.card_le_card hsub` as an intermediate fact. Simplify using `at this`.

Use linear arithmetic over natural numbers and integers. Establish `hval : ∀ i : Fin (n + 1), (i : ℕ) ≠ 0 → nu i = if (i : ℕ) ≤ t then 1 else 0`. Introduce `i hi`. Establish `h1` using `hhook i hi`. Use `split_ifs with h`.

Use `hB i hi h` as an intermediate fact. Simplify using `only [hs, mem_filter, mem_univ, true_and] at this`. Conclude with `this.2`. Establish `: nu i ≠ 1`. Introduce `h1'`.

Use `hA i (by simp only [hs, mem_filter, mem_univ, true_and]; exact ⟨hi, h1'⟩)` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Use linear arithmetic over natural numbers and integers. Establish `htn : t ≤ n`. Establish `hsub : s ⊆ univ.erase 0`.

Introduce `i hi`. Simplify using `only [hs, mem_filter, mem_univ, true_and] at hi`. Conclude with `Finset.mem_erase.mpr ⟨fun h => hi.1 (by simp [h]), mem_univ _⟩`. Use `card_le_card hsub` as an intermediate fact. Simplify `this` using `[card_erase_of_mem]`.

Establish `hnu0 : nu 0 + t = n + 1`. Establish `hpt : ∀ i, nu i = (if i = 0 then nu 0 else 0) + (if (i : ℕ) ≠ 0 ∧ nu i = 1 then 1 else 0)`. Introduce `i`. Distinguish the cases in `h0 : i = 0`. Substitute `h0` using the available equality.

Simplify using the standard rewrite rules. Establish `hi : (i : ℕ) ≠ 0` using `fun h => h0 (Fin.ext (by simp [h]))`. Use `hhook i hi` as an intermediate fact. Rewrite using `[if_neg h0, zero_add]`. Apply the tactic sequence `split_ifs with h <;> omega`.

Establish `hsum2 : ∑ i, nu i = nu 0 + t`. Rewrite using `[Finset.sum_congr rfl (fun i _ => hpt i), Finset.sum_add_distrib, Finset.sum_boole]`. Simplify using `[t, s]`. Use linear arithmetic over natural numbers and integers. Use `⟨(Fin.cycleRange (⟨t, by omega⟩ : Fin (n + 1)))⁻¹, ?_, ?_⟩` and prove the remaining obligations.

Introduce `i`. Take `⟨j, rfl⟩` from `(Fin.cycleRange (⟨t, by omega⟩ : Fin (n + 1))).surjective i`. Simplify using `only [Equiv.Perm.inv_def, Equiv.symm_apply_apply]`. Break down `lt_trichotomy (j : ℕ) t with h | h | h` into its components or cases. Establish `hlt : j < (⟨t, by omega⟩ : Fin (n + 1))` using `Fin.lt_def.mpr h`.

Establish `hv : ((Fin.cycleRange (⟨t, by omega⟩ : Fin (n + 1)) j : Fin (n + 1)) : ℕ) = j + 1` using `Fin.coe_cycleRange_of_lt hlt`. Rewrite using `[hval _ (by rw [hv]; omega), hv, if_pos (by omega), Nat.mod_eq_of_lt (by omega)]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[Fin.cycleRange_of_eq (Fin.ext h), Fin.val_zero]`. Establish `h2 : nu 0 + (n + 1 - 1 - 0) = (n - t) + (n + 1)` using `by omega`.

Rewrite using `[h2, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]`. Use linear arithmetic over natural numbers and integers. Establish `hgt : (⟨t, by omega⟩ : Fin (n + 1)) < j` using `Fin.lt_def.mpr h`. Rewrite using `[Fin.cycleRange_of_gt hgt, hval j (by omega), if_neg (by omega), Nat.mod_eq_of_lt (by omega)]`. Use linear arithmetic over natural numbers and integers.

Rewrite using `[Equiv.Perm.sign_inv, Fin.sign_cycleRange]`. Simplify using `[t, s]`.
-/
theorem SchHookResidues.proof : SchHookResidues.Statement := by
  intro k nu hk hanti hsum hhook
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  set s := univ.filter fun i : Fin (n + 1) => (i : ℕ) ≠ 0 ∧ nu i = 1 with hs
  set t := s.card with ht
  have down : ∀ i j : Fin (n + 1), (i : ℕ) ≠ 0 → i ≤ j → j ∈ s → i ∈ s := by
    intro i j hi hij hj
    simp only [hs, mem_filter, mem_univ, true_and] at hj ⊢
    have h1 := hanti hij
    have h2 := hhook i hi
    exact ⟨hi, by omega⟩
  have hA : ∀ j ∈ s, (j : ℕ) ≤ t := by
    intro j hj
    have hsub : Finset.Icc 1 (j : ℕ) ⊆ s.map Fin.valEmbedding := by
      intro m hm
      rw [Finset.mem_Icc] at hm
      rw [Finset.mem_map]
      refine ⟨⟨m, by omega⟩, down _ j (show m ≠ 0 by omega)
        (by rw [Fin.le_iff_val_le_val]; show m ≤ (j : ℕ); omega) hj, rfl⟩
    have := Finset.card_le_card hsub
    simp at this
    omega
  have hB : ∀ i : Fin (n + 1), (i : ℕ) ≠ 0 → (i : ℕ) ≤ t → i ∈ s := by
    intro i hi hit
    by_contra hni
    have hsub : s.map Fin.valEmbedding ⊆ Finset.Ico 1 (i : ℕ) := by
      intro m hm
      rw [Finset.mem_map] at hm
      obtain ⟨j, hj, rfl⟩ := hm
      have hj' := hj
      simp only [hs, mem_filter, mem_univ, true_and] at hj'
      rw [Finset.mem_Ico]
      refine ⟨by simp only [Fin.valEmbedding_apply]; omega, ?_⟩
      by_contra hle
      exact hni (down i j hi (by rw [Fin.le_iff_val_le_val]; simp at hle; omega) hj)
    have := Finset.card_le_card hsub
    simp at this
    omega
  have hval : ∀ i : Fin (n + 1), (i : ℕ) ≠ 0 → nu i = if (i : ℕ) ≤ t then 1 else 0 := by
    intro i hi
    have h1 := hhook i hi
    split_ifs with h
    · have := hB i hi h
      simp only [hs, mem_filter, mem_univ, true_and] at this
      exact this.2
    · have : nu i ≠ 1 := by
        intro h1'
        have := hA i (by simp only [hs, mem_filter, mem_univ, true_and]; exact ⟨hi, h1'⟩)
        omega
      omega
  have htn : t ≤ n := by
    have hsub : s ⊆ univ.erase 0 := by
      intro i hi
      simp only [hs, mem_filter, mem_univ, true_and] at hi
      exact Finset.mem_erase.mpr ⟨fun h => hi.1 (by simp [h]), mem_univ _⟩
    have := card_le_card hsub
    simpa [card_erase_of_mem] using this
  have hnu0 : nu 0 + t = n + 1 := by
    have hpt : ∀ i, nu i = (if i = 0 then nu 0 else 0) +
        (if (i : ℕ) ≠ 0 ∧ nu i = 1 then 1 else 0) := by
      intro i
      by_cases h0 : i = 0
      · subst h0; simp
      · have hi : (i : ℕ) ≠ 0 := fun h => h0 (Fin.ext (by simp [h]))
        have := hhook i hi
        rw [if_neg h0, zero_add]
        split_ifs with h <;> omega
    have hsum2 : ∑ i, nu i = nu 0 + t := by
      rw [Finset.sum_congr rfl (fun i _ => hpt i), Finset.sum_add_distrib, Finset.sum_boole]
      simp [t, s]
    omega
  refine ⟨(Fin.cycleRange (⟨t, by omega⟩ : Fin (n + 1)))⁻¹, ?_, ?_⟩
  · intro i
    obtain ⟨j, rfl⟩ := (Fin.cycleRange (⟨t, by omega⟩ : Fin (n + 1))).surjective i
    simp only [Equiv.Perm.inv_def, Equiv.symm_apply_apply]
    rcases lt_trichotomy (j : ℕ) t with h | h | h
    · have hlt : j < (⟨t, by omega⟩ : Fin (n + 1)) := Fin.lt_def.mpr h
      have hv : ((Fin.cycleRange (⟨t, by omega⟩ : Fin (n + 1)) j : Fin (n + 1)) : ℕ) = j + 1 :=
        Fin.coe_cycleRange_of_lt hlt
      rw [hval _ (by rw [hv]; omega), hv, if_pos (by omega), Nat.mod_eq_of_lt (by omega)]
      omega
    · rw [Fin.cycleRange_of_eq (Fin.ext h), Fin.val_zero]
      have h2 : nu 0 + (n + 1 - 1 - 0) = (n - t) + (n + 1) := by omega
      rw [h2, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      omega
    · have hgt : (⟨t, by omega⟩ : Fin (n + 1)) < j := Fin.lt_def.mpr h
      rw [Fin.cycleRange_of_gt hgt, hval j (by omega), if_neg (by omega),
        Nat.mod_eq_of_lt (by omega)]
      omega
  · rw [Equiv.Perm.sign_inv, Fin.sign_cycleRange]
    simp [t, s]

end GroundTheory.Heights₂.Heights.RestTerms
