import Mathlib
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntiJMulApply

open Formalism.UG GlobalTheory.SatakeWeyl

namespace GlobalTheory.SatakeWeyl

/- English proof (translation)
Introduce `L _ _ σ n r e β γ ι hσ hD hι g`. Take `⟨he, -, -, -, -, hβγ⟩` from `hD`. Take `⟨h1, h2⟩` from `hι g`. Establish `hcases : ∀ a b : Fin n, (∃ i j, a = e i ∧ b = e j) ∨ (a ∉ Set.range e ∨ b ∉ Set.range e)`. Introduce `a b`.

Distinguish the cases in `ha : a ∈ Set.range e`. Distinguish the cases in `hb : b ∈ Set.range e`. Take `⟨i, rfl⟩` from `ha`. Take `⟨j, rfl⟩` from `hb`. Conclude with `Or.inl ⟨i, j, rfl, rfl⟩`.

Conclude with `Or.inr (Or.inr hb)`. Conclude with `Or.inr (Or.inl ha)`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[mem_KU_iff hσ, mem_KU_iff hσ]`. Use `⟨fun h i j => h1 i j ▸ h (e i) (e j), fun h a b => ?_⟩` and prove the remaining obligations.

Break down `hcases a b with ⟨i, j, rfl, rfl⟩ | hab` into its components or cases. Rewrite using `[h1]`. Conclude with `h i j`. Rewrite using `[h2 a b hab, Matrix.one_apply] split_ifs`. Conclude with `one_mem _`.

Conclude with `zero_mem _`. Introduce `hg a b hab`. Break down `hcases a b with ⟨i, j, rfl, rfl⟩ | h` into its components or cases. Rewrite using `[h1]`. Conclude with `hg i j fun hij => hab ((hβγ i j).2 hij)`.

Rewrite using `[h2 a b h]`. Conclude with `Matrix.one_apply_ne fun h' => hab (h' ▸ rfl)`. Introduce `hg a b hab`. Break down `hcases a b with ⟨i, j, rfl, rfl⟩ | h` into its components or cases. Establish `hji : j ≤ i` using `he.le_iff_le.1 hab`.

Rewrite using `[h1, hg i j hji, Matrix.one_apply, Matrix.one_apply]`. Simplify using `only [he.injective.eq_iff]`. Conclude with `h2 a b h`.
-/
theorem embMem : EmbMem := by
  intro L _ _ σ n r e β γ ι hσ hD hι g
  obtain ⟨he, -, -, -, -, hβγ⟩ := hD
  obtain ⟨h1, h2⟩ := hι g
  have hcases : ∀ a b : Fin n, (∃ i j, a = e i ∧ b = e j) ∨ (a ∉ Set.range e ∨ b ∉ Set.range e) := by
    intro a b
    by_cases ha : a ∈ Set.range e
    · by_cases hb : b ∈ Set.range e
      · obtain ⟨i, rfl⟩ := ha
        obtain ⟨j, rfl⟩ := hb
        exact Or.inl ⟨i, j, rfl, rfl⟩
      · exact Or.inr (Or.inr hb)
    · exact Or.inr (Or.inl ha)
  refine ⟨?_, ?_, ?_⟩
  · rw [mem_KU_iff hσ, mem_KU_iff hσ]
    refine ⟨fun h i j => h1 i j ▸ h (e i) (e j), fun h a b => ?_⟩
    rcases hcases a b with ⟨i, j, rfl, rfl⟩ | hab
    · rw [h1]; exact h i j
    · rw [h2 a b hab, Matrix.one_apply]
      split_ifs
      · exact one_mem _
      · exact zero_mem _
  · intro hg a b hab
    rcases hcases a b with ⟨i, j, rfl, rfl⟩ | h
    · rw [h1]
      exact hg i j fun hij => hab ((hβγ i j).2 hij)
    · rw [h2 a b h]
      exact Matrix.one_apply_ne fun h' => hab (h' ▸ rfl)
  · intro hg a b hab
    rcases hcases a b with ⟨i, j, rfl, rfl⟩ | h
    · have hji : j ≤ i := he.le_iff_le.1 hab
      rw [h1, hg i j hji, Matrix.one_apply, Matrix.one_apply]
      simp only [he.injective.eq_iff]
    · exact h2 a b h

end GlobalTheory.SatakeWeyl
