import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OmAOneApply
open Matrix MeasureTheory ValuativeRel GlobalTheory.SplitFlip GlobalTheory.SmGL GlobalTheory.WeilM GlobalTheory.RankFibre GlobalTheory.SplitWeil GlobalTheory.RankFibreKer

namespace GlobalTheory.RankFibreKer

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations.

Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem exists_isFirstMax : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (a d : ℕ) (Y : Matrix (Fin a) (Fin d) k),
    (∃ J, minor Y J ≠ 0) → ∃ J, IsFirstMax Y J := by
  intro k _ _ _ _ a d Y ⟨J0, hJ0⟩
  classical
  obtain ⟨M, -, hM⟩ := Finset.exists_max_image Finset.univ (fun J => valuation k (minor Y J))
    ⟨J0, Finset.mem_univ _⟩
  set S := Finset.univ.filter (fun J => valuation k (minor Y J) = valuation k (minor Y M)) with hS
  obtain ⟨J, hJS, hJmin⟩ := S.exists_min_image (fun J => idx J) ⟨M, by simp [S]⟩
  have hJ : valuation k (minor Y J) = valuation k (minor Y M) := (Finset.mem_filter.1 hJS).2
  refine ⟨J, ?_, fun J' => ⟨?_, fun hlt => ?_⟩⟩
  · intro h0
    apply hJ0
    have hM0 : valuation k (minor Y M) = 0 := by rw [← hJ, h0, map_zero]
    have h1 := hM J0 (Finset.mem_univ _)
    rw [hM0] at h1
    exact (Valuation.zero_iff _).1 (le_antisymm h1 zero_le')
  · rw [hJ]; exact hM J' (Finset.mem_univ _)
  · rw [hJ]
    refine lt_of_le_of_ne (hM J' (Finset.mem_univ _)) fun heq => ?_
    have := hJmin J' (by simp [S, heq])
    exact absurd hlt (not_lt.2 this)

end GlobalTheory.RankFibreKer
