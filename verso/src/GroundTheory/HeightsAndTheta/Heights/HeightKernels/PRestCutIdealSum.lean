import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsRest
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

/- English proof (translation)
By extensionality, compare the relevant components. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules.

Reduce the equality to equality of the corresponding arguments. Use linear arithmetic over natural numbers and integers. Assume the hypotheses and unpack their components. Supply the required witnesses or components.
-/
theorem restPsumIdeal_generators_eq_range (f N : ℕ) :
    {P | ∃ k τ, 1 ≤ k ∧ k ≤ N ∧ P = RestTerms.blockPowerSum f N k τ} =
      Set.range fun i : Fin N × Fin f => RestTerms.blockPowerSum f N ((i.1 : ℕ) + 1) i.2 := by
  ext P
  constructor
  · rintro ⟨k, τ, hk1, hkN, rfl⟩
    refine ⟨(⟨k - 1, by omega⟩, τ), ?_⟩
    simp only
    congr 1
    omega
  · rintro ⟨i, rfl⟩
    exact ⟨(i.1 : ℕ) + 1, i.2, by omega, by omega, rfl⟩

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Rewrite the indicated hypotheses using the stated equalities. Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
theorem RestCutIdealSum.proof : RestCutIdealSum.Statement := by
  intro f N A hA
  rw [restPsumIdeal, restPsumIdeal_generators_eq_range, Ideal.mem_span_range_iff_exists_fun] at hA
  obtain ⟨c, hc⟩ := hA
  exact ⟨c, by rw [← hc]; exact Finset.sum_congr rfl fun i _ => mul_comm _ _⟩

end GroundTheory.Heights₂.Heights
