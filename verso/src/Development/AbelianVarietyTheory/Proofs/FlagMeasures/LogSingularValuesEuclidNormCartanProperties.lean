import Mathlib
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormPosOfIsUnit
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DFactsHolds

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ContDiff

noncomputable section

namespace GlobalTheory.Count.CartanSize

open GlobalTheory.Count.Cartan

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations.

Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Separate the alternatives or extract the components of the hypothesis. Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Use the polynomial consequences of the given equalities and inequalities. Fix the arbitrary inputs or assume the hypotheses. Supply the required witnesses or components.

Fix the arbitrary inputs or assume the hypotheses. Separate the alternatives or extract the components of the hypothesis. Simplify using the standard rewrite rules. Extract witnesses or component facts from the available result. Simplify using the standard rewrite rules.

A detailed English derivation is pending.
-/
theorem cartan_size : ∀ (n : ℕ) (ε : Fin n → Bool), Continuous (fun g : UJ ε => dHS (uMat g)) ∧ (∀ g : UJ ε, 0 ≤ dHS (uMat g) ∧ dOp (uMat g) ≤ dHS (uMat g)) ∧ (∀ g : UJ ε, ∃ k ∈ Kset ε, ∃ X, inP ε X ∧ uMat g = k * NormedSpace.exp X ∧ dHS (uMat g) = Real.sqrt (hs X)) ∧ (rkR ε = 0 → ∀ g : UJ ε, dHS (uMat g) = 0) := by
  intro n ε
  have hU : ∀ g : UJ ε, Formalism.REAL.inUJ ε (uMat g) := fun g => g.2
  have hnn : ∀ g : Matrix (Fin n) (Fin n) ℂ, 0 ≤ dHS g := fun g => Real.sqrt_nonneg _
  obtain ⟨-, hB, -, hC, -⟩ := GlobalTheory.Count.Cartan.cartan_distances n ε
  refine ⟨hC, ?_, ?_, ?_⟩
  · intro g
    refine ⟨hnn _, ?_⟩
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [GlobalTheory.Dec.dOp_fin_zero]
      exact hnn _
    · obtain ⟨h0, -, -, h2, -⟩ := hB g g (by omega)
      have h1 : (1 : ℝ) ≤ Real.sqrt 2 := by
        rw [show (1 : ℝ) = Real.sqrt 1 by simp]
        exact Real.sqrt_le_sqrt (by norm_num)
      nlinarith
  · intro g
    exact ⟨uMat g * NormedSpace.exp (-Formalism.REAL.polarLog (uMat g)), Formalism.REAL.mul_exp_neg_polarLog_mem_compact (hU g),
      Formalism.REAL.polarLog (uMat g), Formalism.REAL.polarLog_mem_hermitian_part (hU g), Formalism.REAL.polar_decomposition_eq,
      GlobalTheory.Count.Cartan.dHS_eq_log (hU g)⟩
  · intro hr g
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [dHS]
    · obtain ⟨-, -, -, -, h3⟩ := hB g g (by omega)
      simp only [hr, Nat.cast_zero, mul_zero, Real.sqrt_zero, zero_mul] at h3
      exact le_antisymm h3 (hnn _)

end GlobalTheory.Count.CartanSize
