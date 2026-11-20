import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.StepTStA
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsMetricTransportSmooth
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PChangeOfLattice
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ChangeOfLattice

noncomputable section

namespace MetricTransportSmooth

/- English proof (translation)
Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts.
-/
theorem matActC_one {J : Type} [Fintype J] [DecidableEq J] (z : J → ℂ) : matActC (1 : Matrix J J ℚ) z = z := by
  have h := matActC_smul_one (J := J) (1 : ℚ) z
  simpa using h

/- English proof (translation)
Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules.
-/
theorem matActC_zero {J : Type} [Fintype J] (A : Matrix J J ℚ) : matActC A 0 = 0 := by
  funext i
  simp [matActC]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem proof : MetricTransportSmooth.Statement := by
  intro κ _ B m m' hB hm hm'
  classical
  obtain ⟨B', hBB', hB'B⟩ := isInvMat_mul hB
  have hinv : ∀ w, matActC B (matActC B' w) = w := fun w => by
    rw [matActC_mul, hBB', matActC_one]
  have heq : ∀ w, m'.ρ w = m.ρ (matActC B' w) := fun w => by
    rw [← hm' (matActC B' w), hinv]
  have hmaps : Set.MapsTo (matActC B') {z : Ix κ → ℂ | z ≠ 0} {z | z ≠ 0} := fun w hw h0 => by
    apply hw
    rw [← hinv w, h0, matActC_zero]
  exact (hm.comp (contDiff_matActC B').contDiffOn hmaps).congr fun w _ => heq w

end MetricTransportSmooth

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
