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
Establish `h` using `matActC_smul_one (J := J) (1 : ℚ) z`. Simplify using `using h`.
-/
theorem matActC_one {J : Type} [Fintype J] [DecidableEq J] (z : J → ℂ) : matActC (1 : Matrix J J ℚ) z = z := by
  have h := matActC_smul_one (J := J) (1 : ℚ) z
  simpa using h

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `[matActC]`.
-/
theorem matActC_zero {J : Type} [Fintype J] (A : Matrix J J ℚ) : matActC A 0 = 0 := by
  funext i
  simp [matActC]

/- English proof (translation)
Introduce `κ _ B m m' hB hm hm'`. Take `⟨B', hBB', hB'B⟩` from `isInvMat_mul hB`. Establish `hinv : ∀ w, matActC B (matActC B' w) = w` using `fun w => by`. Rewrite using `[matActC_mul, hBB', matActC_one]`. Establish `heq : ∀ w, m'.ρ w = m.ρ (matActC B' w)` using `fun w => by`.

Rewrite using `[← hm' (matActC B' w), hinv]`. Establish `hmaps : Set.MapsTo (matActC B') {z : Ix κ → ℂ | z ≠ 0} {z | z ≠ 0}` using `fun w hw h0 => by`. Apply `hw` to reduce the goal to its premises. Rewrite using `[← hinv w, h0, matActC_zero]`. Conclude with `(hm.comp (contDiff_matActC B').contDiffOn hmaps).congr fun w _ => heq w`.
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
