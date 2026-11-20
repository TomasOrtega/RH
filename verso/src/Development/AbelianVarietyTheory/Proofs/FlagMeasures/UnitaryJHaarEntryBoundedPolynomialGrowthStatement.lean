import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryJHaarEntryBoundedPolynomialGrowth
import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.RealObj
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnipotentRadicalInterConjugateClosedUnimodular
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsHaarMeasureOfSigmaFinite
open MeasureTheory
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.UJGrowth.growth | exact GlobalTheory.UJGrowth.growth | (intros; apply GlobalTheory.UJGrowth.growth <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.unitaryJ_haar_entryBounded_polynomial_growth : ∀ {n : ℕ} (ε : Fin n → Bool) (S : Subgroup (Formalism.REAL.UJ ε)), IsClosed (S : Set (Formalism.REAL.UJ ε)) → ∀ μ : Measure (Formalism.REAL.UJ ε), Formalism.L2.SG.RealObj.IsHaarLoc (S : Set (Formalism.REAL.UJ ε)) μ → IsFiniteMeasureOnCompacts μ → ∃ (C : ℝ) (D : ℕ), ∀ R : ℝ, 1 ≤ R → μ {g : Formalism.REAL.UJ ε | ∀ i j, ‖Formalism.MainNotions.S.uMat g i j‖ ≤ R} ≤ ENNReal.ofReal (C * R ^ D) := by
  first | exact @GlobalTheory.UJGrowth.growth | exact GlobalTheory.UJGrowth.growth | (intros; apply GlobalTheory.UJGrowth.growth <;> assumption)
