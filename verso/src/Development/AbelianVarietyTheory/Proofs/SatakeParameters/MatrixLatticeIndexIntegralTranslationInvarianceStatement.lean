import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MatrixLatticeIndexIntegralTranslationInvariance
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemIntMat
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FSatakeParameters%2FMatrixLatticeIndexIntegralTranslationInvariance.lean&line=69#L69)
-/
theorem _root_.GlobalTheory.T.matrixLatticeIndex_integral_translation_invariance : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (a b : ℕ) (x : Matrix (Fin a) (Fin b) L),
    (∀ u ∈ GlobalTheory.Hk3.HoweDuality.intMat L a b, GlobalTheory.Hk3.HoweDuality.latIdx (x + u) = GlobalTheory.Hk3.HoweDuality.latIdx x) ∧
    ∀ h : GL (Fin a) L, h ∈ Formalism.UG.GLint (Fin a) (Formalism.UG.intL L) →
      GlobalTheory.Hk3.HoweDuality.latIdx ((h : Matrix (Fin a) (Fin a) L) * x) = GlobalTheory.Hk3.HoweDuality.latIdx x := by
  first | exact @GlobalTheory.Hk3.HoweDuality.latIdx_invariance | exact GlobalTheory.Hk3.HoweDuality.latIdx_invariance | (intros; apply GlobalTheory.Hk3.HoweDuality.latIdx_invariance <;> assumption)
