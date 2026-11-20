import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MahlerCoefficientNormLeOneIffJetsBoundedMeasureM
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LatIntZero
open GlobalTheory.MomOne GlobalTheory.MomN PowerSeries
open scoped ComplexConjugate
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FGlobalInterpolation%2FMahlerCoefficientNormLeOneIffJetsBoundedMeasureM.lean&line=217#L217)
-/
theorem _root_.GlobalTheory.T.mahlerCoefficient_norm_le_one_iff_jets_boundedMeasureMoments : ∀ (q : ℕ) [Fact q.Prime] (ι : ℂ ≃+* ℂ_[q]) (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (κ : Type) [Fintype κ] (v : κ → V) (G : V → ℂ), ContDiff ℂ ⊤ G → (MomInt ι v G ↔ ∀ n, ‖ι (mahler v G n)‖ ≤ 1) := by
  first | exact @GlobalTheory.MomCrit.momInt_iff_norm_mahler_le | exact GlobalTheory.MomCrit.momInt_iff_norm_mahler_le | (intros; apply GlobalTheory.MomCrit.momInt_iff_norm_mahler_le <;> assumption)
