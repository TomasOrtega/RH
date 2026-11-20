import Mathlib
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.VanishingLowCoefficientReadingsSpanModels
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.CarchAt
import Development.AbelianVarietyTheory.Definitions.ThetaValues.Generic
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.Pj.QAt Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions GlobalTheory.ArcCM GlobalTheory.Shares
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FThetaShiftProofs%2FVanishingLowCoefficientReadingsSpanModels.lean&line=31#L31)
-/
theorem _root_.GlobalTheory.T.vanishing_low_coefficient_readings_span_models : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ), InR D j → ∀ (ka : WeightFamilies.Wt D j) (CR Tt cc : ℝ), (j < D.R.m → DetectQ h.toLawsCore j ka CR Tt cc) → RdOnto h j ka → MggOnto h j CR Tt cc ka := by
  first | exact @GlobalTheory.ConjKill.mggOnto_of_rdOnto | exact GlobalTheory.ConjKill.mggOnto_of_rdOnto | (intros; apply GlobalTheory.ConjKill.mggOnto_of_rdOnto <;> assumption)
