import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormalFormRootMeasureHaarUnimodular
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.BlockAnti
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Amp.RootMeas.normR_facts` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FNormalFormRootMeasureHaarUnimodular.lean&line=14#L14)
-/
theorem _root_.GlobalTheory.T.normalFormRootMeasure_haar_unimodular : ∀ (k r : ℕ) (γ : Mat k r) (s : ℝ) (μR : Measure (Mt k r)), 0 < s → NormR k r γ s μR → IsClosedSub k r (Rset k r γ) ∧ IsHaarOn (Rset k r γ) μR ∧ IsUnimod (Rset k r γ) μR ∧ NormR k r γ⁻¹ s (μR.map (conjM γ)) := by
  first | exact @GlobalTheory.Amp.RootMeas.normR_facts | exact GlobalTheory.Amp.RootMeas.normR_facts | (intros; apply GlobalTheory.Amp.RootMeas.normR_facts <;> assumption)
