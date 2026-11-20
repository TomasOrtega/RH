import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmplitudeSizeConsequencesOfWordIndependentHyps
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.DegVand
import Formalism.LocalRingCardinality.DataTies
open MeasureTheory Matrix Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Amp.SizesProof.sizes_of_hyp` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FAmplitudeSizeConsequencesOfWordIndependentHyps.lean&line=15#L15)
-/
theorem _root_.GlobalTheory.T.amplitudeSizeConsequences_of_wordIndependentHyps : ∀ (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 : ℝ), D.host.rdE ≤ large₂.sc.b → HypZ D large₂ C' Cl Cg cb Cu cT CT C0 → Sizes D large₂ Cl Cg CT := by
  first | exact @GlobalTheory.Amp.SizesProof.sizes_of_hyp | exact GlobalTheory.Amp.SizesProof.sizes_of_hyp | (intros; apply GlobalTheory.Amp.SizesProof.sizes_of_hyp <;> assumption)
