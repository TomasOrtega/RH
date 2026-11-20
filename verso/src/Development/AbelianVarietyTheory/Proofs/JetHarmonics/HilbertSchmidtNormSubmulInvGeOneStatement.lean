import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.HilbertSchmidtNormSubmulInvGeOne
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.BesselNorm.hilbertSchmidt_normInv` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FJetHarmonics%2FHilbertSchmidtNormSubmulInvGeOne.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.hilbertSchmidt_norm_submul_inv_ge_one : Formalism.FourierDecayAlt.ThreeDimData.NormInv := by
  first | exact @GlobalTheory.BesselNorm.hilbertSchmidt_normInv | exact GlobalTheory.BesselNorm.hilbertSchmidt_normInv | (intros; apply GlobalTheory.BesselNorm.hilbertSchmidt_normInv <;> assumption)
