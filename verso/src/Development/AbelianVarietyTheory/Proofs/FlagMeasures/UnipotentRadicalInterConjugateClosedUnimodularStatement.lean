import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnipotentRadicalInterConjugateClosedUnimodular
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NCoords
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MatrixOfBesselTwoSidedAction
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Formalism.HermitianCurvature.WeylElementCommutesLevelOne
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.SnMass
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FUnipotentRadicalInterConjugateClosedUnimodular.lean&line=320#L320)
-/
theorem _root_.GlobalTheory.T.unipotentRadical_inter_conjugate_closed_unimodular : ∀ (k r : ℕ) (γ : Mat k r), γ ∈ GG k r → IsClosedSub k r (Rset k r γ) ∧ ∀ μ, IsHaarOn (Rset k r γ) μ → IsUnimod (Rset k r γ) μ := by
  first | exact @GlobalTheory.UnipUnimod.rset_unimodular | exact GlobalTheory.UnipUnimod.rset_unimodular | (intros; apply GlobalTheory.UnipUnimod.rset_unimodular <;> assumption)
