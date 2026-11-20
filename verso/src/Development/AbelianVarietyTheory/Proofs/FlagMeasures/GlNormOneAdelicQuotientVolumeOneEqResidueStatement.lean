import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GlNormOneAdelicQuotientVolumeOneEqResidue
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsGaugeAll
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FGlNormOneAdelicQuotientVolumeOneEqResidue.lean&line=440#L440)
-/
theorem _root_.GlobalTheory.T.glNormOneAdelicQuotientVolume_one_eq_residue : ∀ (E : Type) [Field E] [NumberField E], IsTotallyComplex E → glVol E 1 = ENNReal.ofReal (dedekindZeta_residue E * Formalism.HermitianLatticesTheory.vInv E ^ Formalism.HermitianLatticesTheory.fDeg E) := by
  first | exact @GlobalTheory.NormOneVol.glVol_one | exact GlobalTheory.NormOneVol.glVol_one | (intros; apply GlobalTheory.NormOneVol.glVol_one <;> assumption)
