import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.VolumeUnitaryMaximalCompactEqProd
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsGaugeAll
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.VolMaxK.volume_maxK` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FVolumeUnitaryMaximalCompactEqProd.lean&line=226#L226)
-/
theorem _root_.GlobalTheory.T.volume_unitaryMaximalCompact_eq_prod : ∀ (n : ℕ) (ε : Fin n → Bool) (p q : ℕ), (univ.filter fun a => ε a = true).card = p → (univ.filter fun a => ε a = false).card = q → ∀ μ, IsGaugeSub (maxK ε) (p ^ 2 + q ^ 2) μ → μ Set.univ = ENNReal.ofReal (volU p * volU q) := by
  first | exact @GlobalTheory.VolMaxK.volume_maxK | exact GlobalTheory.VolMaxK.volume_maxK | (intros; apply GlobalTheory.VolMaxK.volume_maxK <;> assumption)
