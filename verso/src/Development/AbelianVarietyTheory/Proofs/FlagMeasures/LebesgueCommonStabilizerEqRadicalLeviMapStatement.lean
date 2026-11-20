import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LebesgueCommonStabilizerEqRadicalLeviMap
import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NormalFormDualOrthogonalLast
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsNormalFormStabilizerMeasure
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsFundOne
open NumberField MeasureTheory Matrix Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.DegVol
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FLebesgueCommonStabilizerEqRadicalLeviMap.lean&line=242#L242)
-/
theorem _root_.GlobalTheory.T.lebesgueCommonStabilizer_eq_radical_levi_map : ∀ (k r j : ℕ) (β : Fin r → ℕ), Monotone β → (∀ a b : Fin r, j ≤ b.val → (β a = β b ↔ j ≤ a.val)) → lebR0 k r j β = (volume : Measure ((UTin β → ℂ) × PTop k r j)).map (fun q => Matrix.of.symm (pTop k r j q.2 * uEmb k r (upperIn β q.1))) ∧ Set.range (rEl k r j β) = Set.range (fun q : (UTin β → ℂ) × PTop k r j => pTop k r j q.2 * uEmb k r (upperIn β q.1)) ∧ Function.Injective (fun q : (UTin β → ℂ) × PTop k r j => pTop k r j q.2 * uEmb k r (upperIn β q.1)) ∧ (j = 0 → lebR0 k r j β = lebN k r) := by
  first | exact @GlobalTheory.DegVol.Swap.range_eq_and_injective_parabolic_unipotent_product | exact GlobalTheory.DegVol.Swap.range_eq_and_injective_parabolic_unipotent_product | (intros; apply GlobalTheory.DegVol.Swap.range_eq_and_injective_parabolic_unipotent_product <;> assumption)
