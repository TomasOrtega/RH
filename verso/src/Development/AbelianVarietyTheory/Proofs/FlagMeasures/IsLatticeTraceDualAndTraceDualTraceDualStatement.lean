import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsLatticeTraceDualAndTraceDualTraceDual
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsLatMeasurableConst
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurableSetDetNormPos
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.MeanDual
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FIsLatticeTraceDualAndTraceDualTraceDual.lean&line=108#L108)
-/
theorem _root_.GlobalTheory.T.isLattice_traceDual_and_traceDual_traceDual : ∀ (E : Type) [Field E] [NumberField E] (j : ℕ) (Λ : Submodule (𝓞 E) (Fin j → E)), Submodule.IsLattice E Λ → Submodule.IsLattice E (trDual E j Λ) ∧ trDual E j (trDual E j Λ) = Λ := by
  first | exact @GlobalTheory.MeanDual.Alg.isLattice_trDual_and_trDual_trDual | exact GlobalTheory.MeanDual.Alg.isLattice_trDual_and_trDual_trDual | (intros; apply GlobalTheory.MeanDual.Alg.isLattice_trDual_and_trDual_trDual <;> assumption)
