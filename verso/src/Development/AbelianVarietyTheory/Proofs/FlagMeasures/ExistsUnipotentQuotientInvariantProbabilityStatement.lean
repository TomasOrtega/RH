import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsUnipotentQuotientInvariantProbability
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
import Formalism.HarderNarasimhan.ShiftInvariance
open GlobalTheory.Count Formalism.MainNotions.S Formalism.HN Formalism.REAL Matrix NumberField MeasureTheory Finset
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FExistsUnipotentQuotientInvariantProbability.lean&line=146#L146)
-/
theorem _root_.GlobalTheory.T.exists_unipotentQuotient_invariant_probability : ∀ (I : AutInst) (W : Submodule I.E (Fin I.n → I.E)), I.IsIsot W → ∃ ν : Measure I.GA, IsProbabilityMeasure ν ∧ I.IsNQuotMeas W ν ∧ ∃ Cp : Set I.GA, IsCompact Cp ∧ Cp ⊆ I.NA W ∧ ν Cpᶜ = 0 := by
  first | exact @GlobalTheory.UnipQuot.exists_quot_prob | exact GlobalTheory.UnipQuot.exists_quot_prob | (intros; apply GlobalTheory.UnipQuot.exists_quot_prob <;> assumption)
