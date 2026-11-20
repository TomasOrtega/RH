import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExpMemUnipotentAndHasDerivAtCharacter
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Formalism.RealPlaceAnalysis.StatementE
import Formalism.RealPlaceAnalysis.StatementKT
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FJetHarmonics%2FExpMemUnipotentAndHasDerivAtCharacter.lean&line=77#L77)
-/
theorem _root_.GlobalTheory.T.exp_mem_unipotent_and_hasDerivAt_character : ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (X : Mx k r), Formalism.QuantumDeterminants.inWb k r z → PI.UpqRep.InLieHpk k r X → (∀ i j : Fin (2 * r + k + 1), ¬ (i < j ∧ ¬ (r ≤ i.val ∧ j.val ≤ r + k)) → X i j = 0) → (∀ t : ℝ, NormedSpace.exp ((t : ℂ) • X) ∈ Formalism.QuantumDeterminants.Nset k r) ∧ HasDerivAt (fun t : ℝ => Formalism.QuantumDeterminants.psi k r z Formalism.QuantumDeterminants.cStd (NormedSpace.exp ((t : ℂ) • X))) (Formalism.QuantumDeterminants.ell k r z X - star (Formalism.QuantumDeterminants.ell k r z X)) 0 := by
  first | exact @GlobalTheory.UnipotentExp.exp_mem_and_deriv | exact GlobalTheory.UnipotentExp.exp_mem_and_deriv | (intros; apply GlobalTheory.UnipotentExp.exp_mem_and_deriv <;> assumption)
