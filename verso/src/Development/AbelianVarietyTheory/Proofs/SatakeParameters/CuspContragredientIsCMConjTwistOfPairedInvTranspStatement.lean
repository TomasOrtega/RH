import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CuspContragredientIsCMConjTwistOfPairedInvTransp
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.DualIsConjByOne
open NumberField Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.ContraPair
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FSatakeParameters%2FCuspContragredientIsCMConjTwistOfPairedInvTransp.lean&line=65#L65)
-/
theorem _root_.GlobalTheory.T.cuspContragredientIsCMConjTwist_of_paired_invTranspose : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (a : ℕ) (π : CuspSub L a) (ψ : HChar L), Paired (π.twist ψ⁻¹) (π.twist ψ⁻¹) invTOp → GlobalTheory.GalOfCusp.IsConjDualBy π ψ → DualIsConjBy π ψ := by
  first | exact @GlobalTheory.ConjDualPair.dualIsConjBy_of_paired_invT | exact GlobalTheory.ConjDualPair.dualIsConjBy_of_paired_invT | (intros; apply GlobalTheory.ConjDualPair.dualIsConjBy_of_paired_invT <;> assumption)
