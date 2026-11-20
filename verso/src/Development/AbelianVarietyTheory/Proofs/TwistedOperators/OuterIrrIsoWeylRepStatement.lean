import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OuterIrrIsoWeylRep
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NonemptyInvFunEquiv
open MvPolynomial GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries GlobalTheory.OneFunctional Formalism.BasicNotions GlobalTheory.Branching
open scoped TensorProduct DirectSum
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FOuterIrrIsoWeylRep.lean&line=215#L215)
-/
theorem _root_.GlobalTheory.T.outer_irr_iso_weylRep_of_pos : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (n : ℕ), 0 < n → ∀ (lam : ι → ℕ → ℤ) (μ : ι → DomWeight n), (∀ τ (i : Fin n), (μ τ).w i = lam τ i) → Iso (outer fun τ => irr n (μ τ)) (weylRep n lam) := by
  first | exact @GlobalTheory.OneFunctional.WeylTensor.outer_irr_iso_weylRep | exact GlobalTheory.OneFunctional.WeylTensor.outer_irr_iso_weylRep | (intros; apply GlobalTheory.OneFunctional.WeylTensor.outer_irr_iso_weylRep <;> assumption)
