import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryIrrepCompConjIsoDual
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NonemptyInvFunEquiv
open MvPolynomial GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries GlobalTheory.OneFunctional Formalism.BasicNotions GlobalTheory.Branching
open scoped TensorProduct DirectSum
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.OneFunctional.iso_irr_comp_conjU` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FUnitaryIrrepCompConjIsoDual.lean&line=61#L61)
-/
theorem _root_.GlobalTheory.T.unitaryIrrep_comp_conj_iso_dual : ∀ (n : ℕ), 0 < n → ∀ lam : DomWeight n, Iso ((irr n lam).comp (conjU n) : Representation ℂ (U n) (nablaSq ℂ n lam)) (irr n lam.dual) := by
  first | exact @GlobalTheory.OneFunctional.iso_irr_comp_conjU | exact GlobalTheory.OneFunctional.iso_irr_comp_conjU | (intros; apply GlobalTheory.OneFunctional.iso_irr_comp_conjU <;> assumption)
