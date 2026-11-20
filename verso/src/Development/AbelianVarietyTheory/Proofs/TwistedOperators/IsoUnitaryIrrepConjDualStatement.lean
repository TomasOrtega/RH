import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsoUnitaryIrrepConjDual
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NonemptyInvFunEquiv
open MvPolynomial GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries GlobalTheory.OneFunctional Formalism.BasicNotions GlobalTheory.Branching
open scoped TensorProduct DirectSum
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.ConjDual.iso_conj_dual` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FIsoUnitaryIrrepConjDual.lean&line=67#L67)
-/
theorem _root_.GlobalTheory.T.iso_unitaryIrrep_conj_dual : ∀ (n : ℕ) (lam : DomWeight n), Iso ((irr n lam).comp (conjU n) : Representation ℂ (U n) (nablaSq ℂ n lam)) (irr n lam).dual := by
  first | exact @GlobalTheory.ConjDual.iso_conj_dual | exact GlobalTheory.ConjDual.iso_conj_dual | (intros; apply GlobalTheory.ConjDual.iso_conj_dual <;> assumption)
