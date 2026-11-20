import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsoUnitaryIrrepConjDual
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NonemptyInvFunEquiv
open MvPolynomial GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries GlobalTheory.OneFunctional Formalism.BasicNotions GlobalTheory.Branching
open scoped TensorProduct DirectSum
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.ConjDual.iso_conj_dual | exact GlobalTheory.ConjDual.iso_conj_dual | (intros; apply GlobalTheory.ConjDual.iso_conj_dual <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.iso_unitaryIrrep_conj_dual : ∀ (n : ℕ) (lam : DomWeight n), Iso ((irr n lam).comp (conjU n) : Representation ℂ (U n) (nablaSq ℂ n lam)) (irr n lam).dual := by
  first | exact @GlobalTheory.ConjDual.iso_conj_dual | exact GlobalTheory.ConjDual.iso_conj_dual | (intros; apply GlobalTheory.ConjDual.iso_conj_dual <;> assumption)
