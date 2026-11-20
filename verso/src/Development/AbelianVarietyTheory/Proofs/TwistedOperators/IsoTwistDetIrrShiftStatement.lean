import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsoTwistDetIrrShift
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NonemptyInvFunEquiv
open MvPolynomial GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries GlobalTheory.OneFunctional Formalism.BasicNotions GlobalTheory.Branching
open scoped TensorProduct DirectSum
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FIsoTwistDetIrrShift.lean&line=39#L39)
-/
theorem _root_.GlobalTheory.T.iso_twist_detU_pow_irr_of_weight_shift : ∀ (n : ℕ) (c : ℤ) (lam lam' : DomWeight n), (∀ i, lam'.w i = lam.w i + c) → Iso (twist (detU n ^ c) (irr n lam)) (irr n lam') := by
  first | exact @GlobalTheory.OneFunctional.iso_twist_det_irr_shift | exact GlobalTheory.OneFunctional.iso_twist_det_irr_shift | (intros; apply GlobalTheory.OneFunctional.iso_twist_det_irr_shift <;> assumption)
