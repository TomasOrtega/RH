import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonzeroSquaresSumEquivIcoModFour
import Development.AbelianVarietyTheory.Definitions.Divisors.DatumOfIsIntegersLattice
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDiscreteValuationRingValuationSubringAtPrime
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AddMonoidHomEqZeroOfEventually
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.sq_sum_equiv_Ico` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FNonzeroSquaresSumEquivIcoModFour.lean&line=37#L37)
-/
theorem _root_.GlobalTheory.T.nonzeroSquares_sum_equiv_Ico_mod_four : ∀ (p : ℕ), p.Prime → p % 4 = 3 → ∃ e : Sq p ⊕ Sq p ≃ (Finset.Ico 1 p : Finset ℕ), ∀ k : Sq p, ((e (Sum.inl k) : ℕ) = (k.1 : ℕ)) ∧ ((e (Sum.inr k) : ℕ) = p - (k.1 : ℕ)) := by
  first | exact @GlobalTheory.sq_sum_equiv_Ico | exact GlobalTheory.sq_sum_equiv_Ico | (intros; apply GlobalTheory.sq_sum_equiv_Ico <;> assumption)
