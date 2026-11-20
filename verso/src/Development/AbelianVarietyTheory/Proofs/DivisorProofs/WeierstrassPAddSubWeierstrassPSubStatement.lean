import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeierstrassPAddSubWeierstrassPSub
import Development.AbelianVarietyTheory.Definitions.Divisors.DatumOfIsIntegersLattice
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDiscreteValuationRingValuationSubringAtPrime
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AddMonoidHomEqZeroOfEventually
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.weierstrassP_add_sub_weierstrassP_sub` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FWeierstrassPAddSubWeierstrassPSub.lean&line=6#L6)
-/
theorem _root_.GlobalTheory.T.weierstrassP_sub_sq_mul_add_sub_eq_neg_deriv_mul : ∀ (L : PeriodPair) (z w : ℂ), z ∉ L.lattice → w ∉ L.lattice → z - w ∉ L.lattice → z + w ∉ L.lattice → (L.weierstrassP z - L.weierstrassP w) ^ 2 * (L.weierstrassP (z + w) - L.weierstrassP (z - w)) = -(L.derivWeierstrassP z * L.derivWeierstrassP w) := by
  first | exact @GlobalTheory.weierstrassP_add_sub_weierstrassP_sub | exact GlobalTheory.weierstrassP_add_sub_weierstrassP_sub | (intros; apply GlobalTheory.weierstrassP_add_sub_weierstrassP_sub <;> assumption)
