import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralJOfNonrealMultiplier
import Development.AbelianVarietyTheory.Definitions.Divisors.DatumOfIsIntegersLattice
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDiscreteValuationRingValuationSubringAtPrime
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AddMonoidHomEqZeroOfEventually
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CMModel.LatticeJInt.main` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FIsIntegralJOfNonrealMultiplier.lean&line=14#L14)
-/
theorem _root_.GlobalTheory.T.isIntegral_j_of_nonreal_multiplier : ∀ (L : PeriodPair) (β : ℂ), MulStable L β → β.im ≠ 0 → _root_.IsIntegral ℤ (latticeCurve L).j := by
  first | exact @GlobalTheory.CMModel.LatticeJInt.main | exact GlobalTheory.CMModel.LatticeJInt.main | (intros; apply GlobalTheory.CMModel.LatticeJInt.main <;> assumption)
