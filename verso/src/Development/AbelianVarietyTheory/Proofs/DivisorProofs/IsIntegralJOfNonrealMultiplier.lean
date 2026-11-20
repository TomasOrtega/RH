import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DatumOfIsIntegersLattice
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDiscreteValuationRingValuationSubringAtPrime
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AddMonoidHomEqZeroOfEventually
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralJInvariantOfComplexMultiplication
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModLatTau
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModJTau
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

namespace GlobalTheory.CMModel.LatticeJInt

/- English proof (translation)
Introduce `L β hβ him`. Take `⟨c, τ, hτ⟩` from `ReciprocityTheory.ChartRestriction.L1.latTau L`. Establish `hj` using `GlobalTheory.JInt.main L c τ β hτ hβ him`. Rewrite `hj` using `[← ReciprocityTheory.ChartRestriction.L1.jInv_eq_jT hτ]`. Rewrite using `[latticeCurve_j_eq]`.

Conclude with `hj`.
-/
theorem main : ∀ (L : PeriodPair) (β : ℂ), MulStable L β → β.im ≠ 0 →
    _root_.IsIntegral ℤ (latticeCurve L).j := by
  intro L β hβ him
  obtain ⟨c, τ, hτ⟩ := ReciprocityTheory.ChartRestriction.L1.latTau L
  have hj := GlobalTheory.JInt.main L c τ β hτ hβ him
  rw [← ReciprocityTheory.ChartRestriction.L1.jInv_eq_jT hτ] at hj
  rw [latticeCurve_j_eq]
  exact hj

end GlobalTheory.CMModel.LatticeJInt
