import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NotMemHalfLatticeOfOddMultiplier
import Development.AbelianVarietyTheory.Definitions.Divisors.DatumOfIsIntegersLattice
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDiscreteValuationRingValuationSubringAtPrime
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AddMonoidHomEqZeroOfEventually
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CMModel.mem_lattice_of_even_kerReps` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FNotMemHalfLatticeOfOddMultiplier.lean&line=12#L12)
-/
theorem _root_.GlobalTheory.T.not_mem_half_lattice_of_odd_multiplier : ∀ (L : PeriodPair) (α a : ℂ) (S : Finset ℂ), α ≠ 0 → MulStable L α → IsKerReps L α S → Even S.card → α * a ∈ L.lattice → 2 * a ∈ L.lattice → a ∈ L.lattice := by
  first | exact @GlobalTheory.CMModel.mem_lattice_of_even_kerReps | exact GlobalTheory.CMModel.mem_lattice_of_even_kerReps | (intros; apply GlobalTheory.CMModel.mem_lattice_of_even_kerReps <;> assumption)
