import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsKernelEquivConjugatePoints
import Development.AbelianVarietyTheory.Definitions.Divisors.DatumOfIsIntegersLattice
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDiscreteValuationRingValuationSubringAtPrime
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AddMonoidHomEqZeroOfEventually
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsKernelEquivConjugatePoints.lean&line=18#L18)
-/
theorem _root_.GlobalTheory.T.exists_kernel_equiv_conjugate_points : ∀ (L : PeriodPair) (σ : ℂ ≃+* ℂ) (α : ℂ) (S S' : Finset ℂ), L.g₂ = σ L.g₂ → L.g₃ = σ L.g₃ → MulStable L α → IsKerReps L α S → IsKerReps L (σ α) S' → ∃ e : S ≃ S', ∀ t : S, GlobalTheory.ConjPoint.IsConj L L σ (t : ℂ) (e t : ℂ) := by
  first | exact @GlobalTheory.ConjPoint.exists_equiv_kerReps_isConj | exact GlobalTheory.ConjPoint.exists_equiv_kerReps_isConj | (intros; apply GlobalTheory.ConjPoint.exists_equiv_kerReps_isConj <;> assumption)
