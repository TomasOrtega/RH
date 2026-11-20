import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMinimalOfDiscrEqUnitMulNegCube
import Development.AbelianVarietyTheory.Definitions.Divisors.DatumOfIsIntegersLattice
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDiscreteValuationRingValuationSubringAtPrime
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AddMonoidHomEqZeroOfEventually
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CMModel.isMinimal_of_discr_eq_unit_mul_neg_cube` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FIsMinimalOfDiscrEqUnitMulNegCube.lean&line=12#L12)
-/
theorem _root_.GlobalTheory.T.isMinimal_of_discr_eq_unit_mul_neg_prime_cube : ∀ (p : ℕ) (F : Type) [Field F] [NumberField F] (w : HeightOneSpectrum (𝓞 F)) (W : WeierstrassCurve F) (u : (w.valuationSubringAtPrime F)ˣ), (p : 𝓞 F) ∉ w.asIdeal ^ 3 → W.IsIntegral (w.valuationSubringAtPrime F) → W.Δ = ((u : w.valuationSubringAtPrime F) : F) * -(p : F) ^ 3 → W.IsMinimal (w.valuationSubringAtPrime F) := by
  first | exact @GlobalTheory.CMModel.isMinimal_of_discr_eq_unit_mul_neg_cube | exact GlobalTheory.CMModel.isMinimal_of_discr_eq_unit_mul_neg_cube | (intros; apply GlobalTheory.CMModel.isMinimal_of_discr_eq_unit_mul_neg_cube <;> assumption)
