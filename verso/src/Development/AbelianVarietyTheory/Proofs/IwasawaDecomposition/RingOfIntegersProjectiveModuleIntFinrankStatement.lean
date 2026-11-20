import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RingOfIntegersProjectiveModuleIntFinrank
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEqAddOfRedVEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonnegSumSmulIntBilinFormToRealMemPsdConeStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsStrictIff
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.HostGeneratorPowFourTraceNormModEight
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.finite_projective_int_of_ringOfIntegers` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FRingOfIntegersProjectiveModuleIntFinrank.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.ringOfIntegers_projective_module_int_finrank : ∀ (E : Type) [Field E] [NumberField E] (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Module.Finite ℤ X ∧ Module.Projective ℤ X ∧ Module.finrank ℤ X = Module.finrank ℚ E * Module.finrank (𝓞 E) X := by
  first | exact @GlobalTheory.finite_projective_int_of_ringOfIntegers | exact GlobalTheory.finite_projective_int_of_ringOfIntegers | (intros; apply GlobalTheory.finite_projective_int_of_ringOfIntegers <;> assumption)
