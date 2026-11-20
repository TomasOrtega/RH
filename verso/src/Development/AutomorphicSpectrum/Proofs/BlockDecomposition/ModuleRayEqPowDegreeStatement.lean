import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ModuleRayEqPowDegree
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThPr
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PureAdelicFunctionFormulaStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BoundedDenominatorsCompactIdeleSetStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter GroundTheory.Global PositivityTheory.Rg.Base1 GlobalTheory.CompanionTheory.BasePsi
open scoped ENNReal NNReal Classical
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.BasePsi.md_ray` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FModuleRayEqPowDegree.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.module_ray_eq_pow_degree : ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F → ∀ (θ : ℝ →+* Ainf F) (r : ℝ → (AF F)ˣ), IsRay θ r →
    ∀ δ : ℝ, 0 < δ → md (r δ) = δ ^ Module.finrank ℚ F := by
  first | exact @GlobalTheory.CompanionTheory.BasePsi.md_ray | exact GlobalTheory.CompanionTheory.BasePsi.md_ray | (intros; apply GlobalTheory.CompanionTheory.BasePsi.md_ray <;> assumption)
