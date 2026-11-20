import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RayNormAndModuleFormula
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OfE

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter PositivityTheory.Rg.Base1 GroundTheory.Global GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil
open scoped TensorProduct ENNReal NNReal Matrix Classical
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FRayNormAndModuleFormula.lean&line=27#L27)
-/
theorem _root_.GlobalTheory.T.ray_norm_and_module_formula : ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F → ∀ θ : ℝ →+* Ainf F, Continuous θ → ∀ r, IsRay θ r → (∀ (ε : ℝ) (w : InfinitePlace F), ‖θ ε w‖ = |ε|) ∧ ∀ δ : ℝ, 0 < δ → md (r δ) = δ ^ Module.finrank ℚ F := by
  first | exact @GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil.MdRay.norm_md_ray | exact GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil.MdRay.norm_md_ray | (intros; apply GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil.MdRay.norm_md_ray <;> assumption)
