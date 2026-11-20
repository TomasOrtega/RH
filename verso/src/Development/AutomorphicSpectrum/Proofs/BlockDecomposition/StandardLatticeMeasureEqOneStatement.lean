import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StandardLatticeMeasureEqOne
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OfE
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter PositivityTheory.Rg.Base1 GroundTheory.Global GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil
open scoped TensorProduct ENNReal NNReal Matrix Classical
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil.CoordLat.coordW_latV_one` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FStandardLatticeMeasureEqOne.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.standard_lattice_measure_eq_one : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)), (∀ v, IsStdV v (lam v)) → ∀ v, coordW (Fv F v) b (lam v) 1 1 (latV b v) = 1 := by
  first | exact @GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil.CoordLat.coordW_latV_one | exact GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil.CoordLat.coordW_latV_one | (intros; apply GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil.CoordLat.coordW_latV_one <;> assumption)
