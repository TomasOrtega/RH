import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaSeriesInvariantRationalUnits
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OfE

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter PositivityTheory.Rg.Base1 GroundTheory.Global GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil
open scoped TensorProduct ENNReal NNReal Matrix Classical
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil.Th_ofE_mul` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FThetaSeriesInvariantRationalUnits.lean&line=32#L32)
-/
theorem _root_.GlobalTheory.T.theta_series_invariant_rational_units : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E] (φ : (Fin 1 → Fin 1 → Ainf F ⊗[F] E) → ℝ) (A : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin 1 → Fin 1 → Fv F v ⊗[F] E)) (q : Eˣ) (y : (AF F ⊗[F] E)ˣ), Th φ A (ofE q * y) = Th φ A y := by
  first | exact @GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil.Th_ofE_mul | exact GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil.Th_ofE_mul | (intros; apply GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil.Th_ofE_mul <;> assumption)
