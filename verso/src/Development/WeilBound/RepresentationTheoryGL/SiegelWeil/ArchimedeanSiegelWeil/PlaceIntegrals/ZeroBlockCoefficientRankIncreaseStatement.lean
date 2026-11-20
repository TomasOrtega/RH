import Development.WeilBound.RepresentationTheoryGL.SiegelWeil.ArchimedeanSiegelWeil.PlaceIntegrals.ZeroBlockCoefficientRankIncrease
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HypOneZeroZero
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.WeilSiegel.HypStep.hyp_step` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FWeilBound%2FRepresentationTheoryGL%2FSiegelWeil%2FArchimedeanSiegelWeil%2FPlaceIntegrals%2FZeroBlockCoefficientRankIncrease.lean&line=78#L78)
-/
theorem _root_.GlobalTheory.T.zero_block_coefficient_rank_increase : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ n : ℕ, 1 ≤ n → 2 * n < M → ∀ (h₀ : ∀ a b : Fin n, σ ((0 : Matrix (Fin n) (Fin n) E) b a) = (0 : Matrix (Fin n) (Fin n) E) a b) (h₁ : ∀ a b : Fin (n + 1), σ ((0 : Matrix (Fin (n + 1)) (Fin (n + 1)) E) b a) = (0 : Matrix (Fin (n + 1)) (Fin (n + 1)) E) a b), (framesE σ J (0 : Matrix (Fin n) (Fin n) E)).Nonempty → SWFree σ J (0 : Matrix (Fin n) (Fin n) E) h₀ → SWFree σ (hypOne J) (0 : Matrix (Fin (n + 1)) (Fin (n + 1)) E) h₁ := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.HypStep.hyp_step | exact GlobalTheory.CompanionTheory.WeilSiegel.HypStep.hyp_step
