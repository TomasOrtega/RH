import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelWeilFreeOfCongruentMatrix
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HypOneZeroZero
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FSiegelWeilFreeOfCongruentMatrix.lean&line=419#L419)
-/
theorem _root_.GlobalTheory.T.siegelWeilFree_of_congruent_matrix : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (n : ℕ) (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a b, σ (T b a) = T a b) (g : GL (Fin n) E) (T' : Matrix (Fin n) (Fin n) E) (hT' : ∀ a b, σ (T' b a) = T' a b), T' = cT (σ : E →+* E) (g : Matrix (Fin n) (Fin n) E) * T * g → SWFree σ J T' hT' → SWFree σ J T hT := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.Free.Scale.sw_free_scale | exact GlobalTheory.CompanionTheory.WeilSiegel.Free.Scale.sw_free_scale | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.Free.Scale.sw_free_scale <;> assumption)
