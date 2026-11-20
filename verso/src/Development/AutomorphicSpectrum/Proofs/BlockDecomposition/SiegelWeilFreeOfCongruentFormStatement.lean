import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelWeilFreeOfCongruentForm
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HypOneZeroZero
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.WeilSiegel.Free.Iso.swFree_of_isometry` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FSiegelWeilFreeOfCongruentForm.lean&line=374#L374)
-/
theorem _root_.GlobalTheory.T.siegelWeilFree_of_congruent_form : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (g : GL (Fin M) E) (J' : Matrix (Fin M) (Fin M) E), J' = cT (σ : E →+* E) (g : Matrix (Fin M) (Fin M) E) * J * g → ∀ (n : ℕ) (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a b, σ (T b a) = T a b), SWFree σ J' T hT → SWFree σ J T hT := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.Free.Iso.swFree_of_isometry | exact GlobalTheory.CompanionTheory.WeilSiegel.Free.Iso.swFree_of_isometry | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.Free.Iso.swFree_of_isometry <;> assumption)
