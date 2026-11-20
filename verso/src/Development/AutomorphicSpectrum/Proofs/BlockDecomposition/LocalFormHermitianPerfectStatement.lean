import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalFormHermitianPerfect
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsHermRingRat
open NumberField IsDedekindDomain Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.KFin
open Formalism.UG (cT)
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.KFin.isHerm_isPerfect_hR` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FLocalFormHermitianPerfect.lean&line=87#L87)
-/
theorem _root_.GlobalTheory.T.local_form_hermitian_perfect : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}, IsCMExt F E σ → IsHermND σ J → ∀ (v : HeightOneSpectrum (𝓞 F)), IsHerm (sigR (Fv F v) σ) (hR (Fv F v) σ J) ∧ IsPerfect (hR (Fv F v) σ J) := by
  first | exact @GlobalTheory.CompanionTheory.KFin.isHerm_isPerfect_hR | exact GlobalTheory.CompanionTheory.KFin.isHerm_isPerfect_hR | (intros; apply GlobalTheory.CompanionTheory.KFin.isHerm_isPerfect_hR <;> assumption)
