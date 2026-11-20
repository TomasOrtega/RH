import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaloisPowMovesPadicRootOfUnity
import Mathlib
import Formalism.CharacterColumnKernels.StatementRho
import Formalism.GaloisCohomology.LocalTateDualityK
import ReciprocityTheory.Hypotheses.GalCohDefs
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevRepZApply
open ReciprocityTheory.Gal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.ShapeNeg.exists_pow_ne_rootOfUnity` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FExistsGaloisPowMovesPadicRootOfUnity.lean&line=69#L69)
-/
theorem _root_.GlobalTheory.T.exists_galois_pow_moves_padic_rootOfUnity : ∀ {p : ℕ} [Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)}, FiniteDimensional ℚ_[p] K →
    ∀ k : ℕ, 0 < k → ∃ (σ : Formalism.GaloisCohomology.GK p K) (n : ℕ) (ζ : PadicAlgCl p), ζ ^ (p ^ n) = 1 ∧ (σ ^ k) ζ ≠ ζ := by
  first | exact @GlobalTheory.ShapeNeg.exists_pow_ne_rootOfUnity | exact GlobalTheory.ShapeNeg.exists_pow_ne_rootOfUnity | (intros; apply GlobalTheory.ShapeNeg.exists_pow_ne_rootOfUnity <;> assumption)
