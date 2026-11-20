import Mathlib
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.UnitaryGroupWeakApproximationAtPrimes
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.IsHermForm
open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.UnRep.WeakApprox.weak_approximation` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FAdelicLatticeProofs%2FUnitaryGroupWeakApproximationAtPrimes.lean&line=252#L252)
-/
theorem _root_.GlobalTheory.T.unitaryGroup_weak_approximation_at_primes : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (c : E ≃ₐ[F] E) (n : ℕ) (G : Matrix (Fin n) (Fin n) E), IsHermForm c G → Module.finrank F E = 2 → ∀ L : Submodule (𝓞 E) (Fin n → E), L.FG → Submodule.span E (L : Set (Fin n → E)) = ⊤ → ∀ (g : GL (Fin n) (RA F E)) (N D : ℕ), IsUnA c G g.1 → 0 < N → 0 < D → ∃ γ : GL (Fin n) E, IsUnE c G γ.1 ∧ CongAtA F L N D (fm F γ.1 * g.1) := by
  first | exact @GlobalTheory.UnRep.WeakApprox.weak_approximation | exact GlobalTheory.UnRep.WeakApprox.weak_approximation | (intros; apply GlobalTheory.UnRep.WeakApprox.weak_approximation <;> assumption)
