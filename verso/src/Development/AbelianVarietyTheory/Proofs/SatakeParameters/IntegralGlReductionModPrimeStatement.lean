import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntegralGlReductionModPrime
import Mathlib
import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.exists_GL_redV_of_mem_GLint` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FSatakeParameters%2FIntegralGlReductionModPrime.lean&line=80#L80)
-/
theorem _root_.GlobalTheory.T.integral_gl_reduction_mod_prime : ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (n : ℕ) (P : HeightOneSpectrum (𝓞 E)) (κ : Sp E n ≃ₗ[E] Sp E n), κ ∈ GLint E n P → ∃ h : GL (Fin n) (𝓞 E ⧸ P.asIdeal), ∀ x ∈ stdAt E n P, redV P (κ x) = h.1.mulVec (redV P x) := by
  first | exact @GlobalTheory.exists_GL_redV_of_mem_GLint | exact GlobalTheory.exists_GL_redV_of_mem_GLint | (intros; apply GlobalTheory.exists_GL_redV_of_mem_GLint <;> assumption)
