import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FrobeniusNontrivialOnInertQuadratic
import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GlobSpecOfExists
open NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.L2.Col Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FSatakeParameters%2FFrobeniusNontrivialOnInertQuadratic.lean&line=7#L7)
-/
theorem _root_.GlobalTheory.T.frobenius_nontrivial_on_inert_quadratic : ∀ (E : Type) [Field E] [NumberField E] (M : Subfield E) (p : ℕ) (Q : HeightOneSpectrum (𝓞 E)) (φ : E ≃ₐ[ℚ] E), p.Prime → Module.finrank ℚ M = 2 → (Ideal.span {((p : ℕ) : 𝓞 M)}).IsPrime → ((p : ℕ) : 𝓞 E) ∈ Q.asIdeal → (∀ x : 𝓞 E, φ • x - x ^ p ∈ Q.asIdeal) → ∃ x ∈ M, φ x ≠ x := by
  first | exact @GlobalTheory.frobenius_moves_quadratic_subfield_of_inert | exact GlobalTheory.frobenius_moves_quadratic_subfield_of_inert | (intros; apply GlobalTheory.frobenius_moves_quadratic_subfield_of_inert <;> assumption)
