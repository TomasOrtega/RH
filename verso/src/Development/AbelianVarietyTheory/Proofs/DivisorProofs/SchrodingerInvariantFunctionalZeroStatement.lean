import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerInvariantFunctionalZero
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPairingStdP
open scoped SchwartzMap
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FSchrodingerInvariantFunctionalZero.lean&line=185#L185)
-/
theorem _root_.GlobalTheory.T.schrodinger_invariant_functional_zero : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (P : V → V → ℝ), GlobalTheory.ArchUniq.IsPairing P → ∀ (T : 𝓢(V, ℂ) →L[ℂ] ℂ) (g : 𝓢(V, ℂ)), g ≠ 0 → (∀ (w : V × V) (g₁ : 𝓢(V, ℂ)), ⇑g₁ = GlobalTheory.ArchUniq.schrF P w ⇑g → T g₁ = 0) → T = 0 := by
  first | exact @GlobalTheory.SchrIrred.eq_zero_of_schrF | exact GlobalTheory.SchrIrred.eq_zero_of_schrF | (intros; apply GlobalTheory.SchrIrred.eq_zero_of_schrF <;> assumption)
