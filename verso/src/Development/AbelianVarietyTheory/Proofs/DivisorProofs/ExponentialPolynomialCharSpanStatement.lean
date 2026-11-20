import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExponentialPolynomialCharSpan
import Mathlib
open Polynomial
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.character_mem_span_translates` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExponentialPolynomialCharSpan.lean&line=141#L141)
-/
theorem _root_.GlobalTheory.T.exponential_polynomial_char_span : ∀ (G : Type) [CommGroup G] (L : G → ℝ), (∀ x y, L (x * y) = L x + L y) → (∃ t, L t ≠ 0) → ∀ (ι : Type) [Fintype ι] (χ : ι → G →* ℂˣ), Function.Injective χ → ∀ (P : ι → ℂ[X]) (i₀ : ι), P i₀ ≠ 0 → (fun t => ((χ i₀ t : ℂˣ) : ℂ)) ∈ Submodule.span ℂ (Set.range fun s : G => fun t : G => ∑ i, (P i).eval ((L (s * t) : ℝ) : ℂ) * ((χ i (s * t) : ℂˣ) : ℂ)) := by
  first | exact @GlobalTheory.character_mem_span_translates | exact GlobalTheory.character_mem_span_translates | (intros; apply GlobalTheory.character_mem_span_translates <;> assumption)
