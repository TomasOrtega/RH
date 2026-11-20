import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundedOfIsIntegral
import Mathlib
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FBoundedOfIsIntegral.lean&line=198#L198)
-/
theorem _root_.GlobalTheory.T.exists_valuation_bound_of_isIntegral_mem_adjoin : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (N : Matrix (Fin n) (Fin n) (w.adicCompletion E)), N.charpoly.Separable → ∃ c : WithZero (Multiplicative ℤ), ∀ g ∈ Algebra.adjoin (w.adicCompletion E) {N}, IsIntegral (w.adicCompletionIntegers E) g → ∀ i j, Valued.v (g i j) ≤ c := by
  first | exact @GlobalTheory.LocBounded.bounded_of_isIntegral | exact GlobalTheory.LocBounded.bounded_of_isIntegral | (intros; apply GlobalTheory.LocBounded.bounded_of_isIntegral <;> assumption)
