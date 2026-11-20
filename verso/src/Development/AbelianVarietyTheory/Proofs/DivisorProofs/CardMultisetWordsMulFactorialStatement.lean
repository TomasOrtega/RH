import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardMultisetWordsMulFactorial
import Mathlib
open scoped Classical
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FCardMultisetWordsMulFactorial.lean&line=32#L32)
-/
theorem _root_.GlobalTheory.T.card_multiset_words_mul_factorial : ∀ {I : Type} [Fintype I] (k : ℕ) (ν : I → ℕ), ∑ i, ν i = k → (Finset.univ.filter (fun s : Fin k → I => ∀ i, (List.ofFn s).count i = ν i)).card * ∏ i, (ν i).factorial = k.factorial := by
  first | exact @GlobalTheory.MultinomialCount.card_mul_prod_factorial | exact GlobalTheory.MultinomialCount.card_mul_prod_factorial | (intros; apply GlobalTheory.MultinomialCount.card_mul_prod_factorial <;> assumption)
