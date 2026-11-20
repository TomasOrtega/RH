import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDerivationEqOneOfPowMem
open TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsDerivationEqOneOfPowMem.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.exists_derivation_eq_one_of_pow_mem' : ∀ (p : ℕ) [Fact p.Prime] (K : Type) [Field K] [CharP K p] (L : Subfield K) (f : K), f ∉ L → f ^ p ∈ L → IntermediateField.adjoin L ({f} : Set K) = ⊤ → ∃ D : Derivation L K K, D f = 1 := by
  first | exact @GlobalTheory.exists_derivation_eq_one_of_pow_mem | exact GlobalTheory.exists_derivation_eq_one_of_pow_mem | (intros; apply GlobalTheory.exists_derivation_eq_one_of_pow_mem <;> assumption)
