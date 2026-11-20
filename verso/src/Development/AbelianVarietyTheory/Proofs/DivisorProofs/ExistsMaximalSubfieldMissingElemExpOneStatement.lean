import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMaximalSubfieldMissingElemExpOne
open TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsMaximalSubfieldMissingElemExpOne.lean&line=31#L31)
-/
theorem _root_.GlobalTheory.T.exists_maximal_subfield_missing_elem_expOne : ∀ (p : ℕ) [Fact p.Prime] (K : Type) [Field K] [CharP K p] (F : Subfield K), (∀ y : K, y ^ p ∈ F) → ∀ f : K, f ∉ F → ∃ L : Subfield K, F ≤ L ∧ f ∉ L ∧ IntermediateField.adjoin L ({f} : Set K) = ⊤ := by
  first | exact @GlobalTheory.cfmax_main | exact GlobalTheory.cfmax_main | (intros; apply GlobalTheory.cfmax_main <;> assumption)
