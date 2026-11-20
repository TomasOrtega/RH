import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowestDegreeComponentNonzero
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TprodMemTensSpan
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FLowestDegreeComponentNonzero.lean&line=160#L160)
-/
theorem _root_.GlobalTheory.T.lowest_degree_component_nonzero : ∀ (P Q R S : ℕ) (x : ℚ) (k k' : ℕ), P ≤ R → Q ≤ S → 0 < k → 0 < k' → x - Formalism.BasicNotions.TH.cPair R S = k → x + Formalism.BasicNotions.TH.cPair R S = k' → GlobalTheory.KFixIrr.lowOne P Q R S x (P * k + Q * k') ≠ ⊥ := by
  first | exact @GlobalTheory.KFixIrr.lowOne_minors_ne_bot | exact GlobalTheory.KFixIrr.lowOne_minors_ne_bot | (intros; apply GlobalTheory.KFixIrr.lowOne_minors_ne_bot <;> assumption)
