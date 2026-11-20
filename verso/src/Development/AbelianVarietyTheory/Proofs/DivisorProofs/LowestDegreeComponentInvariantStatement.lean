import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowestDegreeComponentInvariant
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TprodMemTensSpan
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FLowestDegreeComponentInvariant.lean&line=90#L90)
-/
theorem _root_.GlobalTheory.T.lowest_degree_component_invariant : ∀ (P Q R S : ℕ) (x : ℚ) (d : ℕ) (Z : Formalism.BasicNotions.TH.Mat R S), Formalism.BasicNotions.TH.IsKC Z → ∀ f ∈ GlobalTheory.KFixIrr.lowOne P Q R S x d, Formalism.BasicNotions.TH.fockAct2 P Q R S Z f ∈ GlobalTheory.KFixIrr.lowOne P Q R S x d := by
  first | exact @GlobalTheory.KFixIrr.LowStable.fockAct2_lowOne | exact GlobalTheory.KFixIrr.LowStable.fockAct2_lowOne | (intros; apply GlobalTheory.KFixIrr.LowStable.fockAct2_lowOne <;> assumption)
