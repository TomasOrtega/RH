import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearIndependentComplexMap
import Mathlib
open Matrix
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.linearIndependent_real_map_of_fieldEmb` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FLinearIndependentComplexMap.lean&line=6#L6)
-/
theorem _root_.GlobalTheory.T.linear_independent_complex_map : ∀ {E : Type} [Field E] {r n : ℕ} (τ : E →+* ℂ) (e : Fin n → Matrix (Fin r) (Fin r) E), LinearIndependent E e → LinearIndependent ℝ (fun i => (e i).map τ) := by
  first | exact @GlobalTheory.linearIndependent_real_map_of_fieldEmb | exact GlobalTheory.linearIndependent_real_map_of_fieldEmb | (intros; apply GlobalTheory.linearIndependent_real_map_of_fieldEmb <;> assumption)
