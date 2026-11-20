import Mathlib
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.KsetTransitive
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsKMeas
open Matrix MeasureTheory Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 GlobalTheory.HCXi
open scoped ENNReal ComplexOrder
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FCovolumeBounds%2FKsetTransitive.lean&line=85#L85)
-/
theorem _root_.GlobalTheory.T.exists_mem_Kset_mul_mem_Pset_eq : ∀ k r : ℕ, 1 ≤ k → ∀ g ∈ GV k r, ∃ κ ∈ Kset k r, ∃ p ∈ Pset k r, g = κ * p := by
  first | exact @GlobalTheory.HCXi.iwasawa | exact GlobalTheory.HCXi.iwasawa | (intros; apply GlobalTheory.HCXi.iwasawa <;> assumption)
