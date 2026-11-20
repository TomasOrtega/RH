import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIdempotentStarEqOneSubOfNotIsField
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WHyp
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FExistsIdempotentStarEqOneSubOfNotIsField.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.exists_idempotent_star_eq_one_sub_of_not_isField : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E), IsField A.K → ¬ IsField A.L → ∃ e : A.L, e * e = e ∧ star e = 1 - e := by
  first | exact @GlobalTheory.JR.Hyp.exists_idempotent_of_not_isField | exact GlobalTheory.JR.Hyp.exists_idempotent_of_not_isField | (intros; apply GlobalTheory.JR.Hyp.exists_idempotent_of_not_isField <;> assumption)
