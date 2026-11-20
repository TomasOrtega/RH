import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EtaKEqNegOneOfNotNorm
import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitting
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.JR.NonNorm.etaK_eq_neg_one` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FEtaKEqNegOneOfNotNorm.lean&line=82#L82)
-/
theorem _root_.GlobalTheory.T.etaK_eq_neg_one_of_not_norm : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E), IsField A.K → IsField A.L → ∀ s : A.Kˣ, (¬ ∃ y : A.L, A.NL y = s) → A.etaK s = -1 := by
  first | exact @GlobalTheory.JR.NonNorm.etaK_eq_neg_one | exact GlobalTheory.JR.NonNorm.etaK_eq_neg_one | (intros; apply GlobalTheory.JR.NonNorm.etaK_eq_neg_one <;> assumption)
