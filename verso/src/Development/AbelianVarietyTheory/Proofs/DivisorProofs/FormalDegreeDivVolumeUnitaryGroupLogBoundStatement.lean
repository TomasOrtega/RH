import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalDegreeDivVolumeUnitaryGroupLogBound
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalDegreeUpperC
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.VolUFactProdMulLe
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows GlobalTheory.LowRow
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.LowRow.formalDeg_div_volU_log_bound` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FFormalDegreeDivVolumeUnitaryGroupLogBound.lean&line=34#L34)
-/
theorem _root_.GlobalTheory.T.formalDegree_div_volume_unitaryGroup_log_bound : ∀ (r n : ℕ) (d : ℝ) (lam : Fin r → ℝ), 1 ≤ r → 3 ≤ n → 0 ≤ d → StrictAnti lam → (∀ a b, |lam a - lam b| ≤ d + n + 3) → 0 < ReciprocityTheory.ChartRestriction.DS.volU r ∧ 0 < (∏ a : Fin r, ∏ b ∈ Finset.univ.filter (fun b : Fin r => a < b), |lam a - lam b|) / (∏ a : Fin r, ∏ b ∈ Finset.univ.filter (fun b : Fin r => a < b), (((b : ℕ) : ℝ) - ((a : ℕ) : ℝ))) ∧ Real.log ((∏ a : Fin r, ∏ b ∈ Finset.univ.filter (fun b : Fin r => a < b), |lam a - lam b|) / (∏ a : Fin r, ∏ b ∈ Finset.univ.filter (fun b : Fin r => a < b), (((b : ℕ) : ℝ) - ((a : ℕ) : ℝ))) / ReciprocityTheory.ChartRestriction.DS.volU r) ≤ 2 + (r : ℝ) ^ 2 * Real.log (2 * Real.sqrt 2 * (r : ℝ) ^ 2 * n * (d + 2)) := by
  first | exact @GlobalTheory.LowRow.formalDeg_div_volU_log_bound | exact GlobalTheory.LowRow.formalDeg_div_volU_log_bound | (intros; apply GlobalTheory.LowRow.formalDeg_div_volU_log_bound <;> assumption)
