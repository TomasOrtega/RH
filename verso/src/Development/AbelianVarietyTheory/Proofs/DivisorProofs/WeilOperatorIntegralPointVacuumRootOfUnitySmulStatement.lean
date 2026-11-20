import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilOperatorIntegralPointVacuumRootOfUnitySmul
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetVecEq
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum GlobalTheory.FunObj.StdDatum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.FunObj.StdDatum.vacuum_int_root_of_unity` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FWeilOperatorIntegralPointVacuumRootOfUnitySmul.lean&line=15#L15)
-/
theorem _root_.GlobalTheory.T.weilOperator_integral_point_vacuum_rootOfUnity_smul : ∀ (D : D7) (δ : ℂ), Crv D ⊤ δ → ∀ {a d : ℕ} (e0 : VC D a d → ℂ), e0 ∈ Th D (tor0 D ⊤ δ) (stdL D a) (stdL D d) → ∀ (W : WeilO D ⊤ δ a d e0) (r : GA D a), r ∈ intG D a → ∃ c : ℂ, (∃ m : ℕ, 0 < m ∧ c ^ m = 1) ∧ W.Om r 1 e0 = c • e0 := by
  first | exact @GlobalTheory.FunObj.StdDatum.vacuum_int_root_of_unity | exact GlobalTheory.FunObj.StdDatum.vacuum_int_root_of_unity | (intros; apply GlobalTheory.FunObj.StdDatum.vacuum_int_root_of_unity <;> assumption)
