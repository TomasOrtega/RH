import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ClassSumPrincipalLevelEqConstMulClassSum
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevelLiftIsLiftPrincipalLevelDatumRealisation
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField GlobalTheory.ExportSeries
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1600000
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FClassSumPrincipalLevelEqConstMulClassSum.lean&line=72#L72)
-/
theorem _root_.GlobalTheory.T.classSum_principalLevel_eq_const_mul_classSum : ∀ (D : D7) (S T : HSp D) (B : Base S T), B.Good → S.SigOK → ∀ (ψ : Twist D Circle), ψ.Good → B.admitted ψ.Q →
    ∀ (ω : PairRep S T), B.IsWeil ψ.chi ω → ∀ (m : ℕ) (h₀ : Fin m → GA D S), IsClassSystem S ((GlobalTheory.FlatVecSum.princ B).levJ ψ) h₀ →
    ∀ (I : Type) [Fintype I] (h : I → GA D S), IsClassSystem S (B.levJ ψ) h →
    ∃ κ : ℂ, ∀ F ∈ B.formsC ψ, (GlobalTheory.FlatVecSum.princ B).classSum ω ψ h₀ F = κ • B.classSum ω ψ h F := by
  first | exact @GlobalTheory.ClassSumPrinc.classSum_princ_eq | exact GlobalTheory.ClassSumPrinc.classSum_princ_eq | (intros; apply GlobalTheory.ClassSumPrinc.classSum_princ_eq <;> assumption)
