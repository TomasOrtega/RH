import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsCoefficientSpaceDualDiscreteSeriesModelPos
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FactTypePrime
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Datum (InfFam)
open GlobalTheory.DefFree GlobalTheory.DefLift Polynomial
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.DualCoef.exists_dual_coef` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FExistsCoefficientSpaceDualDiscreteSeriesModelPos.lean&line=262#L262)
-/
theorem _root_.GlobalTheory.T.exists_coefficientSpace_dual_discreteSeriesModel_posDef : ∀ (D : D7) (θ : InfFam D) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S), IsInfFam θ → AllPlus M → ∃ (c : CoefA V) (pr : c.W →ₗ[ℂ] SmT M →ₗ[ℂ] ℂ), c.Is ∧ IsDualPair θ M c pr ∧ Function.Surjective pr := by
  first | exact @GlobalTheory.DualCoef.exists_dual_coef | exact GlobalTheory.DualCoef.exists_dual_coef | (intros; apply GlobalTheory.DualCoef.exists_dual_coef <;> assumption)
