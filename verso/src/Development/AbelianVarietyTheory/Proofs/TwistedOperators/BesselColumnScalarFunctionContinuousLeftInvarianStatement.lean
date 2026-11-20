import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselColumnScalarFunctionContinuousLeftInvariant
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.StepUnfold
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FBesselColumnScalarFunctionContinuousLeftInvariant.lean&line=14#L14)
-/
theorem _root_.GlobalTheory.T.besselColumnScalarFunction_continuous_leftInvariant : Big fun ch => ∀ a, Continuous (colFn ch a) ∧
    ∀ γ ∈ GQ (ch.G.V (.top 0)), ∀ g, colFn ch a (γ * g) = colFn ch a g := by
  first | exact @GlobalTheory.RowClaim.colFn_cont_left | exact GlobalTheory.RowClaim.colFn_cont_left | (intros; apply GlobalTheory.RowClaim.colFn_cont_left <;> assumption)
