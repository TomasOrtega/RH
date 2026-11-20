import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CountableDoubledHermitianLagrangians
import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWeilDatumOOneOfRankZero
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.RawLift.lag_countable` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FCountableDoubledHermitianLagrangians.lean&line=18#L18)
-/
theorem _root_.GlobalTheory.T.countable_doubled_hermitian_lagrangians : ∀ (D : D7) (W : HSp D), Countable (Lag W) := by
  first | exact @GlobalTheory.RawLift.lag_countable | exact GlobalTheory.RawLift.lag_countable | (intros; apply GlobalTheory.RawLift.lag_countable <;> assumption)
