import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftWeightSizesEventuallyAlongFamily
import Formalism.SharpRestriction.ParConsts
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalDegreeUpperC
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows GlobalTheory.LowRow
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FThetaLiftWeightSizesEventuallyAlongFamily.lean&line=16#L16)
-/
theorem _root_.GlobalTheory.T.thetaLift_weightSizes_eventually_along_family : ∀ (eps : ℝ) (Fm : FamP eps), ∃ x0 : ℝ, ∀ x, Fm.x1 < x → x0 ≤ x → ∀ (i : Fm.Ix x) j, Sizes (Fm.D x i) j (Fm.L x i).sc.b := by
  first | exact @GlobalTheory.LowRow.weightSizes_along | exact GlobalTheory.LowRow.weightSizes_along | (intros; apply GlobalTheory.LowRow.weightSizes_along <;> assumption)
