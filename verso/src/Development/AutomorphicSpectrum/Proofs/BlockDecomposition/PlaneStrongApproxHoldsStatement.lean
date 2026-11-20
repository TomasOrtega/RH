import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PlaneStrongApproxHolds
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PlaneSupports.PlaneSupp
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published Sa2
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.PlaneSA.plane` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FPlaneStrongApproxHolds.lean&line=43#L43)
-/
theorem _root_.GlobalTheory.T.plane_strong_approx_holds : Sa2.PropPlane := by
  first | exact @GlobalTheory.CompanionTheory.PlaneSA.plane | exact GlobalTheory.CompanionTheory.PlaneSA.plane | (intros; apply GlobalTheory.CompanionTheory.PlaneSA.plane <;> assumption)
