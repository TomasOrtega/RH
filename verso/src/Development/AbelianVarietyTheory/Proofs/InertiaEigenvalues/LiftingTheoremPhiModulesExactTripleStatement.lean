import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftingTheoremPhiModulesExactTriple
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ConductorExponents
open PowerSeries GlobalTheory.BK
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FLiftingTheoremPhiModulesExactTriple.lean&line=23#L23)
-/
theorem _root_.GlobalTheory.T.liftingTheorem_phiModules_exact_triple : GlobalTheory.IndefiniteRowSideFullHecke.ConductorExponents.Lifting := by
  first | exact @GlobalTheory.InertiaEigenvalues.lifting_along_exact_triple | exact GlobalTheory.InertiaEigenvalues.lifting_along_exact_triple | (intros; apply GlobalTheory.InertiaEigenvalues.lifting_along_exact_triple <;> assumption)
