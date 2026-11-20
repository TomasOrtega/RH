import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TeichmullerTiltMinusOneDvdOfThetaFrobeniusZero
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.MemLoc.mu_dvd_of_theta_frob` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FTeichmullerTiltMinusOneDvdOfThetaFrobeniusZero.lean&line=259#L259)
-/
theorem _root_.GlobalTheory.T.teichmullerTiltMinusOne_dvd_of_theta_frobenius_zero : ∀ (l : ℕ) [Fact l.Prime], ∀ e : Per.Fl l, IsEps e → ∀ a : Per.Ainf l, (∀ n : ℕ, Per.θ l ((Per.φA l)^[n] a) = 0) → mu e ∣ a := by
  first | exact @GlobalTheory.MemLoc.mu_dvd_of_theta_frob | exact GlobalTheory.MemLoc.mu_dvd_of_theta_frob | (intros; apply GlobalTheory.MemLoc.mu_dvd_of_theta_frob <;> assumption)
