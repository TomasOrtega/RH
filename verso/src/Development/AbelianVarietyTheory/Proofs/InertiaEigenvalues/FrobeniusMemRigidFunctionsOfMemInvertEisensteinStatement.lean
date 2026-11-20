import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusMemRigidFunctionsOfMemInvertEisenstein
import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsAlgebraMapEqRoot
open PowerSeries GlobalTheory.BK Filter Topology
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FFrobeniusMemRigidFunctionsOfMemInvertEisenstein.lean&line=63#L63)
-/
theorem _root_.GlobalTheory.T.frobenius_mem_rigidFunctions_of_mem_invertEisenstein : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] (l e : ℕ) [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] (k : ℝ), 1 / ((e : ℝ) * l) < k → ∀ f ∈ invE l e (A O K), frob K l f ∈ R O K l k := by
  first | exact @GlobalTheory.BK.frob_mem_R_of_mem_invE_A | exact GlobalTheory.BK.frob_mem_R_of_mem_invE_A | (intros; apply GlobalTheory.BK.frob_mem_R_of_mem_invE_A <;> assumption)
