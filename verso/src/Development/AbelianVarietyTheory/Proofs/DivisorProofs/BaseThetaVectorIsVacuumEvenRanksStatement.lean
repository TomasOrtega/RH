import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseThetaVectorIsVacuumEvenRanks
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetRefinement
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FBaseThetaVectorIsVacuumEvenRanks.lean&line=31#L31)
-/
theorem _root_.GlobalTheory.T.base_theta_vector_is_vacuum_even_ranks : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ), TaylorLogMetric.adm1 D → GL3Theta.InducedCMType D → TaylorLogMetric.IsCurveIdeal D cc → TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ → B.kc.YFinite → ∀ N N' : ℕ, Even N → Even N' → StandardLatticesGL3.ThetaVectorUpToUnits D (TaylorLogMetric.tor0 D cc δ) (B.ω₀ / 2) (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N') (B.thZero N N') := by
  first | exact @GlobalTheory.BaseVacuum.thetaVectorUpToUnits_thZero_of_even | exact GlobalTheory.BaseVacuum.thetaVectorUpToUnits_thZero_of_even | (intros; apply GlobalTheory.BaseVacuum.thetaVectorUpToUnits_thZero_of_even <;> assumption)
