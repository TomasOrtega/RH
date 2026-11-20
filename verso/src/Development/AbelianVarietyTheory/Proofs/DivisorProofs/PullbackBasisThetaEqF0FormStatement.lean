import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackBasisThetaEqF0Form
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlkLat
import Formalism.LocalToGlobal.InertKernelTheory.StatementAlg
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.BaseVacuum
open Classical
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FPullbackBasisThetaEqF0Form.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.pullback_basis_theta_eq_F0_form : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (n n' : ℕ) (z : TaylorLogMetric.VC D (n * 2) (n' * 2)), StandardLatticesGL3.pullB D (TaylorLogMetric.tor0 D cc δ) (bas B n n') (GL3Theta.th0 (TaylorLogMetric.lamOf D cc δ) (B.ω₀ / 2)) z = F0 B.L B.ω₀ (Ix D n n') (phi B n n' z) := by
  first | exact @GlobalTheory.BaseVacuum.pullback_basis_theta_eq_F0 | exact GlobalTheory.BaseVacuum.pullback_basis_theta_eq_F0 | (intros; apply GlobalTheory.BaseVacuum.pullback_basis_theta_eq_F0 <;> assumption)
