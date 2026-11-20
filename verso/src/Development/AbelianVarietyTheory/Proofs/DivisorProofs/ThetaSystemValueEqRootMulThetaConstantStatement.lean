import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSystemValueEqRootMulThetaConstant
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.RigGen
open AlgebraicGeometry CategoryTheory GlobalTheory.ZH
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.ZH.EvRoot.ev_eq_root_mul_th` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FThetaSystemValueEqRootMulThetaConstant.lean&line=154#L154)
-/
theorem _root_.GlobalTheory.T.theta_system_value_eq_root_mul_theta_constant : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (x : S.Gam) (j : S.J), ∃ (y : S.Gam) (u : Ω) (k : ℕ), 0 < k ∧ u ^ k = 1 ∧ S.ev x j = u * S.th y := by
  first | exact @GlobalTheory.ZH.EvRoot.ev_eq_root_mul_th | exact GlobalTheory.ZH.EvRoot.ev_eq_root_mul_th | (intros; apply GlobalTheory.ZH.EvRoot.ev_eq_root_mul_th <;> assumption)
