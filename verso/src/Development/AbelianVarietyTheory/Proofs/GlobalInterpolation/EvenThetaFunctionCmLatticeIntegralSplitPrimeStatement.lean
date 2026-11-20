import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.EvenThetaFunctionCmLatticeIntegralSplitPrime
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LatIntZero
import Formalism.LocalToGlobal.KernelLattices.LateralTheory
open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker GlobalTheory.MomN
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.MomN.latInt_th0_of_split_prime` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FGlobalInterpolation%2FEvenThetaFunctionCmLatticeIntegralSplitPrime.lean&line=23#L23)
-/
theorem _root_.GlobalTheory.T.evenThetaFunction_cmLattice_integral_splitPrime : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ → ∀ (q : ℕ) [Fact q.Prime], q ≠ 2 → jacobiSym (-(D.host.d : ℤ)) q = 1 → Nat.Coprime (Ideal.absNorm cc) q → ∀ (ι : ℂ ≃+* ℂ_[q]) (δ₀ : ℂ) (θ : ℂ → ℂ) (Ω : ℂ_[q]), Per D.host.d ι δ₀ θ Ω → LatInt ι (Ω / ι δ₀) (lamOf D cc δ) B.th0 := by
  first | exact @GlobalTheory.MomN.latInt_th0_of_split_prime | exact GlobalTheory.MomN.latInt_th0_of_split_prime | (intros; apply GlobalTheory.MomN.latInt_th0_of_split_prime <;> assumption)
