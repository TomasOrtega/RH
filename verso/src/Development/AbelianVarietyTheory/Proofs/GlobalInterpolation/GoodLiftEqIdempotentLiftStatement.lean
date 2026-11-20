import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.GoodLiftEqIdempotentLift
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LatIntZero
import Formalism.LocalToGlobal.KernelLattices.DeterminantCokernelCount.CokernelIndexFactors.StatementB
open GlobalTheory.MomN Formalism.L2.Ker.JMB
open scoped ComplexConjugate
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FGlobalInterpolation%2FGoodLiftEqIdempotentLift.lean&line=63#L63)
-/
theorem _root_.GlobalTheory.T.goodLift_eq_idempotent_lift : ∀ (q : ℕ) [Fact q.Prime] (lam : Qbar →+* ℂ_[q]) (g : ℕ) (S : Setup g) (r : ℕ) (b : Fin r → Fin g → ℂ) (e : (Fin g → ℂ) → ℂ) (t : Fin g → ℂ), S.Ok → GlobalTheory.MomOne.Split S.d q → S.NNBasis q b → S.IsTheta e → ∀ N₀ : ℕ, 0 < N₀ → Nat.Coprime N₀ q → (N₀ : ℂ) • t ∈ S.La → ∀ (n : ℕ), ∀ y ∈ AddSubgroup.closure {y : Fin g → ℂ | ∃ κ ∈ OK S.d, ‖lamA lam (conj κ)‖ ≤ (q : ℝ) ^ (-(2 * n : ℤ)) ∧ ∃ x ∈ S.La, y = (κ * (N₀ : ℂ) / (q : ℂ) ^ n) • x}, (∃ z : ℤ, (beta S.d S.Hm y y).re = z) ∧ ∃ (m : ℕ) (eps : ℂ) (yt : Fin r → Fin (q ^ n)), IsIdem lam S.d m eps ∧ 2 * n ≤ m ∧ (∀ i, ∃ z : ℤ, (hf S.Hm (eps • b i) t).im = z) ∧ opW S.d S.Hm y (opU S.Hm t e) = opW S.d S.Hm (liftY q n eps b yt) (opU S.Hm t e) ∧ ∀ a : Fin r → ℕ, kap S.Hm (∑ i, (a i : ℂ) • b i) y = kap S.Hm (vecA n b fun i => (a i : ℤ_[q])) (liftY q n eps b yt) := by
  first | exact @GlobalTheory.MomN.goodLift_eq | exact GlobalTheory.MomN.goodLift_eq | (intros; apply GlobalTheory.MomN.goodLift_eq <;> assumption)
