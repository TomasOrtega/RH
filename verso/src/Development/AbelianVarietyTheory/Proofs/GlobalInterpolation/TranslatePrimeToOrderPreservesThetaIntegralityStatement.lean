import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TranslatePrimeToOrderPreservesThetaIntegrality
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LatIntZero
import Formalism.LocalToGlobal.KernelLattices.DeterminantCokernelCount.CokernelIndexFactors.StatementB
open GlobalTheory.MomN Formalism.L2.Ker.JMB
open scoped ComplexConjugate
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FGlobalInterpolation%2FTranslatePrimeToOrderPreservesThetaIntegrality.lean&line=60#L60)
-/
theorem _root_.GlobalTheory.T.translate_primeToOrder_preserves_theta_integrality : ∀ (q : ℕ) [Fact q.Prime] (ι : ℂ ≃+* ℂ_[q]) (δ₀ : ℂ) (θ : ℂ → ℂ) (Ω : ℂ_[q]) (g : ℕ) (S : Setup g) (e : (Fin g → ℂ) → ℂ) (t : Fin g → ℂ), Per S.d ι δ₀ θ Ω → S.Ok → GlobalTheory.MomOne.Split S.d q → S.IsTheta e → S.AlgJets δ₀ e → S.PrimeTo q t → LatInt ι (Ω / ι δ₀) S.La.toAddSubgroup e → LatInt ι (Ω / ι δ₀) S.La.toAddSubgroup (opU S.Hm t e) := by
  first | exact @GlobalTheory.MomTrans.latInt_translate | exact GlobalTheory.MomTrans.latInt_translate | (intros; apply GlobalTheory.MomTrans.latInt_translate <;> assumption)
