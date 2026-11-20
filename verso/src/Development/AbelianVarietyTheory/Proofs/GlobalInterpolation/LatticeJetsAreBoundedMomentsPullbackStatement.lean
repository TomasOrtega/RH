import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LatticeJetsAreBoundedMomentsPullback
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LatIntZero
open GlobalTheory.MomOne GlobalTheory.MomN PowerSeries
open scoped ComplexConjugate
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.MomN.latInt_pull` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FGlobalInterpolation%2FLatticeJetsAreBoundedMomentsPullback.lean&line=24#L24)
-/
theorem _root_.GlobalTheory.T.latticeJetsAreBoundedMoments_pullback : ∀ (q : ℕ) [Fact q.Prime] (ι : ℂ ≃+* ℂ_[q]) (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (V' : Type) [NormedAddCommGroup V'] [NormedSpace ℂ V'] (ω : ℂ_[q]) (Λ : AddSubgroup V) (Λ' : AddSubgroup V') (g : V' →L[ℂ] V) (G : V → ℂ), ContDiff ℂ ⊤ G → (∀ x ∈ Λ', ∃ s : ℕ, Nat.Coprime s q ∧ s • g x ∈ Λ) → LatInt ι ω Λ G → LatInt ι ω Λ' fun z => G (g z) := by
  first | exact @GlobalTheory.MomN.latInt_pull | exact GlobalTheory.MomN.latInt_pull | (intros; apply GlobalTheory.MomN.latInt_pull <;> assumption)
