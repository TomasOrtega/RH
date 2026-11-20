import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LatticeJetsAreBoundedMomentsOfSpanImagQuadratic
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LatIntZero
open GlobalTheory.MomOne GlobalTheory.MomN PowerSeries
open scoped ComplexConjugate
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FGlobalInterpolation%2FLatticeJetsAreBoundedMomentsOfSpanImagQuadratic.lean&line=31#L31)
-/
theorem _root_.GlobalTheory.T.latticeJetsAreBoundedMoments_of_span_imagQuadratic : ∀ (q : ℕ) [Fact q.Prime] (ι : ℂ ≃+* ℂ_[q]) (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (d : ℕ) (ω : ℂ_[q]) (Λ : AddSubgroup V) (κ : Type) [Fintype κ] (b : κ → V) (G : V → ℂ), d.Prime → d % 16 = 7 → Split d q → (∀ x ∈ Λ, ∃ s : ℕ, Nat.Coprime s q ∧ ∃ c : κ → ℂ, (∀ i, InOK d (c i)) ∧ (s : ℂ) • x = ∑ i, c i • b i) → MomInt ι (fun i => ι.symm ω • b i) G → LatInt ι ω Λ G := by
  first | exact @GlobalTheory.MomN.latInt_of_span | exact GlobalTheory.MomN.latInt_of_span | (intros; apply GlobalTheory.MomN.latInt_of_span <;> assumption)
