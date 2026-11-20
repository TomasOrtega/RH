import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TracePowerProductRealSpanMulMem
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SumSumEqSumPair
open MvPolynomial GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.GoodMetric.ChernSpan GlobalTheory.GoodMetric.PolyRep
open scoped Matrix
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FTracePowerProductRealSpanMulMem.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.tracePowerProductRealSpan_mul_mem : ∀ {ι : Type} (m : ι → ℕ) (S : Type) [CommRing S] [Algebra ℝ S] (w w' : ℕ) (f g : Mat m S → S), f ∈ TrSpan m w S → g ∈ TrSpan m w' S → f * g ∈ TrSpan m (w + w') S := by
  first | exact @GlobalTheory.GoodMetric.ChernSpan.trSpan_mul | exact GlobalTheory.GoodMetric.ChernSpan.trSpan_mul | (intros; apply GlobalTheory.GoodMetric.ChernSpan.trSpan_mul <;> assumption)
