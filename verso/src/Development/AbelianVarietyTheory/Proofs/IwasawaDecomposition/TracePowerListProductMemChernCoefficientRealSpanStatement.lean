import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TracePowerListProductMemChernCoefficientRealSpan
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SumSumEqSumPair
open MvPolynomial GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.GoodMetric.ChernSpan GlobalTheory.GoodMetric.PolyRep
open scoped Matrix
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FTracePowerListProductMemChernCoefficientRealSpan.lean&line=110#L110)
-/
theorem _root_.GlobalTheory.T.tracePowerListProduct_mem_chernCoefficientRealSpan : ∀ {ι : Type} [Fintype ι] (m : ι → ℕ) (n : ℕ) (S : Type) [CommRing S] [Algebra ℝ S] (l : List (ι × ℕ)), (∀ x ∈ l, 1 ≤ x.2) → (l.map Prod.snd).sum = n → (fun A : Mat m S => trProd l A) ∈ Reach m n S := by
  first | exact @GlobalTheory.GoodMetric.ChernSpan.trProd_mem_reach | exact GlobalTheory.GoodMetric.ChernSpan.trProd_mem_reach | (intros; apply GlobalTheory.GoodMetric.ChernSpan.trProd_mem_reach <;> assumption)
