import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullRankZetaSurjective
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullRk
open MeasureTheory GlobalTheory.SplitFlip
open scoped Matrix
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FFullRankZetaSurjective.lean&line=290#L290)
-/
theorem _root_.GlobalTheory.T.full_rank_zeta_surjective : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k] (n d : ℕ) (ν : kˣ →* ℂˣ), n ≤ d → GlobalTheory.SmGL.IsSmoothChar ν →
    ∀ f ∈ GlobalTheory.FullRankCoinv.indSp k n d ν,
    ∃ Ψ ∈ GlobalTheory.FullRankCoinv.fullRk k n d, ∀ h : GL (Fin d) k,
      smallF (haarVol (GlobalTheory.SplitWeil.KO k (Fin n))) ν Ψ (GlobalTheory.FullRankCoinv.Y0 k n d * h.val) = f h := by
  first | exact @GlobalTheory.FullRankOnto.exists_fullRk_smallF_eq | exact GlobalTheory.FullRankOnto.exists_fullRk_smallF_eq | (intros; apply GlobalTheory.FullRankOnto.exists_fullRk_smallF_eq <;> assumption)
