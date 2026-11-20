import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullRankZetaKernel
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullRk
open MeasureTheory GlobalTheory.SplitFlip
open scoped Matrix
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FFullRankZetaKernel.lean&line=23#L23)
-/
theorem _root_.GlobalTheory.T.full_rank_zeta_kernel : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k] (n d : ℕ) (ν : kˣ →* ℂˣ), n ≤ d → GlobalTheory.SmGL.IsSmoothChar ν →
    ∀ Ψ ∈ GlobalTheory.FullRankCoinv.fullRk k n d,
    (∀ h : GL (Fin d) k, smallF (haarVol (GlobalTheory.SplitWeil.KO k (Fin n))) ν Ψ (GlobalTheory.FullRankCoinv.Y0 k n d * h.val) = 0) →
      Ψ ∈ GlobalTheory.FullRankCoinv.augRk n d ν := by
  first | exact @GlobalTheory.FullRankCoinv.mem_augRk_of_fibre_eq_zero | exact GlobalTheory.FullRankCoinv.mem_augRk_of_fibre_eq_zero | (intros; apply GlobalTheory.FullRankCoinv.mem_augRk_of_fibre_eq_zero <;> assumption)
