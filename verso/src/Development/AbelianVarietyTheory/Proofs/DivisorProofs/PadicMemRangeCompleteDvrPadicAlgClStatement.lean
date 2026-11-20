import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PadicMemRangeCompleteDvrPadicAlgCl
import Mathlib
open IsLocalRing
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.PadicUnitBall.padic_mem_range` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FPadicMemRangeCompleteDvrPadicAlgCl.lean&line=129#L129)
-/
theorem _root_.GlobalTheory.T.padic_mem_range_complete_dvr_padicAlgCl : ∀ (p : ℕ) [Fact p.Prime] (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V], IsAdicComplete (maximalIdeal V) V → ∀ (κ : FractionRing V →+* PadicAlgCl p), (∀ x, ‖κ x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap V (FractionRing V))) → ∀ q : ℚ_[p], algebraMap ℚ_[p] (PadicAlgCl p) q ∈ κ.range := by
  first | exact @GlobalTheory.PadicUnitBall.padic_mem_range | exact GlobalTheory.PadicUnitBall.padic_mem_range | (intros; apply GlobalTheory.PadicUnitBall.padic_mem_range <;> assumption)
