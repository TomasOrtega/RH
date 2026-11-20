import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalValueFirstClopenPartition
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ScaledBoxRadiiAtEntry
open ValuativeRel Matrix GlobalTheory.SplitFlip GlobalTheory.FullRankCoinv GlobalTheory.RankCoinv GlobalTheory.NormalCore
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FPrincipalValueFirstClopenPartition.lean&line=17#L17)
-/
theorem _root_.GlobalTheory.T.principal_value_first_clopen_partition : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n d : ℕ) (Bf : fullRk k n d →ₗ[ℂ] fullRk k n d →ₗ⋆[ℂ] ℂ) (ι : Type) (s : Finset ι) (Kf : ι → Set (Matrix (Fin n) (Fin d) k)) (B₁ B₂ : Set (Matrix (Fin n) (Fin d) k)), B₁.indicator (1 : Matrix (Fin n) (Fin d) k → ℂ) ∈ fullRk k n d → (∀ i ∈ s, IsClopen (Kf i)) → (↑s : Set ι).PairwiseDisjoint Kf → B₁ = (⋃ i ∈ s, Kf i) → pv Bf B₁ B₂ = ∑ i ∈ s, pv Bf (Kf i) B₂ := by
  first | exact @GlobalTheory.NormalCore.pv_sum_left_clopen | exact GlobalTheory.NormalCore.pv_sum_left_clopen | (intros; apply GlobalTheory.NormalCore.pv_sum_left_clopen <;> assumption)
