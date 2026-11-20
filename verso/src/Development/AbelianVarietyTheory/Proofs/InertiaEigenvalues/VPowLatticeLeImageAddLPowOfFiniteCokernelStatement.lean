import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.VPowLatticeLeImageAddLPowOfFiniteCokernel
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ImageStableDegreeBounds
open PowerSeries GlobalTheory.BK
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.LiftCoker.vPow_mem_imL_add_lPow` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FVPowLatticeLeImageAddLPowOfFiniteCokernel.lean&line=14#L14)
-/
theorem _root_.GlobalTheory.T.vPow_lattice_le_image_add_lPow_of_finite_cokernel : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (κ : Type) [Fintype κ] [DecidableEq κ] (η H : ℕ) (D₁ : BKDat O K l e a ι η H) (D₂ : BKDat O K l e a κ η H) (F : BKHom D₁ D₂), IsFiniteLength (A O K) F.coker → ∀ b : ℕ, 1 ≤ b → H + η + b ≤ l → ∀ x ∈ D₂.L, ∃ y ∈ D₁.L, ∃ z ∈ D₂.L, ((X : K⟦X⟧) ^ e) ^ (H + η + b) • x = F.app y + (l : K) ^ b • z := by
  first | exact @GlobalTheory.LiftCoker.vPow_mem_imL_add_lPow | exact GlobalTheory.LiftCoker.vPow_mem_imL_add_lPow | (intros; apply GlobalTheory.LiftCoker.vPow_mem_imL_add_lPow <;> assumption)
