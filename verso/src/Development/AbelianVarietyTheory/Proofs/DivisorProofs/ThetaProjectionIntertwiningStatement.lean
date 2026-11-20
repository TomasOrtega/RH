import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaProjectionIntertwining
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IotaScalarOne
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.DetInv.proj_redC_intertwine` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FThetaProjectionIntertwining.lean&line=7#L7)
-/
theorem _root_.GlobalTheory.T.theta_projection_intertwining : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (C : Type) [Field C] [Algebra O C] (Λ : Type) [CommRing Λ] [Algebra ℤ_[p] Λ] (N h : ℕ) (f : RL p O Λ →+* O) (e e' : (Fin N → RL p O Λ) ≃ₗ[Ainf p O] (Fin h → Ainf p O)) (π π' : (Fin h → C) →ₗ[C] (Fin N → C)) (X : Matrix (Fin h) (Fin h) (Ainf p O)) (Y : Matrix (Fin N) (Fin N) (RL p O Λ)), IsProj C e f π → IsProj C e' f π' → IsMat e e' X Y → ∀ z, π' (redC C X z) = Y.map ((algebraMap O C).comp f) *ᵥ π z := by
  first | exact @GlobalTheory.DetInv.proj_redC_intertwine | exact GlobalTheory.DetInv.proj_redC_intertwine | (intros; apply GlobalTheory.DetInv.proj_redC_intertwine <;> assumption)
