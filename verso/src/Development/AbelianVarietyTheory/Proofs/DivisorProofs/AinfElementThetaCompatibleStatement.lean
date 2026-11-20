import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AinfElementThetaCompatible
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IotaScalarOne
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FAinfElementThetaCompatible.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.ainf_element_theta_compatible : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O → ∀ (ε : PreTilt O p), IsPrimitiveRoot (root ε).untilt p → ∀ (Λ : Type) [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ] [Algebra ℤ_[p] Λ] [Module.Finite ℤ_[p] Λ] [FaithfulSMul ℤ_[p] Λ], ∀ a : Ainf p O, a ≠ 0 → (inA a : RL p O Λ) ∈ nonZeroDivisors (RL p O Λ) := by
  first | exact @GlobalTheory.DetInv.inA_mem_nonZeroDivisors | exact GlobalTheory.DetInv.inA_mem_nonZeroDivisors | (intros; apply GlobalTheory.DetInv.inA_mem_nonZeroDivisors <;> assumption)
