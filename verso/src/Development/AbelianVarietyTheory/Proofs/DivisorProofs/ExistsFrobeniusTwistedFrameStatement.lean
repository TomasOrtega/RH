import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFrobeniusTwistedFrame
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IotaScalarOne
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.DetInv.frame_twist` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsFrobeniusTwistedFrame.lean&line=92#L92)
-/
theorem _root_.GlobalTheory.T.exists_frobenius_twisted_frame : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (Λ : Type) [CommRing Λ] [Algebra ℤ_[p] Λ] (N h : ℕ) (ψ : RL p O Λ →+* RL p O Λ) (ρ : Λ → Matrix (Fin h) (Fin h) (Ainf p O)) (e : (Fin N → RL p O Λ) ≃ₗ[Ainf p O] (Fin h → Ainf p O)), IsPsi ψ → IsFrame ρ e → ∃ e' : (Fin N → RL p O Λ) ≃ₗ[Ainf p O] (Fin h → Ainf p O), IsFrame (fun l => (ρ l).map (phiInv p O)) e' ∧ ∀ w, e' (fun i => ψ (w i)) = fun j => phiInv p O (e w j) := by
  first | exact @GlobalTheory.DetInv.frame_twist | exact GlobalTheory.DetInv.frame_twist | (intros; apply GlobalTheory.DetInv.frame_twist <;> assumption)
