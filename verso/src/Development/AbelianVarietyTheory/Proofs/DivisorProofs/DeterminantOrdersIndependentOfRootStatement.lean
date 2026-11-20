import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeterminantOrdersIndependentOfRoot
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsDetEltOne
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.detData_indep_eps` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FDeterminantOrdersIndependentOfRoot.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.determinant_orders_independent_of_root : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O → ∀ (ε ε' : PreTilt O p) (Λ : Type) [CommRing Λ] [Algebra ℤ_[p] Λ] (ψ : RL p O Λ →+* RL p O Λ) (N : ℕ) (Δ : RL p O Λ) (a : (Λ →+* O) → ℕ) (c : (Λ →+* O) → C), Associated (xi ε) (xi ε') → Associated (mu ε) (mu ε') → IsDetElt ε ψ N Δ → HasOrders C ε N Δ a c → ∃ c' : (Λ →+* O) → C, IsDetElt ε' ψ N Δ ∧ HasOrders C ε' N Δ a c' ∧ ∀ σ, v (c' σ) = v (c σ) := by
  first | exact @GlobalTheory.detData_indep_eps | exact GlobalTheory.detData_indep_eps | (intros; apply GlobalTheory.detData_indep_eps <;> assumption)
