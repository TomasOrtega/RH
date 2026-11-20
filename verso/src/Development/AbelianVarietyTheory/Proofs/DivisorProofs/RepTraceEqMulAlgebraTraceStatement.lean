import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepTraceEqMulAlgebraTrace
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SandwichMaps
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FRepTraceEqMulAlgebraTrace.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.rep_trace_eq_mul_algebra_trace : ∀ (p : ℕ) [Fact p.Prime] (Λ : Type) [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ] [Algebra ℤ_[p] Λ] [Module.Finite ℤ_[p] Λ] [FaithfulSMul ℤ_[p] Λ] (N h : ℕ), h = Module.finrank ℤ_[p] Λ * N → ∀ (ρ : Λ →ₐ[ℤ_[p]] Matrix (Fin h) (Fin h) ℤ_[p]) (a : Λ), (ρ a).trace = (N : ℤ_[p]) * Algebra.trace ℤ_[p] Λ a := by
  first | exact @GlobalTheory.traceOnLattice_eq_rank_mul_trace | exact GlobalTheory.traceOnLattice_eq_rank_mul_trace | (intros; apply GlobalTheory.traceOnLattice_eq_rank_mul_trace <;> assumption)
