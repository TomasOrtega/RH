import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceRingOfIntegersActionLatticeEq
import Mathlib
open NumberField
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.LatticeTrace.trace_lattice_eq` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FTraceRingOfIntegersActionLatticeEq.lean&line=7#L7)
-/
theorem _root_.GlobalTheory.T.trace_ringOfIntegers_action_lattice_eq : ∀ (F : Type) [Field F] [NumberField F] (O : Type) [Ring O] [Algebra (𝓞 F) O] (La : Type) [AddCommGroup La] [Module O La] [Module.Free ℤ La] [Module.Finite ℤ La] (k : ℕ), Module.finrank ℤ La = k * Module.finrank ℚ F → ∀ c : 𝓞 F, ((LinearMap.trace ℤ La (DistribMulAction.toAddMonoidHom La (algebraMap (𝓞 F) O c)).toIntLinearMap : ℤ) : ℂ) = (k : ℂ) * ∑ τ : F →+* ℂ, τ (c : F) := by
  first | exact @GlobalTheory.LatticeTrace.trace_lattice_eq | exact GlobalTheory.LatticeTrace.trace_lattice_eq | (intros; apply GlobalTheory.LatticeTrace.trace_lattice_eq <;> assumption)
