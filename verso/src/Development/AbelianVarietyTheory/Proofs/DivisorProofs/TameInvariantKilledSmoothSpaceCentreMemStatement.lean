import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TameInvariantKilledSmoothSpaceCentreMem
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemKilled
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FundamentalDomainMeasureFinite
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalCentreAnnihilatorCompatibleMaps
open NumberField GlobalTheory.CuspRep GlobalTheory.AutGrowth
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FTameInvariantKilledSmoothSpaceCentreMem.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.tameInvariantKilledSmoothSpace_centre_mem : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (b : ℕ) (L : Subgroup (GL (Fin b) (Af E))) (W : Submodule ℂ (Kinf E b → ℂ)), FiniteDimensional ℂ W → ∀ (q : (E →+* ℂ) → ℂ → Polynomial ℂ) (z : Module.End ℂ (Sm E b)), z ∈ Zalg E b → ∀ ψ ∈ GlobalTheory.CapKilled.space E b L W q, z ψ ∈ GlobalTheory.CapKilled.space E b L W q := by
  first | exact @GlobalTheory.CapKilled.zalg_mem_space | exact GlobalTheory.CapKilled.zalg_mem_space | (intros; apply GlobalTheory.CapKilled.zalg_mem_space <;> assumption)
