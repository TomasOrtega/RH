import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniformizerPowTendstoZero
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CentredSegments.IrreducibleUnif
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.StandardFunctorsFiniteLength
open Filter Topology MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult ValuativeRel
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.UnifPow.tendsto_unifU_pow` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FUniformizerPowTendstoZero.lean&line=16#L16)
-/
theorem _root_.GlobalTheory.T.uniformizer_pow_tendsto_zero : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], Filter.Tendsto (fun n : ℕ => ((Zls.unifU k : kˣ) : k) ^ n) Filter.atTop (nhds 0) := by
  first | exact @GlobalTheory.CompanionTheory.UnifPow.tendsto_unifU_pow | exact GlobalTheory.CompanionTheory.UnifPow.tendsto_unifU_pow | (intros; apply GlobalTheory.CompanionTheory.UnifPow.tendsto_unifU_pow <;> assumption)
