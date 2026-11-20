import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.DualLatticeMembershipTrace
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SumRhoEqTrace
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core GlobalTheory.CompanionTheory.SW.ThW
open scoped ENNReal NNReal MatrixGroups Kronecker
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.SW.ThW.toA_mem_perp_latN_iff` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=CompanionTheory%2FSpectralGeometry%2FLocalGlobalProofs%2FAdelicAnalysis%2FDualLatticeMembershipTrace.lean&line=36#L36)
-/
theorem _root_.GlobalTheory.T.dual_lattice_membership_trace : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (A F) ℂ), IsStdChar F ψ → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (B : Matrix ι ι F) (b : Module.Basis (InfinitePlace F) ℤ (𝓞 F)) (N : ℕ), 0 < N → ∀ y : ι → F, toA y ∈ perp (chiB ψ (Bf B)) (latN F ι N : Set (ι → A F)) ↔ ∀ i v, ∃ m : ℤ, (N : ℚ) * Algebra.trace ℚ F ((b v : F) * (B *ᵥ y) i) = m := by
  first | exact @GlobalTheory.CompanionTheory.SW.ThW.toA_mem_perp_latN_iff | exact GlobalTheory.CompanionTheory.SW.ThW.toA_mem_perp_latN_iff | (intros; apply GlobalTheory.CompanionTheory.SW.ThW.toA_mem_perp_latN_iff <;> assumption)
