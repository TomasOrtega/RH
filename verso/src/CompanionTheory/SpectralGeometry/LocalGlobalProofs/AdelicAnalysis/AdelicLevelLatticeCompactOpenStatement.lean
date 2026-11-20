import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicLevelLatticeCompactOpen
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SumRhoEqTrace
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core GlobalTheory.CompanionTheory.SW.ThW
open scoped ENNReal NNReal MatrixGroups Kronecker
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=CompanionTheory%2FSpectralGeometry%2FLocalGlobalProofs%2FAdelicAnalysis%2FAdelicLevelLatticeCompactOpen.lean&line=31#L31)
-/
theorem _root_.GlobalTheory.T.adelic_level_lattice_compact_open : ∀ (F : Type) [Field F] [NumberField F] (ι : Type) [Fintype ι] [DecidableEq ι] (N : ℕ), 0 < N → IsCompact (latN F ι N : Set (ι → A F)) ∧ IsOpen (latN F ι N : Set (ι → A F)) ∧ ∀ a : ι → F, SB (indC N a) := by
  first | exact @GlobalTheory.CompanionTheory.SW.ThW.Lco.main | exact GlobalTheory.CompanionTheory.SW.ThW.Lco.main | (intros; apply GlobalTheory.CompanionTheory.SW.ThW.Lco.main <;> assumption)
