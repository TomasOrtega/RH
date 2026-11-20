import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CongruenceSubgroupAntitone
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CentredSegments.IrreducibleUnif
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.StandardFunctorsFiniteLength
open Filter Topology MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult ValuativeRel
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.CongruenceSubgroups.Km_antitone` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FCongruenceSubgroupAntitone.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.congruence_subgroup_antitone : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N m m' : ℕ), m ≤ m' → Zls.Km k N m' ≤ Zls.Km k N m := by
  first | exact @GlobalTheory.CompanionTheory.CongruenceSubgroups.Km_antitone | exact GlobalTheory.CompanionTheory.CongruenceSubgroups.Km_antitone | (intros; apply GlobalTheory.CompanionTheory.CongruenceSubgroups.Km_antitone <;> assumption)
