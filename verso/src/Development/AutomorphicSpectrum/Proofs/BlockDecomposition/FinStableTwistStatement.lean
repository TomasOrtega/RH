import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FinStableTwist
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FinStable
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.InducedTensorMap
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.CompanionTheory.LimV
open scoped ContDiff
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FFinStableTwist.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.finStable_twist : ∀ {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {N : ℕ} (U : Submodule ℂ (Sm E N)) (z : ℂ), FinStable U → FinStable (tw U z) := by
  first | exact @GlobalTheory.CompanionTheory.LimV.finStable_tw | exact GlobalTheory.CompanionTheory.LimV.finStable_tw | (intros; apply GlobalTheory.CompanionTheory.LimV.finStable_tw <;> assumption)
