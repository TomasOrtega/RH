import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsFiniteDeterminingSet

import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FinStable
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.InducedTensorMap
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.CompanionTheory.LimV
open scoped ContDiff
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.LimV.exists_finset_separating_points` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FExistsFiniteDeterminingSet.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.exists_finite_determining_set : ∀ {A : Type} (W : Submodule ℂ (A → ℂ)), FiniteDimensional ℂ W → ∃ S : Finset A, ∀ w ∈ W, (∀ a ∈ S, w a = 0) → w = 0 := by
  first | exact @GlobalTheory.CompanionTheory.LimV.exists_finset_separating_points | exact GlobalTheory.CompanionTheory.LimV.exists_finset_separating_points | (intros; apply GlobalTheory.CompanionTheory.LimV.exists_finset_separating_points <;> assumption)
