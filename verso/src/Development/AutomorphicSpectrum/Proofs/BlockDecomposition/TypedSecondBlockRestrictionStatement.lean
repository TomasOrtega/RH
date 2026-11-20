import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TypedSecondBlockRestriction

import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FinStable
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.InducedTensorMap
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.CompanionTheory.LimV
open scoped ContDiff
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FTypedSecondBlockRestriction.lean&line=62#L62)
-/
theorem _root_.GlobalTheory.T.typed_second_block_restriction : ∀ {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {r s : ℕ} (k : Kinf E (r + s)) (t : GL (Fin (r + s)) (Af E)) (K : Subgroup (GL (Fin (r + s)) (Af E))) (W : Submodule ℂ (Kinf E (r + s) → ℂ)), IsOpen (K : Set (GL (Fin (r + s)) (Af E))) → FiniteDimensional ℂ W → ∃ (K₂ : Subgroup (GL (Fin s) (Af E))) (W₂ : Submodule ℂ (Kinf E s → ℂ)), IsOpen (K₂ : Set (GL (Fin s) (Af E))) ∧ FiniteDimensional ℂ W₂ ∧ ∀ f ∈ typeF K W, ∀ x : GA E r, (fun y : GA E s => f (lev (Ad E) r s (x, y) * cf (r + s) k t)) ∈ typeF K₂ W₂ := by
  first | exact @GlobalTheory.CompanionTheory.LimV.SliceR.slice_right | exact GlobalTheory.CompanionTheory.LimV.SliceR.slice_right | (intros; apply GlobalTheory.CompanionTheory.LimV.SliceR.slice_right <;> assumption)
