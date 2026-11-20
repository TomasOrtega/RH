import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TypedFirstBlockRestriction

import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FinStable
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.InducedTensorMap
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.CompanionTheory.LimV
open scoped ContDiff
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FTypedFirstBlockRestriction.lean&line=14#L14)
-/
theorem _root_.GlobalTheory.T.typed_first_block_restriction : ∀ {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {r s : ℕ} (k : Kinf E (r + s)) (t : GL (Fin (r + s)) (Af E)) (K : Subgroup (GL (Fin (r + s)) (Af E))) (W : Submodule ℂ (Kinf E (r + s) → ℂ)), IsOpen (K : Set (GL (Fin (r + s)) (Af E))) → FiniteDimensional ℂ W → ∃ (K₁ : Subgroup (GL (Fin r) (Af E))) (W₁ : Submodule ℂ (Kinf E r → ℂ)), IsOpen (K₁ : Set (GL (Fin r) (Af E))) ∧ FiniteDimensional ℂ W₁ ∧ ∀ f ∈ typeF K W, ∀ y : GA E s, (fun x : GA E r => f (lev (Ad E) r s (x, y) * cf (r + s) k t)) ∈ typeF K₁ W₁ := by
  first | exact @GlobalTheory.CompanionTheory.LimV.SliceL.slice_typeF | exact GlobalTheory.CompanionTheory.LimV.SliceL.slice_typeF | (intros; apply GlobalTheory.CompanionTheory.LimV.SliceL.slice_typeF <;> assumption)
