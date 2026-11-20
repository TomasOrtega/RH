import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocalIndexAtSinglePlace
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PlaceEqOneOfNotMem
open NumberField Matrix IsDedekindDomain GlobalTheory.CompanionTheory.Ar.Cusp.LocFrame
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Ar.Cusp.LocIndex.relIndex_locAt` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FGeometryProofs%2FLocalIndexAtSinglePlace.lean&line=113#L113)
-/
theorem _root_.GlobalTheory.T.local_index_at_single_place : ∀ (L : Type) [Field L] [NumberField L] (W : Type) [AddCommGroup W] [Module (𝓞 L) W] (v : FinitePlace L) (A B : Submodule (𝓞 L) W), B ≤ A → B.toAddSubgroup.relIndex A.toAddSubgroup ≠ 0 → (∀ w : FinitePlace L, w ≠ v → locAt w A = locAt w B) → (locAt v B).toAddSubgroup.relIndex (locAt v A).toAddSubgroup = B.toAddSubgroup.relIndex A.toAddSubgroup := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.LocIndex.relIndex_locAt | exact GlobalTheory.CompanionTheory.Ar.Cusp.LocIndex.relIndex_locAt | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.LocIndex.relIndex_locAt <;> assumption)
