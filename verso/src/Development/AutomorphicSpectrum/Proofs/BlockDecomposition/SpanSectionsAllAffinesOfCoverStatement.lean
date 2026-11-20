import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SpanSectionsAllAffinesOfCover
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KerOpsComm
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.GE.UV.span_range_app_eq_top_of_local` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FSpanSectionsAllAffinesOfCover.lean&line=46#L46)
-/
theorem _root_.GlobalTheory.T.span_sections_all_affines_of_cover : ∀ {X : AlgebraicGeometry.Scheme.{0}} {ι : Type} [Finite ι] {F : ι → X.Modules} {G : X.Modules}, (∀ i, (F i).IsQuasicoherent) → G.IsQuasicoherent → ∀ (φ : ∀ i, F i ⟶ G), (∀ x : X, ∃ U : X.affineOpens, x ∈ (U : X.Opens) ∧ Submodule.span Γ(X, U) (⋃ i, Set.range ((φ i).app U)) = ⊤) → ∀ (U : X.affineOpens), Submodule.span Γ(X, U) (⋃ i, Set.range ((φ i).app U)) = ⊤ := by
  first | exact @GlobalTheory.CompanionTheory.GE.UV.span_range_app_eq_top_of_local | exact GlobalTheory.CompanionTheory.GE.UV.span_range_app_eq_top_of_local | (intros; apply GlobalTheory.CompanionTheory.GE.UV.span_range_app_eq_top_of_local <;> assumption)
