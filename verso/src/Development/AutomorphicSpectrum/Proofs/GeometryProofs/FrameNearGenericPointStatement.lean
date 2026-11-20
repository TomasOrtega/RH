import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FrameNearGenericPoint
import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LevelSectionsExactKernelLocusOpen
open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FGeometryProofs%2FFrameNearGenericPoint.lean&line=44#L44)
-/
theorem _root_.GlobalTheory.T.frame_near_generic_point : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E] (L : Lat ξ E) (T : Set (Cpt ξ)) (r : ℕ) (V : Submodule Ω E) (b : Fin r → E), IsCptGen ξ → (⟨genPt ξ, specializes_rfl⟩ : Cpt ξ) ∈ T → L.IsVBOn T r V → LinearIndependent Ω b → Submodule.span Ω (Set.range b) = V → ∃ W : X.Opens, genPt ξ ∈ W ∧ ∀ q ∈ T, q.1 ∈ W → L.IsFrameAt b q := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.FrameOpen.isFrameAt_near_genPt | exact GlobalTheory.CompanionTheory.Ar.Flat.FrameOpen.isFrameAt_near_genPt | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.FrameOpen.isFrameAt_near_genPt <;> assumption)
