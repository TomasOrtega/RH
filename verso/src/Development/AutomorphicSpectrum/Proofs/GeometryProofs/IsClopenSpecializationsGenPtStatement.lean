import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsClopenSpecializationsGenPt
import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsCptGen
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Ar.isClopen_setOf_genPt_specializes` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FGeometryProofs%2FIsClopenSpecializationsGenPt.lean&line=52#L52)
-/
theorem _root_.GlobalTheory.T.isClopen_specializations_genPt : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) [IsLocallyNoetherian X], IsCptGen ξ → IsClopen {q : X | genPt ξ ⤳ q} := by
  first | exact @GlobalTheory.CompanionTheory.Ar.isClopen_setOf_genPt_specializes | exact GlobalTheory.CompanionTheory.Ar.isClopen_setOf_genPt_specializes | (intros; apply GlobalTheory.CompanionTheory.Ar.isClopen_setOf_genPt_specializes <;> assumption)
