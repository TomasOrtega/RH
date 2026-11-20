import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MorphismToProjSpaceSectionPullbackComp
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ISupNonzeroLocusEmbH
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsLiftClosedImmersionOfDense
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Mum.toProj_secPull_secPull` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FMorphismToProjSpaceSectionPullbackComp.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.morphismToProjSpace_sectionPullback_comp : ∀ (R : Type) [CommRing R] (N : ℕ) (X Y Z : Scheme.{0}) (L : LB X) (s : Fin (N + 1) → L.Sec) (h : Y ⟶ X) (g : Z ⟶ Y) (f : Z ⟶ Sp R) (hs₁ : ⨆ i, nonzeroLocus (GlobalTheory.secPull (GlobalTheory.secPull (s i) h) g) = ⊤) (hs₂ : ⨆ i, nonzeroLocus (GlobalTheory.secPull (s i) (g ≫ h)) = ⊤), GlobalTheory.ProjSpace.toProj f (fun i => GlobalTheory.secPull (GlobalTheory.secPull (s i) h) g) hs₁ = GlobalTheory.ProjSpace.toProj f (fun i => GlobalTheory.secPull (s i) (g ≫ h)) hs₂ := by
  first | exact @GlobalTheory.Mum.toProj_secPull_secPull | exact GlobalTheory.Mum.toProj_secPull_secPull | (intros; apply GlobalTheory.Mum.toProj_secPull_secPull <;> assumption)
