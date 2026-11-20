import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothOfRelDimGeomConnectedDescendFieldExtension
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.KawamataViehweg
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineOpenPreimageOfIsPullback
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.FieldDescentSm.smoothOfRelativeDimension_and_geometricallyConnected_descend` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FSmoothOfRelDimGeomConnectedDescendFieldExtension.lean&line=14#L14)
-/
theorem _root_.GlobalTheory.T.smoothOfRelDim_geomConnected_descend_fieldExtension : ∀ (k E : Type) [Field k] [Field E] [Algebra k E] (Y X : Scheme.{0}) (p : Y ⟶ Sp k) (q : X ⟶ Sp E) (π : X ⟶ Y), IsPullback π q p (spMap (algebraMap k E)) → ∀ D : ℕ, Nonempty X → SmoothOfRelativeDimension D q → GeometricallyConnected q → SmoothOfRelativeDimension D p ∧ GeometricallyConnected p := by
  first | exact @GlobalTheory.FieldDescentSm.smoothOfRelativeDimension_and_geometricallyConnected_descend | exact GlobalTheory.FieldDescentSm.smoothOfRelativeDimension_and_geometricallyConnected_descend | (intros; apply GlobalTheory.FieldDescentSm.smoothOfRelativeDimension_and_geometricallyConnected_descend <;> assumption)
