import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointDefinedOverSubfieldOfIsIntegralHom
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SepAtBIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSectionOfIsIsoRestrict
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FPointDefinedOverSubfieldOfIsIntegralHom.lean&line=26#L26)
-/
theorem _root_.GlobalTheory.T.pointDefinedOverSubfield_of_isIntegralHom : ∀ {X Y : Scheme.{0}} (f : X ⟶ Y) [IsIntegralHom f] {K : Type} [Field K] (k₀ : Subfield K), IsAlgClosed k₀ → ∀ P : Sp K ⟶ X, GlobalTheory.UChart.DefOver k₀ (P ≫ f) → GlobalTheory.UChart.DefOver k₀ P := by
  first | exact @GlobalTheory.DefOverIntegral.defOver_of_isIntegralHom | exact GlobalTheory.DefOverIntegral.defOver_of_isIntegralHom | (intros; apply GlobalTheory.DefOverIntegral.defOver_of_isIntegralHom <;> assumption)
