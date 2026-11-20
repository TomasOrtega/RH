import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.ChainOfKernelsUnique
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsSemiAbelianOfCharts
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.QuotientIsAbelianSchemeOfQuotientScheme
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.QuotAbelian

/- English proof (translation)
Introduce `S 𝒰 A G _ _ Q B _ ψ hA hG hQ hψ hB`. Establish `: IsZariskiLocalAtTarget @Smooth.{0}` using `HasRingHomProperty.instIsZariskiLocalAtTarget (P := @Smooth)`. Establish `hsm : Smooth G.hom` using `GlobalTheory.GroupGlue.of_charts @Smooth hψ fun j => (hB j).smooth`. Establish `hpr : IsProper G.hom` using `GlobalTheory.GroupGlue.of_charts @IsProper hψ fun j => (hB j).proper`. Establish `hw : Q.left ≫ G.hom = A.hom` using `Over.w Q`.

Use `hA.geomConnected` as an intermediate fact. Establish `: GeometricallyConnected (Q.left ≫ G.hom)` using `by rw [hw]; infer_instance`. Conclude with `⟨hG, hsm, hpr, GlobalTheory.AbelianQuotient.geometricallyConnected_of_comp Q.left G.hom⟩`.
-/
theorem isAbelianScheme_of_charts_of_surjective :
    ∀ (S : Scheme.{0}) (𝒰 : S.OpenCover.{0}) (A G : Over S) [GrpObj A] [GrpObj G] (Q : A ⟶ G)
    (B : ∀ j, Over (𝒰.X j)) [∀ j, GrpObj (B j)] (ψ : ∀ j, (B j).left ⟶ G.left),
    IsAbelianScheme A → IsCommMonObj G → Surjective Q.left → (∀ j, IsPullback (ψ j) (B j).hom G.hom (𝒰.f j)) →
    (∀ j, IsAbelianScheme (B j)) → IsAbelianScheme G := by
  intro S 𝒰 A G _ _ Q B _ ψ hA hG hQ hψ hB
  have : IsZariskiLocalAtTarget @Smooth.{0} := HasRingHomProperty.instIsZariskiLocalAtTarget (P := @Smooth)
  have hsm : Smooth G.hom := GlobalTheory.GroupGlue.of_charts @Smooth hψ fun j => (hB j).smooth
  have hpr : IsProper G.hom := GlobalTheory.GroupGlue.of_charts @IsProper hψ fun j => (hB j).proper
  have hw : Q.left ≫ G.hom = A.hom := Over.w Q
  have := hA.geomConnected
  have : GeometricallyConnected (Q.left ≫ G.hom) := by rw [hw]; infer_instance
  exact ⟨hG, hsm, hpr, GlobalTheory.AbelianQuotient.geometricallyConnected_of_comp Q.left G.hom⟩

end GlobalTheory.QuotAbelian
