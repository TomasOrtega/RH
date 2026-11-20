import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NotSymEOfNe
import Development.AbelianVarietyTheory.Definitions.Divisors.UnifAlong
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsWithoutCohomology
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.HasBasisOfBasis

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UMin.FibExist

/- English proof (translation)
Introduce `X P R _ x`. Take `⟨P', g, hg, hgg, mul, t, ht⟩` from `GlobalTheory.polBaseChange_holds X (Sp R) x P`. Take `⟨t', ht', -⟩` from `GenericSectionBasis.exists_inv_iso t ht`. Use `⟨P', g, hgg, ⟨hg, fun T a b a₀ b₀ ha hb => ?_⟩, ⟨t', ht'⟩⟩` and prove the remaining obligations. Establish `ea : a₀ = toBase hg.w a` using `Over.OverMorphism.ext ha`.

Establish `eb : b₀ = toBase hg.w b` using `Over.OverMorphism.ext hb`. Substitute `ea eb` using the available equality. Rewrite using `[← mul]`. Both sides reduce to the same expression.
-/
theorem polFib_of_point : ∀ (X : Scheme.{0}) (P : PolAV X) (R : Type) [CommRing R] (x : Sp R ⟶ X),
    PolFib P.A P.L P.g x := by
  intro X P R _ x
  obtain ⟨P', g, hg, hgg, mul, t, ht⟩ := GlobalTheory.polBaseChange_holds X (Sp R) x P
  obtain ⟨t', ht', -⟩ := GenericSectionBasis.exists_inv_iso t ht
  refine ⟨P', g, hgg, ⟨hg, fun T a b a₀ b₀ ha hb => ?_⟩, ⟨t', ht'⟩⟩
  have ea : a₀ = toBase hg.w a := Over.OverMorphism.ext ha
  have eb : b₀ = toBase hg.w b := Over.OverMorphism.ext hb
  subst ea eb
  rw [← mul]
  rfl

end GlobalTheory.UMin.FibExist
