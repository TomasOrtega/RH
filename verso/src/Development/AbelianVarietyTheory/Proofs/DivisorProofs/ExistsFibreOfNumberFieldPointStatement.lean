import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFibreOfNumberFieldPoint
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCochFrame
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
open AlgebraicGeometry CategoryTheory Limits NumberField MonoidalCategory CartesianMonoidalCategory MonObj Matrix Topology
open Formalism.BasicNotions ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CubeFib GlobalTheory.LieMet GlobalTheory.LieHt GlobalTheory.LocM.Frm GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh GlobalTheory.Toroidal GlobalTheory.HeightParts GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.BdFib
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsFibreOfNumberFieldPoint.lean&line=36#L36)
-/
theorem _root_.GlobalTheory.T.exists_fibre_of_number_field_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Z : Model Xo c (algebraMap (𝓞 c.F) c.F)) (K : Type) [Field K] [NumberField K] (yK : Sp K ⟶ gen Z), yK (IsLocalRing.closedPoint K) ∉ genBd Z → ∃ (φ : Fib K) (m : CubeMap φ.G Z.t.G), FibAt Z.t (yK ≫ genι Z) φ m := by
  first | exact @GlobalTheory.InteriorFibre.exists_fibAt_of_not_mem_genBd | exact GlobalTheory.InteriorFibre.exists_fibAt_of_not_mem_genBd | (intros; apply GlobalTheory.InteriorFibre.exists_fibAt_of_not_mem_genBd <;> assumption)
