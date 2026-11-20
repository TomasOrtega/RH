import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoordinateDividesOnNonzeroLocusSection
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.UnifAlong
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.ThetaDiv.div_of_mem_nonzeroLocus` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FCoordinateDividesOnNonzeroLocusSection.lean&line=22#L22)
-/
theorem _root_.GlobalTheory.T.coordinate_divides_on_nonzeroLocus_section : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : ZH.RatModel o Ω) (δ : LB M.Z) {I : Type} (t : I → δ.Sec) (th : I → Ω), δ.IsLB → ZM.SecCoord δ t M.pt th → ∀ (a : I) (z : M.Z), z ∈ nonzeroLocus (t a) → M.Div th a z := by
  first | exact @GlobalTheory.ThetaDiv.div_of_mem_nonzeroLocus | exact GlobalTheory.ThetaDiv.div_of_mem_nonzeroLocus | (intros; apply GlobalTheory.ThetaDiv.div_of_mem_nonzeroLocus <;> assumption)
