import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemOfClosedPointsClosedFibreMem
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.QuasiCompact
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Mum.mem_of_closedPoints_closedFibre_mem` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FMemOfClosedPointsClosedFibreMem.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.mem_of_closedPoints_closedFibre_mem' : ∀ (R : Type) [CommRing R] [IsLocalRing R] (T : Scheme.{0}) (q : T ⟶ Sp R), LocallyOfFiniteType q → ∀ U : T.Opens, (∀ x : T, IsClosed ({x} : Set T) → q x = closedPoint R → x ∈ U) → ∀ x : T, q x = closedPoint R → x ∈ U := by
  first | exact @GlobalTheory.Mum.mem_of_closedPoints_closedFibre_mem | exact GlobalTheory.Mum.mem_of_closedPoints_closedFibre_mem | (intros; apply GlobalTheory.Mum.mem_of_closedPoints_closedFibre_mem <;> assumption)
