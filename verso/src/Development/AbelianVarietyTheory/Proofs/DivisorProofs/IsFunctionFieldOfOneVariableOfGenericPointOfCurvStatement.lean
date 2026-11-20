import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFunctionFieldOfOneVariableOfGenericPointOfCurv
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatPath

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Nef.CurveFF.isFF_of_isGenOver` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FIsFunctionFieldOfOneVariableOfGenericPointOfCurv.lean&line=56#L56)
-/
theorem _root_.GlobalTheory.T.isFunctionFieldOfOneVariable_of_genericPointOfCurve : ∀ (k K : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field K] [Algebra k K] (C : Scheme.{0}) [Algebra k Γ(C, ⊤)] (x : Sp K ⟶ C), IsGenOver k x →
  IsFF k K := by
  first | exact @GlobalTheory.Nef.CurveFF.isFF_of_isGenOver | exact GlobalTheory.Nef.CurveFF.isFF_of_isGenOver | (intros; apply GlobalTheory.Nef.CurveFF.isFF_of_isGenOver <;> assumption)
