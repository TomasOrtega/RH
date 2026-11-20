import Mathlib
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.EqOfLamEq
import Development.AbelianVarietyTheory.Definitions.CMLattices.LamLetters
import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CM.PairingInj.eq_of_lamEq` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FCubicalLineBundles%2FEqOfLamEq.lean&line=40#L40)
-/
theorem _root_.GlobalTheory.T.eq_of_lamEq_polAV : Out.Laws → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : Out.PolAV S) (X : Over S) (f g : X ⟶ P.A), LamEq P.L f (𝟙 P.A) P.L g (𝟙 P.A) → f = g := by
  first | exact @GlobalTheory.CM.PairingInj.eq_of_lamEq | exact GlobalTheory.CM.PairingInj.eq_of_lamEq | (intros; apply GlobalTheory.CM.PairingInj.eq_of_lamEq <;> assumption)
