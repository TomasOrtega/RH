import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexDegreeDirectSum
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProd
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory NumberField
open Limits MonoidalCategory CartesianMonoidalCategory GlobalTheory.VB
open scoped ComplexOrder

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FComplexDegreeDirectSum.lean&line=27#L27)
-/
theorem _root_.GlobalTheory.T.complex_degree_direct_sum : ∀ (k : Type) [CommRing k] (S : Scheme.{0}) (p : S ⟶ Sp k) [IsIntegral S], IsArithVar p 1 → ∀ (E F : S.Modules) (r s : ℕ), VB.IsVB E r → VB.IsVB F s → cxDeg p (E ⊞ F) (r + s) = cxDeg p E r + cxDeg p F s := by
  first | exact @GlobalTheory.CxDegSum.cxDeg_biprod | exact GlobalTheory.CxDegSum.cxDeg_biprod | (intros; apply GlobalTheory.CxDegSum.cxDeg_biprod <;> assumption)
