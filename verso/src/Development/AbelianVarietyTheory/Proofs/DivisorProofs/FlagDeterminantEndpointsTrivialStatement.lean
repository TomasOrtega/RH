import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagDeterminantEndpointsTrivial
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NormSqColGrLineOfOrthogonal
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.FlagZ GlobalTheory.ArInt Formalism.DegreeFormula GlobalTheory.Cartier
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.FlagZ.flDet_zero_last_isometric_triv` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FFlagDeterminantEndpointsTrivial.lean&line=14#L14)
-/
theorem _root_.GlobalTheory.T.flag_determinant_endpoints_trivial : ∀ (ι : Type) [Fintype ι] (N : ℕ) (τ : ι), (flDet τ 0 : GlobalTheory.HermLB (flStr ι N)).Isometric (GlobalTheory.HermLB.triv _) ∧ (flDet τ (Fin.last N) : GlobalTheory.HermLB (flStr ι N)).Isometric (GlobalTheory.HermLB.triv _) := by
  first | exact @GlobalTheory.FlagZ.flDet_zero_last_isometric_triv | exact GlobalTheory.FlagZ.flDet_zero_last_isometric_triv | (intros; apply GlobalTheory.FlagZ.flDet_zero_last_isometric_triv <;> assumption)
