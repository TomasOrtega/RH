import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagDeterminantNefOnFibres
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NormSqColGrLineOfOrthogonal
open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.FlagZ GlobalTheory.ArInt Formalism.DegreeFormula GlobalTheory.Cartier
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.FlagZ.nefFib_flDet` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FFlagDeterminantNefOnFibres.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.flag_determinant_nef_on_fibres : ∀ (ι : Type) [Fintype ι] (N : ℕ) (τ : ι) (l : Fin (N + 1)), GlobalTheory.ArInt.NefFib (flDet τ l : GlobalTheory.HermLB (flStr ι N)) := by
  first | exact @GlobalTheory.FlagZ.nefFib_flDet | exact GlobalTheory.FlagZ.nefFib_flDet | (intros; apply GlobalTheory.FlagZ.nefFib_flDet <;> assumption)
