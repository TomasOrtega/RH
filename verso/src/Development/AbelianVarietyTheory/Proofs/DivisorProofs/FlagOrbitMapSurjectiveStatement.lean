import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagOrbitMapSurjective
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NormSqColGrLineOfOrthogonal
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.FlagZ GlobalTheory.FlagPoly Formalism.DegreeFormula
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.FlagZ.surjective_orbit` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FFlagOrbitMapSurjective.lean&line=56#L56)
-/
theorem _root_.GlobalTheory.T.flag_orbit_map_surjective : ∀ (ι κ : Type) [Fintype ι] [Finite κ] (N : ℕ) (a : κ → ι) (l : κ → Fin (N + 1)), Function.Surjective (orbit a l) := by
  first | exact @GlobalTheory.FlagZ.surjective_orbit | exact GlobalTheory.FlagZ.surjective_orbit | (intros; apply GlobalTheory.FlagZ.surjective_orbit <;> assumption)
