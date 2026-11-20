import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.NormSqColGrLineOfOrthogonal
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ArBirational
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagGdegEqDegFl
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical

namespace GlobalTheory.FlagDegChecked

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Apply an available result and prove the equalities needed to match it to the conclusion.
-/
theorem flag_gdeg_eq_degFl_checked : Hypotheses2 → GlobalTheory.Published.ArDegree → ∀ (ι : Type) [Fintype ι] (N : ℕ) (n : ι × Fin N → ℤ), gdeg (comb (GlobalTheory.FlagZ.grLine (ι := ι) (N := N)) n) (dimFl ι N) = degFl ι N (lin (fun x => (n x : ℝ)) ^ dimFl ι N) := by
  intro h1 h2 ι _ N n
  convert GlobalTheory.FlagDegTie.flag_gdeg_eq_degFl h1 h2 ι N n

end GlobalTheory.FlagDegChecked
