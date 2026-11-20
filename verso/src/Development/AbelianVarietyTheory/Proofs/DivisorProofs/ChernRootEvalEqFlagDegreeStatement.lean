import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernRootEvalEqFlagDegree
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ArBirational
import Development.AbelianVarietyTheory.Definitions.Divisors.NormSqColGrLineOfOrthogonal
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordProportionality
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AntisymmEqChernRootsMulRootDiscr
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FChernRootEvalEqFlagDegree.lean&line=135#L135)
-/
theorem _root_.GlobalTheory.T.chern_root_eval_eq_flag_degree : ∀ (ι : Type) [Fintype ι] (N : ℕ) (Q : MvPolynomial (GlobalTheory.GoodMetric.Root (fun _ : ι => N)) ℝ) (R : MvPolynomial (ι × ℕ) ℝ), GlobalTheory.GoodMetric.antisymm Q = GlobalTheory.GoodMetric.chernRoots (fun _ : ι => N) R * GlobalTheory.GoodMetric.rootDiscr (fun _ : ι => N) → MvPolynomial.eval (fun x : ι × ℕ => if x.2 = 0 then (1 : ℝ) else 0) R = degFl ι N (MvPolynomial.rename (fun x : GlobalTheory.GoodMetric.Root (fun _ : ι => N) => (x.1, x.2)) Q) := by
  first | exact @GlobalTheory.FlagAlternation.eval_chernRoots_eq_degFl | exact GlobalTheory.FlagAlternation.eval_chernRoots_eq_degFl | (intros; apply GlobalTheory.FlagAlternation.eval_chernRoots_eq_degFl <;> assumption)
