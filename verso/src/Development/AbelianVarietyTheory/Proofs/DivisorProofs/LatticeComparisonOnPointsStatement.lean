import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeComparisonOnPoints
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.LatHt.latCmp` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FLatticeComparisonOnPoints.lean&line=120#L120)
-/
theorem _root_.GlobalTheory.T.lattice_comparison_on_points : Hypotheses2 → HypothesesH → OnObj fun _ _ _ _ H h => LatCmp H h.pts := by
  first | exact @GlobalTheory.LatHt.latCmp | exact GlobalTheory.LatHt.latCmp | (intros; apply GlobalTheory.LatHt.latCmp <;> assumption)
