import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedIntegralConstantFlagDegree
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FMixedIntegralConstantFlagDegree.lean&line=38#L38)
-/
theorem _root_.GlobalTheory.T.mixed_integral_constant_flag_degree : Hypotheses2 → HypothesesH → OnObj fun D O A T _ _ => ∀ B : ℝ, 2 ≤ B → ∀ c (u : Wt O.Y) (f : (T.M c).Fun),
    (T.M c).Smooth f → ∀ a : ℝ,
      (T.M c).int (fun _ => (T.K B c).c1 (T.L B c u + (T.K B c).ar f)) (fun _ _ => a) =
        a * (A.w c * Formalism.DegreeFormula.flagDeg D.what₂.Tau O.Y.N u) := by
  first | exact @GlobalTheory.GenDeg.main | exact GlobalTheory.GenDeg.main | (intros; apply GlobalTheory.GenDeg.main <;> assumption)
