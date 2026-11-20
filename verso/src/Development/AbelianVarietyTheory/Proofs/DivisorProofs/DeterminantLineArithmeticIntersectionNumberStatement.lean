import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeterminantLineArithmeticIntersectionNumber
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsX
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open scoped ENNReal Classical
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.FlatDetModel.num_eq_htDetT_mul_int` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FDeterminantLineArithmeticIntersectionNumber.lean&line=41#L41)
-/
theorem _root_.GlobalTheory.T.determinant_line_arithmetic_intersection_number : GlobalTheory.CovTop.HypothesesXH → Hypotheses2 → HypothesesH → GlobalTheory.Published.ScholzeWeinsteinB → OnObj fun D O _ T _ _ => ∀ B : ℝ, 2 ≤ B → ∀ (τ : D.what₂.Tau) c (g : (T.M c).Fun),
    (T.M c).Smooth g →
    (∀ σ x, x ∉ (T.M c).Z σ → g σ x = (T.F c).ph (fun σ' _ => if σ' = τ then (-1 : ℝ) else 0) σ x) →
    ∀ u : Wt O.Y, (T.K B c).num (Fin.cons (T.L B c (fun σ' _ => if σ' = τ then (-1 : ℝ) else 0) + (T.K B c).ar g)
        fun _ => T.L B c u) =
      (T.M c).int (fun _ => (T.K B c).c1 (T.L B c u)) (fun _ _ => O.Y.htDetT B c τ) := by
  first | exact @GlobalTheory.FlatDetModel.num_eq_htDetT_mul_int | exact GlobalTheory.FlatDetModel.num_eq_htDetT_mul_int | (intros; apply GlobalTheory.FlatDetModel.num_eq_htDetT_mul_int <;> assumption)
