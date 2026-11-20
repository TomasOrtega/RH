import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaValues.SWEqSOf
import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.AdmissibleModuleIffLatticeQuotients
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.TheoremZeroOfReducedInputs
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.SupBoundPageRows
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LatOfLamSt

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.L2.Pj GlobalTheory.RunIn

namespace GlobalTheory

/- English proof (translation)
Introduce `D large₂ j ka w hL hd hn h`. Take `⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩` from `h`. Use `⟨h1, h2, h3, h4, h5, h6, h7, ?_, ?_⟩` and prove the remaining obligations. Use `le_trans (Real.log_le_log (by positivity) ?_) h8` and prove the remaining obligations. Establish `: ((WeightAlgebra.DF w : ℕ) : ℝ) ≤ ((WeightAlgebra.DF ka : ℕ) : ℝ)` using `by exact_mod_cast hd`.

Combine the linear equalities and inequalities to obtain the conclusion. Break down `Nat.eq_zero_or_pos w.n with h0 | h0` into its components or cases. Rewrite using `[h0]`. Simplify using `using hL`. Conclude with `le_trans (Real.log_le_log (by exact_mod_cast h0) (by exact_mod_cast hn)) h9`.
-/
theorem pageRows_of_le : ∀ (D : D7) (large₂ : SizeData₂ D) (j : ℕ) (ka w : WeightFamilies.Wt D j), 0 ≤ large₂.sc.L → WeightAlgebra.DF w ≤ WeightAlgebra.DF ka → w.n ≤ ka.n → ReciprocityTheory.ChartRestriction.G.PullbackSections.SupBoundPageRows D large₂ ka → ReciprocityTheory.ChartRestriction.G.PullbackSections.SupBoundPageRows D large₂ w := by
  intro D large₂ j ka w hL hd hn h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  refine ⟨h1, h2, h3, h4, h5, h6, h7, ?_, ?_⟩
  · refine le_trans (Real.log_le_log (by positivity) ?_) h8
    have : ((WeightAlgebra.DF w : ℕ) : ℝ) ≤ ((WeightAlgebra.DF ka : ℕ) : ℝ) := by exact_mod_cast hd
    linarith
  · rcases Nat.eq_zero_or_pos w.n with h0 | h0
    · rw [h0]; simpa using hL
    · exact le_trans (Real.log_le_log (by exact_mod_cast h0) (by exact_mod_cast hn)) h9

end GlobalTheory
