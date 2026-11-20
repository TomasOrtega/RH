import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.PnormInvStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.MinimumGrowthBounds

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.FirstMinimum

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

/- English proof (translation)
Take `⟨τ⟩ : Nonempty (E →+* ℂ)` from `inferInstance`. Distinguish the cases in `h : τ ∈ X.Ψ`. Conclude with `⟨⟨τ, h⟩⟩`. Establish `h' : ComplexEmbedding.conjugate τ ∈ X.Ψ`. Assume the negation of the conclusion as `h2`.

Conclude with `h ((X.cmType τ).mpr h2)`. Conclude with `⟨⟨_, h'⟩⟩`.
-/
theorem cmType_nonempty {r : ℕ} (X : Data E r) : Nonempty X.Ψ := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  by_cases h : τ ∈ X.Ψ
  · exact ⟨⟨τ, h⟩⟩
  · have h' : ComplexEmbedding.conjugate τ ∈ X.Ψ := by
      by_contra h2
      exact h ((X.cmType τ).mpr h2)
    exact ⟨⟨_, h'⟩⟩

omit [NumberField E] [IsCMField E] in
/- English proof (translation)
Use function extensionality and compare the values at `a`. Simplify using `[Data.emb, Matrix.mulVec, dotProduct, map_sum, map_mul]`.
-/
theorem emb_mulVec {r : ℕ} (τ : E →+* ℂ) (M : Matrix (Fin r) (Fin r) E) (v : Fin r → E) :
    Data.emb τ (M.mulVec v) = (M.map τ).mulVec (Data.emb τ v) := by
  funext a
  simp [Data.emb, Matrix.mulVec, dotProduct, map_sum, map_mul]

end GlobalTheory.FirstMinimum
