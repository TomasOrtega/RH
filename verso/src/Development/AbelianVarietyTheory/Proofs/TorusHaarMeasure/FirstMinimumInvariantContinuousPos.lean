import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.PnormInvStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.MinimumGrowthBounds

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.FirstMinimum

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

/- English proof (translation)
Extract witnesses or component facts from the available result. Consider separately whether the proposition holds or fails. Supply the required witnesses or components. Establish an intermediate fact. Assume the negation of the conclusion and derive a contradiction.

Supply the required witnesses or components. A detailed English derivation is pending.
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
Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules.
-/
theorem emb_mulVec {r : ℕ} (τ : E →+* ℂ) (M : Matrix (Fin r) (Fin r) E) (v : Fin r → E) :
    Data.emb τ (M.mulVec v) = (M.map τ).mulVec (Data.emb τ v) := by
  funext a
  simp [Data.emb, Matrix.mulVec, dotProduct, map_sum, map_mul]

end GlobalTheory.FirstMinimum
