import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteMaximalIdealsContainingNatCast
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmHostUnitAddConjEqOne

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LowDat GlobalTheory.LowFilt

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.LowDat.finite_maximal_ideals_containing_natCast` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FFiniteMaximalIdealsContainingNatCast.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.finite_maximal_ideals_containing_natCast' : ∀ {E : Type} [Field E] [NumberField E] (n : ℕ) (hn : 0 < n),
    {𝔮 : Ideal (𝓞 E) | 𝔮.IsMaximal ∧ (n : 𝓞 E) ∈ 𝔮}.Finite := by
  first | exact @GlobalTheory.LowDat.finite_maximal_ideals_containing_natCast | exact GlobalTheory.LowDat.finite_maximal_ideals_containing_natCast | (intros; apply GlobalTheory.LowDat.finite_maximal_ideals_containing_natCast <;> assumption)
