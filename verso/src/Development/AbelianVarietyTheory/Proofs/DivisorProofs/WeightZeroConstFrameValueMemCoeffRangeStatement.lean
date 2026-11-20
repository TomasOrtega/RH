import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightZeroConstFrameValueMemCoeffRange
import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsAlgebraicOfNormConst
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.CountableFractionRingMvPolynomial
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.MemRangeOfIsAlgebraicRatFun
open NumberField Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.FlatLine.const_value_mem_range` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FWeightZeroConstFrameValueMemCoeffRange.lean&line=37#L37)
-/
theorem _root_.GlobalTheory.T.weightZero_const_frameValue_mem_coeff_range : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r), GoodEmb c σ → IsUnf U → 1 ≤ Dw.p + Dw.q → ∀ f ∈ sec Xo c 0 0, ∀ a : ℂ, (∀ k, ∀ x ∈ (U.X k).dom, rdU U f k x = a) → a ∈ σ.range := by
  first | exact @GlobalTheory.FlatLine.const_value_mem_range | exact GlobalTheory.FlatLine.const_value_mem_range | (intros; apply GlobalTheory.FlatLine.const_value_mem_range <;> assumption)
