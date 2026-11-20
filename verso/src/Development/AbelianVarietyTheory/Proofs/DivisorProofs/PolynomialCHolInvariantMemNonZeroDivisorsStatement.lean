import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialCHolInvariantMemNonZeroDivisors
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsArchOne
import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.SmallUnipotentElements
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LactMemDomOfIsom
open NumberField Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn GlobalTheory.CuspEmb
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CuspEmb.C_mem_nonZeroDivisors` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FPolynomialCHolInvariantMemNonZeroDivisors.lean&line=22#L22)
-/
theorem _root_.GlobalTheory.T.polynomialC_holInvariant_mem_nonZeroDivisors : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (U C : Type) [Group U] [MulAction U C] (M : TwoLevels E r U C) (D : HA M), (∀ c, ∃ x : M.dom, (D : C → M.dom → ℂ) c x ≠ 0) → Polynomial.C D ∈ nonZeroDivisors (Polynomial (HA M)) := by
  first | exact @GlobalTheory.CuspEmb.C_mem_nonZeroDivisors | exact GlobalTheory.CuspEmb.C_mem_nonZeroDivisors | (intros; apply GlobalTheory.CuspEmb.C_mem_nonZeroDivisors <;> assumption)
