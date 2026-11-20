import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonzeroBoundedSectionShiftedWeight
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsArchOne
import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.SmallUnipotentElements
open NumberField Module ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsNonzeroBoundedSectionShiftedWeight.lean&line=195#L195)
-/
theorem _root_.GlobalTheory.T.exists_nonzero_boundedSection_shiftedWeight : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : DataX E r) (Xa : ArchInM X.toData) (Fl : FlatM X.toData Xa), GlobalTheory.Shares.Margins X.toData Xa → 0 < X.p0 → X.p0 < r → GapsGe X.p0 Xa.L 1 → PairGe Xa.L (1.9 * Xa.T) → GapsGe X.p0 (Xa.Fp - kLog X.Ψ r - (nd X.toData + 2) • Xa.L) 0 → PairGe (Xa.Fp - kLog X.Ψ r - (nd X.toData + 2) • Xa.L) 1 → ∀ s : ℕ, Even s → s ≤ Xa.T → ∀ u : Frame X.Ψ r → ℂ, u ∈ X.SS (deMul X.Ψ r X.p0 s) → (∃ x ∈ X.dom, u x ≠ 0) → ∃ w : Frame X.Ψ r → ℂ, X.IsBddSec ((nd X.toData + 4) • Xa.L - 2 • deMul X.Ψ r X.p0 s) w ∧ ∃ x ∈ X.dom, w x ≠ 0 := by
  first | exact @GlobalTheory.ShareSection.exists_bddSec_shift | exact GlobalTheory.ShareSection.exists_bddSec_shift | (intros; apply GlobalTheory.ShareSection.exists_bddSec_shift <;> assumption)
