import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFundamentalDomainSaturatedFundamentalSetFrames
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarChart
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.MeasurableSetSatFrames
open NumberField MeasureTheory ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHaarVolume GlobalTheory.FlagQuotHaar
open scoped ENNReal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.FundFrames.isFundamentalDomain_satFrames` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FIsFundamentalDomainSaturatedFundamentalSetFrames.lean&line=13#L13)
-/
theorem _root_.GlobalTheory.T.isFundamentalDomain_saturated_fundamentalSet_frames : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) {c : ℝ≥0∞}, HaarChart X c → ∀ {x0 : Frame X.Ψ r}, IsOrth X x0 → ∀ {FF : Set (V (nd X))}, IsFundSet X x0 FF → ∀ (Λ : Subgroup (RealGrp X)), (∀ s, s ∈ Λ ↔ ∃ γ ∈ X.Γ, lact γ (baseFr X) = frameOf X s) → IsFundamentalDomain Λ (frameOf X ⁻¹' GlobalTheory.Unfold.satFrames X x0 FF) (haarR X) := by
  first | exact @GlobalTheory.FundFrames.isFundamentalDomain_satFrames | exact GlobalTheory.FundFrames.isFundamentalDomain_satFrames | (intros; apply GlobalTheory.FundFrames.isFundamentalDomain_satFrames <;> assumption)
