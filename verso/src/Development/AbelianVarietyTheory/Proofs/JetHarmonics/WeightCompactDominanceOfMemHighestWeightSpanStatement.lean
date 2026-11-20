import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.WeightCompactDominanceOfMemHighestWeightSpan
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FJetHarmonics%2FWeightCompactDominanceOfMemHighestWeightSpan.lean&line=42#L42)
-/
theorem _root_.GlobalTheory.T.weight_compactDominance_of_mem_highestWeightSpan : ∀ (k : ℕ) (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] (E : Fin k → Fin k → Module.End ℂ W) (Λ μ : Fin k → ℝ) (x v : W), Formalism.REAL.GlRel E → Formalism.REAL.IsUnitary (PI.UpqRep.allPos k) E → Formalism.REAL.KHighest (PI.UpqRep.allPos k) E Λ x → v ∈ Formalism.REAL.kSpan (PI.UpqRep.allPos k) E x → v ≠ 0 → Formalism.REAL.IsWeight E μ v → PI.UpqRep.CDom (PI.UpqRep.allPos k) μ Λ := by
  first | exact @GlobalTheory.weight_cdom_of_mem_kSpan | exact GlobalTheory.weight_cdom_of_mem_kSpan | (intros; apply GlobalTheory.weight_cdom_of_mem_kSpan <;> assumption)
