import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ReductionMaxCompactInterConjRadicalContainsConj
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.StandardMaximalParabolic
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SumRepSubgroupEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOfValILeOne

open MeasureTheory ValuativeRel GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.StandardMaximalParabolic
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FReductionMaxCompactInterConjRadicalContainsConj.lean&line=40#L40)
-/
theorem _root_.GlobalTheory.T.reduction_maxCompact_inter_conjRadical_contains_conj : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {r a b : ℕ}
    (h : a + b = r) (g₀ : GL (Fin r) k), ∃ c : GL (Fin r) 𝓀[k], ∀ v ∈ stdMaxRad 𝓀[k] h,
    ∃ (u : GL (Fin r) k) (hu : u ∈ KO k (Fin r)), u ∈ conjBy g₀ (stdMaxRad k h) ∧
      GlobalTheory.LocGL.redK k (Fin r) ⟨u, hu⟩ = c * v * c⁻¹ := by
  first | exact @GlobalTheory.RadRedLift.red_lift | exact GlobalTheory.RadRedLift.red_lift | (intros; apply GlobalTheory.RadRedLift.red_lift <;> assumption)
