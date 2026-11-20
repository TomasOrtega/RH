import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConjInvariantApproxIdentityRealLieSmoothin
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfMemSpanK
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsConjInvariantApproxIdentityRealLieSmoothin.lean&line=164#L164)
-/
theorem _root_.GlobalTheory.T.exists_conjInvariant_approxIdentity_realLieSmoothing : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (ν : Measure (Lie E a)) [ν.IsAddHaarMeasure], ∃ α : ℕ → Lie E a → ℂ, (∀ n, IsTest (invSet E a) (α n) ∧ KInv (α n)) ∧ ∀ ψ ∈ Sm E a, ∀ g, Tendsto (fun n => smoothing ν (α n) ψ g) atTop (𝓝 (ψ g)) := by
  first | exact @GlobalTheory.AutGrowth.ApproxId.exists_approx_identity | exact GlobalTheory.AutGrowth.ApproxId.exists_approx_identity | (intros; apply GlobalTheory.AutGrowth.ApproxId.exists_approx_identity <;> assumption)
