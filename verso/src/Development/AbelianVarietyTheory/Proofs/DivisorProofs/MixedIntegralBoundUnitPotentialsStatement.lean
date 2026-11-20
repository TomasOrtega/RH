import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedIntegralBoundUnitPotentials
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialPullbackStatement
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.ChernLevineNirenberg.cln_bound` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FMixedIntegralBoundUnitPotentials.lean&line=194#L194)
-/
theorem _root_.GlobalTheory.T.mixed_integral_bound_unit_potentials : ∀ (e : ℕ) (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas e X) (Om : LocPot X) (w : X → ℝ) (v : Fin e → X → ℝ), IsPotential A Om → IsPsh A Om → A.Smooth w → (∀ x, w x ≤ 0) → IsPsh A (Om + LocPot.ofFun w) → (∀ i, A.Smooth (v i) ∧ (∀ x, -1 ≤ v i x ∧ v i x ≤ 0) ∧ IsPsh A (Om + LocPot.ofFun (v i))) → mInt A (fun i => Om + LocPot.ofFun (v i)) (fun x => -w x) ≤ mInt A (fun _ => Om) (fun x => -w x) + e * mInt A (fun _ => Om) (fun _ => 1) := by
  first | exact @GlobalTheory.ChernLevineNirenberg.cln_bound | exact GlobalTheory.ChernLevineNirenberg.cln_bound | (intros; apply GlobalTheory.ChernLevineNirenberg.cln_bound <;> assumption)
