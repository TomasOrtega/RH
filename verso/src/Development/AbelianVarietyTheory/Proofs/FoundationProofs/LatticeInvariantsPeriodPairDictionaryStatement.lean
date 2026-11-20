import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LatticeInvariantsPeriodPairDictionary
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FLatticeInvariantsPeriodPairDictionary.lean&line=191#L191)
-/
theorem _root_.GlobalTheory.T.latticeInvariants_periodPair_dictionary : ∀ (L : PeriodPair) (Λ : AddSubgroup ℂ), (∀ z, z ∈ Λ ↔ z ∈ L.lattice) → g2 Λ = L.g₂ ∧ g3 Λ = L.g₃ ∧ TaylorLogMetric.discr Λ ≠ 0 ∧ area Λ = |(L.ω₁ * starRingEnd ℂ L.ω₂).im| ∧ (∀ z, z ∉ Λ → wpF Λ z = L.weierstrassP z ∧ wpD Λ z = L.derivWeierstrassP z) ∧ (∀ (Λ' : AddSubgroup ℂ), g2 Λ' = g2 Λ → g3 Λ' = g3 Λ → Λ' = Λ) ∧ ∀ a b : ℂ, a ^ 3 - 27 * b ^ 2 ≠ 0 → ∃ (L' : PeriodPair), L'.g₂ = a ∧ L'.g₃ = b := by
  first | exact @GlobalTheory.LatticeInvariants.invariants_dictionary | exact GlobalTheory.LatticeInvariants.invariants_dictionary | (intros; apply GlobalTheory.LatticeInvariants.invariants_dictionary <;> assumption)
