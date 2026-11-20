import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalFiniteTypeSubringLeValuationSubringA
import Mathlib
open Polynomial
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.exists_normal_finiteType_subring_le_valuationSubring` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsNormalFiniteTypeSubringLeValuationSubringA.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.exists_normal_finiteType_subring_le_valuationSubring' : ∀ {κ : Type} [Field κ] [Algebra ℂ κ] (V : ValuationSubring κ) (T : Finset κ), (∀ a : ℂ, algebraMap ℂ κ a ∈ V) → (∀ x ∈ T, x ∈ V) → (∀ f : κ, ∃ a ∈ Algebra.adjoin ℂ (T : Set κ), ∃ b ∈ Algebra.adjoin ℂ (T : Set κ), b ≠ 0 ∧ f * b = a) → ∃ (R : Subring κ) (hcR : ∀ a : ℂ, algebraMap ℂ κ a ∈ R), ((algebraMap ℂ κ).codRestrict R hcR).FiniteType ∧ (∀ x ∈ T, x ∈ R) ∧ R ≤ V.toSubring ∧ IsNoetherianRing R ∧ IsIntegrallyClosed R ∧ IsFractionRing R κ := by
  first | exact @GlobalTheory.exists_normal_finiteType_subring_le_valuationSubring | exact GlobalTheory.exists_normal_finiteType_subring_le_valuationSubring | (intros; apply GlobalTheory.exists_normal_finiteType_subring_le_valuationSubring <;> assumption)
