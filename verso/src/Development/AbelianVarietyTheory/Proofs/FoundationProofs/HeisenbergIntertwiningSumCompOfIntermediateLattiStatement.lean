import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeisenbergIntertwiningSumCompOfIntermediateLatti
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsHeisTrivial
open Classical GlobalTheory.FinWeil
open scoped BigOperators
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FHeisenbergIntertwiningSumCompOfIntermediateLatti.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.heisenbergIntertwiningSum_comp_of_intermediate_lattice : ∀ {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M] {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M}, IsHeis σ w γ W → ∀ (A B C : Submodule R X), SelfDual γ A → SelfDual γ B → SelfDual γ C → idx A B ≠ 0 → idx B C ≠ 0 → B ≤ (B ⊓ A) ⊔ (B ⊓ C) → idx A C = idx A B * idx B C ∧ ∀ v, Fixes W A v → sumOp W B C (sumOp W A B v) = sumOp W A C v := by
  first | exact @GlobalTheory.FinWeil.sumOp_comp_of_between | exact GlobalTheory.FinWeil.sumOp_comp_of_between | (intros; apply GlobalTheory.FinWeil.sumOp_comp_of_between <;> assumption)
