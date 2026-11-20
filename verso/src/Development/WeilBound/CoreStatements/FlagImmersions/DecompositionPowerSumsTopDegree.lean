import Mathlib
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.CompactGapsGE
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PCoinvAboveTopGeneral
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PCoinvAboveTop
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PCoinvIdealComponent
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PCoinvIdealRepresentation
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PCoinvMonomialReduction
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PCoinvPolynomialReduction
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PCoinvStaircaseComponent
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PCoinvStaircaseDegree
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PCoinvStepReduction
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PHomogeneousComponentMul

open MvPolynomial Filter Topology GlobalTheory.CompanionTheory.Ar.Top

open GroundTheory.Heights₂.Heights.RestTerms in

/- English proof (translation)
The claim follows from `CoinvAboveTopGeneral.proof (CoinvAboveTop.proof (CoinvPolynomialReduction.proof (CoinvMonomialReduction.proof CoinvStepReduction.proof)) (CoinvIdealComponent.proof CoinvIdealRepresentation.proof HomogeneousComponentMul.proof) (CoinvStaircaseComponent.proof CoinvStaircaseDegree.pr …`.
-/
theorem RootFieldNumerics.coinv_above_top : CoinvAboveTopGeneral.Statement :=
  CoinvAboveTopGeneral.proof (CoinvAboveTop.proof
    (CoinvPolynomialReduction.proof (CoinvMonomialReduction.proof CoinvStepReduction.proof))
    (CoinvIdealComponent.proof CoinvIdealRepresentation.proof HomogeneousComponentMul.proof)
    (CoinvStaircaseComponent.proof CoinvStaircaseDegree.proof))

/- English proof (translation)
Introduce `Ψ _ _ N F _ hF`. Establish `hlt : Fintype.card Ψ * (Fintype.card (Fin N) * (Fintype.card (Fin N) - 1) / 2) < dimFl Ψ N + 1`. Simplify using `[dimFl]`. Take `⟨Q, hQ, hFQ⟩` from `RootFieldNumerics.coinv_above_top ℝ Ψ (Fin N) (dimFl Ψ N + 1) F hF hlt`. Use `⟨fun τ k => Q k τ, fun τ k _ _ => hQ k τ, ?_⟩` and prove the remaining obligations.

Rewrite using `[hFQ, Fintype.card_fin, Finset.sum_comm]`. Both sides reduce to the same expression.
-/
theorem RootFieldNumerics.decomposition_power_sums_top_degree : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (F : RP Ψ N), 2 ≤ N → F.IsHomogeneous (dimFl Ψ N + 1) → ∃ Q : Ψ → ℕ → RP Ψ N, (∀ τ k, 1 ≤ k → k ≤ N → (Q τ k).IsHomogeneous (dimFl Ψ N + 1 - k)) ∧ F = ∑ τ, ∑ k ∈ Finset.Icc 1 N, pk τ k * Q τ k := by
  intro Ψ _ _ N F _ hF
  have hlt : Fintype.card Ψ * (Fintype.card (Fin N) * (Fintype.card (Fin N) - 1) / 2) < dimFl Ψ N + 1 := by
    simp [dimFl]
  obtain ⟨Q, hQ, hFQ⟩ := RootFieldNumerics.coinv_above_top ℝ Ψ (Fin N) (dimFl Ψ N + 1) F hF hlt
  refine ⟨fun τ k => Q k τ, fun τ k _ _ => hQ k τ, ?_⟩
  rw [hFQ, Fintype.card_fin, Finset.sum_comm]
  rfl
