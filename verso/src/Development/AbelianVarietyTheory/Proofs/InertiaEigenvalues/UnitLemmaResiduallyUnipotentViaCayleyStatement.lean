import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitLemmaResiduallyUnipotentViaCayley
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
open GlobalTheory.UnitLemma Polynomial
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.UnitLemma.CayleyCase.identity_of_residually_unipotent` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FUnitLemmaResiduallyUnipotentViaCayley.lean&line=253#L253)
-/
theorem _root_.GlobalTheory.T.unitLemma_residually_unipotent_via_cayley : UnitLemmaLie → ∀ (K : UQ), K.Odd → ∀ B₁ B₂ : InvAlg K, B₁.g * B₁.σ B₁.g = 1 → B₂.g * B₂.σ B₂.g = 1 → (B₁.P * B₂.P).Separable → ∀ s : K.Oˣ, algebraMap K.O K.E s * K.c (algebraMap K.O K.E s) = 1 → (∃ Q : K.O[X], Q.map (algebraMap K.O K.E) = B₁.P * B₂.P ∧ Q.map (IsLocalRing.residue K.O) = (X - C (IsLocalRing.residue K.O s)) ^ Q.natDegree) → InvAlg.Identity B₁ B₂ := by
  first | exact @GlobalTheory.UnitLemma.CayleyCase.identity_of_residually_unipotent | exact GlobalTheory.UnitLemma.CayleyCase.identity_of_residually_unipotent | (intros; apply GlobalTheory.UnitLemma.CayleyCase.identity_of_residually_unipotent <;> assumption)
