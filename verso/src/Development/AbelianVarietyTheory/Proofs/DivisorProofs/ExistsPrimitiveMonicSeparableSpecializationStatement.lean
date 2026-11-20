import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrimitiveMonicSeparableSpecialization
open Filter Topology
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.PrimTransc.exists_primitive_monic_separable_specialization` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsPrimitiveMonicSeparableSpecialization.lean&line=56#L56)
-/
theorem _root_.GlobalTheory.T.exists_primitive_monic_separable_specialization' : ∀ (K : Type) [Field K] [CharZero K] (D : ℕ) (x : Fin D → K), IsTranscendenceBasis ℚ x → ∀ (J : Type) [Finite J] (e : J → K), ∃ (P : Polynomial (MvPolynomial (Fin D) ℚ)) (ψ : AdjoinRoot P →ₐ[ℚ] K) (g : K) (c : Fin D → ℚ), P.Monic ∧ Function.Injective ψ ∧ (∀ i, ψ (AdjoinRoot.of P (MvPolynomial.X i)) = x i) ∧ g ≠ 0 ∧ (∀ j, g * e j ∈ ψ.range) ∧ (P.map (MvPolynomial.eval c)).Separable := by
  first | exact @GlobalTheory.PrimTransc.exists_primitive_monic_separable_specialization | exact GlobalTheory.PrimTransc.exists_primitive_monic_separable_specialization | (intros; apply GlobalTheory.PrimTransc.exists_primitive_monic_separable_specialization <;> assumption)
