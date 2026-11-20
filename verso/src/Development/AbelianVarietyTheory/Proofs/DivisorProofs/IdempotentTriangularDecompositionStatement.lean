import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentTriangularDecomposition
import Mathlib
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.exists_integral_block_bases_of_projectors` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FIdempotentTriangularDecomposition.lean&line=85#L85)
-/
theorem _root_.GlobalTheory.T.idempotent_triangular_decomposition : ∀ (F : Type) [Field F] (R : Subring F), IsPrincipalIdealRing R → (∀ x : F, ∃ d ∈ R, d ≠ 0 ∧ d * x ∈ R) →
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (N : ℕ) (e : ι → Matrix (Fin N) (Fin N) F),
    (∀ σ τ, e σ * e τ = if σ = τ then e τ else 0) → ∑ τ, e τ = 1 →
    ∃ (b : Fin N → ι) (U L : Matrix (Fin N) (Fin N) F), (∀ i j, U i j ∈ R ∧ L i j ∈ R) ∧
      (∀ s, (e (b s)).mulVec (fun i => U i s) = fun i => U i s) ∧
      ∀ r s, b r = b s → (L * U) r s = if r = s then 1 else 0 := by
  first | exact @GlobalTheory.exists_integral_block_bases_of_projectors | exact GlobalTheory.exists_integral_block_bases_of_projectors | (intros; apply GlobalTheory.exists_integral_block_bases_of_projectors <;> assumption)
