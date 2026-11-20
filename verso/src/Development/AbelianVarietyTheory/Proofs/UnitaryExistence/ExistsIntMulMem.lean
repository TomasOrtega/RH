import Mathlib

namespace GlobalTheory.IntMulMem

open NumberField

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately. Treat this case separately. Treat this case separately.

Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Reduce the equality to equality of the corresponding arguments. Simplify using the standard rewrite rules. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Treat this case separately. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Extract witnesses or component facts from the available result. Introduce a local definition for the expression. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Reduce the equality to equality of the corresponding arguments. Rewrite the conclusion using the stated equalities. Move the embeddings inside the algebraic operations. Expand and normalize the polynomial expressions, which then agree. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem exists_int_mul_mem {E : Type} [Field E] [NumberField E] {V : Type} [AddCommGroup V]
    [Module E V] [Module (RingOfIntegers E) V] [IsScalarTower (RingOfIntegers E) E V]
    (Λ : Submodule (RingOfIntegers E) V) :
    ∀ v ∈ Submodule.span E (↑Λ : Set V), ∃ (N : ℤ), N ≠ (0 : ℤ) ∧ (↑N : E) • v ∈ Λ := by
  intro v hv
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
  | zero => exact ⟨1, one_ne_zero, by simpa using Λ.zero_mem⟩
  | add x y _ _ hx hy =>
    obtain ⟨N, hN, hNx⟩ := hx
    obtain ⟨M, hM, hMy⟩ := hy
    refine ⟨N * M, mul_ne_zero hN hM, ?_⟩
    have h1 : ((N * M : ℤ) : E) • x = ((M : ℤ) : RingOfIntegers E) • ((N : E) • x) := by
      rw [← algebraMap_smul E ((M : ℤ) : RingOfIntegers E), smul_smul]
      congr 1
      simp [mul_comm]
    have h2 : ((N * M : ℤ) : E) • y = ((N : ℤ) : RingOfIntegers E) • ((M : E) • y) := by
      rw [← algebraMap_smul E ((N : ℤ) : RingOfIntegers E), smul_smul]
      congr 1
      simp
    rw [smul_add, h1, h2]
    exact Λ.add_mem (Λ.smul_mem _ hNx) (Λ.smul_mem _ hMy)
  | smul c x _ hx =>
    obtain ⟨N, hN, hNx⟩ := hx
    have halg : IsAlgebraic ℤ c := (IsFractionRing.isAlgebraic_iff ℤ ℚ E).mpr (.of_finite ℚ c)
    obtain ⟨y, hy0, hyi⟩ := halg.exists_integral_multiple
    let a : RingOfIntegers E := ⟨y • c, hyi⟩
    refine ⟨y * N, mul_ne_zero hy0 hN, ?_⟩
    have h : ((y * N : ℤ) : E) • (c • x) = a • ((N : E) • x) := by
      rw [← algebraMap_smul E a, smul_smul, smul_smul]
      congr 1
      show _ = (y • c) * (N : E)
      rw [zsmul_eq_mul]; push_cast; ring
    rw [h]
    exact Λ.smul_mem _ hNx

end GlobalTheory.IntMulMem
