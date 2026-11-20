import Mathlib

namespace GlobalTheory.NatMulMem

open NumberField

/- English proof (translation)
Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the indicated hypotheses using the stated equalities. Separate the alternatives or extract the components of the hypothesis. Establish an intermediate fact.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
lemma exists_nat_mul_mem {E : Type} [Field E] [NumberField E] (c : E) :
    ∃ m : ℕ, 0 < m ∧ IsIntegral ℤ ((m : E) * c) := by
  obtain ⟨y, hy, hint⟩ :=
    IsAlgebraic.exists_integral_multiple (R := ℤ) (z := c)
      ((IsFractionRing.isAlgebraic_iff ℤ ℚ E).mpr (Algebra.IsAlgebraic.isAlgebraic c))
  refine ⟨y.natAbs, Int.natAbs_pos.mpr hy, ?_⟩
  rw [zsmul_eq_mul] at hint
  rcases Int.natAbs_eq y with h | h
  · have : ((y.natAbs : ℕ) : E) = ((y : ℤ) : E) := by
      conv_rhs => rw [h]
      simp
    rw [this]; exact hint
  · have : ((y.natAbs : ℕ) : E) = -((y : ℤ) : E) := by
      conv_rhs => rw [h]
      simp
    rw [this, neg_mul]; exact hint.neg

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Introduce a local definition for the expression. Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Assume the hypotheses and unpack their components. Extract witnesses or component facts from the available result.

Reduce the conclusion to the remaining proof obligations. Introduce a local definition for the expression. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem main {E : Type} [Field E] {n : ℕ} [NumberField E]
    (L : Submodule (RingOfIntegers E) (Fin n → E)) :
    Submodule.span E (L : Set (Fin n → E)) = ⊤ →
      ∀ x : Fin n → E, ∃ d : ℕ, 0 < d ∧ d • x ∈ L := by
  intro hspan
  let S : Submodule E (Fin n → E) :=
    { carrier := {x | ∃ d : ℕ, 0 < d ∧ d • x ∈ L}
      add_mem' := by
        rintro x y ⟨a, ha, hx⟩ ⟨b, hb, hy⟩
        refine ⟨a * b, Nat.mul_pos ha hb, ?_⟩
        rw [smul_add]
        refine L.add_mem ?_ ?_
        · rw [mul_comm, mul_smul]; exact L.toAddSubmonoid.nsmul_mem hx b
        · rw [mul_smul]; exact L.toAddSubmonoid.nsmul_mem hy a
      zero_mem' := ⟨1, one_pos, by simp⟩
      smul_mem' := by
        rintro c x ⟨a, ha, hx⟩
        obtain ⟨m, hm, hint⟩ := exists_nat_mul_mem c
        refine ⟨m * a, Nat.mul_pos hm ha, ?_⟩
        let r : RingOfIntegers E := ⟨(m : E) * c, hint⟩
        have key : (m * a) • (c • x) = r • (a • x) := by
          funext i
          have hr : algebraMap (RingOfIntegers E) E r = (m : E) * c := rfl
          rw [Pi.smul_apply, Pi.smul_apply, Pi.smul_apply, Pi.smul_apply, Algebra.smul_def r, hr]
          simp only [nsmul_eq_mul, smul_eq_mul, Nat.cast_mul]
          ring
        rw [key]; exact L.smul_mem r hx }
  have hle : Submodule.span E (L : Set (Fin n → E)) ≤ S :=
    Submodule.span_le.mpr (fun y hy => ⟨1, one_pos, by simpa using hy⟩)
  intro x
  have hx : x ∈ S := hle (hspan ▸ Submodule.mem_top)
  exact hx

end GlobalTheory.NatMulMem
