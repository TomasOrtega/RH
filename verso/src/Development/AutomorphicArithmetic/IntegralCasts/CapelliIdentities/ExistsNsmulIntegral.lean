import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Signature

/- English proof (translation)
Establish an intermediate fact. Extract witnesses or component facts from the available result. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities.
-/
private theorem UpperTheory.Reformulated.B.Uc15.exists_nsmul_integral {E : Type} [Field E] [NumberField E]
    (a : E) : ∃ M : ℕ, M ≠ 0 ∧ ∃ b : NumberField.RingOfIntegers E, (b : E) = (M : E) * a := by
  have halg : IsAlgebraic ℤ a :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ E).mpr (Algebra.IsAlgebraic.isAlgebraic a)
  obtain ⟨y, hy, hint⟩ := halg.exists_integral_multiple
  have h2 : IsIntegral ℤ (y • (y • a)) := hint.smul y
  refine ⟨(y * y).natAbs, Int.natAbs_ne_zero.mpr (mul_ne_zero hy hy), ⟨y • (y • a), h2⟩, ?_⟩
  have h3 : (((y * y).natAbs : ℕ) : E) = ((y * y : ℤ) : E) := by
    rw [← Int.cast_natCast, Int.natAbs_of_nonneg (mul_self_nonneg y)]
  rw [h3]
  change y • (y • a) = _
  rw [smul_smul, zsmul_eq_mul]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Proceed by induction. Treat this case separately.

Treat this case separately. Treat this case separately. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Treat this case separately.

Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument.

Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Move the embeddings inside the algebraic operations. Expand and normalize the polynomial expressions, which then agree. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem UpperTheory.Reformulated.B.Uc15.exists_nsmul_mem :
    ∀ {E : Type} [inst : Field E] [inst_1 : NumberField E] [inst_2 : NumberField.IsCMField E] {r : ℕ}
      (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r) (u : Fin r → E), ∃ (N : ℕ), N ≠ (0 : ℕ) ∧ N • u ∈ X.Λ := by
  intro E _ _ _ r X u
  have hu : u ∈ Submodule.span E (X.Λ : Set (Fin r → E)) := by
    rw [X.Λ_span]; exact Submodule.mem_top
  induction hu using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by rw [one_nsmul]; exact hx⟩
  | zero => exact ⟨1, one_ne_zero, by rw [one_nsmul]; exact X.Λ.zero_mem⟩
  | add x y _ _ hx hy =>
    obtain ⟨M, hM, hx⟩ := hx
    obtain ⟨N, hN, hy⟩ := hy
    refine ⟨M * N, mul_ne_zero hM hN, ?_⟩
    rw [nsmul_add]
    refine X.Λ.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact nsmul_mem hx N
    · rw [mul_smul]; exact nsmul_mem hy M
  | smul a x _ hx =>
    obtain ⟨N, hN, hx⟩ := hx
    obtain ⟨M, hM, b, hb⟩ := UpperTheory.Reformulated.B.Uc15.exists_nsmul_integral a
    refine ⟨M * N, mul_ne_zero hM hN, ?_⟩
    have h : (M * N) • a • x = b • (N • x) := by
      funext i
      change (M * N) • (a * x i) = (b : E) * (N • x i)
      rw [hb, nsmul_eq_mul, nsmul_eq_mul]
      push_cast
      ring
    rw [h]
    exact X.Λ.smul_mem b hx
