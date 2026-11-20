import Mathlib

namespace Bl.IntegerMulIntegral

/- English proof (translation)
Establish an intermediate fact. Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
private lemma int_mul_integral {E : Type} [Field E] [NumberField E] (a : E) :
    ∃ d : ℤ, d ≠ 0 ∧ IsIntegral ℤ ((d : E) * a) := by
  have hx : IsAlgebraic ℤ a := (IsFractionRing.isAlgebraic_iff ℤ ℚ E).mpr (.of_finite ℚ a)
  obtain ⟨y, hy, hi⟩ := hx.exists_integral_multiple
  exact ⟨y, hy, by simpa [zsmul_eq_mul] using hi⟩

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately. Treat this case separately. Treat this case separately.

Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. Treat this case separately. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations.

Extract witnesses or component facts from the available result. Establish an intermediate fact. Apply an available result and prove the equalities needed to match it to the conclusion. By extensionality, compare the relevant components. Express the relevant assertion in an equivalent form by its definition.

Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree. A detailed English derivation is pending.
-/
theorem goal1 :
  ∀ {E : Type} [inst : Field.{0} E] [NumberField.{0} E] {n : Nat}
  (L : Submodule.{0, 0} (NumberField.RingOfIntegers.{0} E) (Fin n → E)) (v : Fin n → E),
  Membership.mem.{0, 0} (Submodule.span.{0, 0} E (SetLike.coe.{0, 0} L)) v →
    Exists.{1} fun (m : Int) ↦ And (Ne.{1} m 0) (Membership.mem.{0, 0} L (HSMul.hSMul.{0, 0, 0} m v)) := by
  intro E _ _ n L v hv
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨m1, h1, hm1⟩ := hx
    obtain ⟨m2, h2, hm2⟩ := hy
    refine ⟨m1 * m2, mul_ne_zero h1 h2, ?_⟩
    have e : (m1 * m2) • (x + y) = m2 • (m1 • x) + m1 • (m2 • y) := by
      rw [smul_add, smul_smul, smul_smul, mul_comm m2 m1]
    rw [e]
    exact L.add_mem (L.toAddSubgroup.zsmul_mem hm1 m2) (L.toAddSubgroup.zsmul_mem hm2 m1)
  | smul a x _ hx =>
    obtain ⟨m, hm, hmx⟩ := hx
    obtain ⟨d, hd, hi⟩ := int_mul_integral a
    refine ⟨d * m, mul_ne_zero hd hm, ?_⟩
    obtain ⟨r, hr⟩ : ∃ r : NumberField.RingOfIntegers E,
        algebraMap (NumberField.RingOfIntegers E) E r = (d : E) * a := ⟨⟨_, hi⟩, rfl⟩
    have hmem := L.smul_mem r hmx
    convert hmem using 1
    ext i
    change (d * m) • (a * x i) = r • ((m • x) i)
    rw [← algebraMap_smul E r, hr, Pi.smul_apply, smul_eq_mul, zsmul_eq_mul, zsmul_eq_mul, Int.cast_mul]
    ring

end Bl.IntegerMulIntegral
