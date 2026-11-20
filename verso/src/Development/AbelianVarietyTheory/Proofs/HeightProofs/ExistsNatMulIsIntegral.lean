import Mathlib

namespace GlobalTheory.ExistsNatMulIsIntegral₂

open NumberField

/- English proof (translation)
Establish `halg : IsAlgebraic ℤ c` using `(IsFractionRing.isAlgebraic_iff ℤ ℚ E).mpr (Algebra.IsAlgebraic.isAlgebraic c)`. Take `⟨y, hy, hint⟩` from `halg.exists_integral_multiple`. Use `⟨y.natAbs, Int.natAbs_pos.mpr hy, ?_⟩` and prove the remaining obligations. Take `⟨n, rfl | rfl⟩` from `Int.eq_nat_or_neg y`. Simplify using `using hint`.

Simplify using `using hint.neg`.
-/
theorem exists_nat_mul_isIntegral {E : Type} [Field E] [NumberField E] (c : E) :
    ∃ d : ℕ, 0 < d ∧ IsIntegral ℤ ((d : E) * c) := by
  have halg : IsAlgebraic ℤ c := (IsFractionRing.isAlgebraic_iff ℤ ℚ E).mpr (Algebra.IsAlgebraic.isAlgebraic c)
  obtain ⟨y, hy, hint⟩ := halg.exists_integral_multiple
  refine ⟨y.natAbs, Int.natAbs_pos.mpr hy, ?_⟩
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg y
  · simpa using hint
  · simpa using hint.neg

/- English proof (translation)
Introduce `E W _ _ _ _ _ _ L x hx`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem x h => exact ⟨1, one_pos, by simpa using h⟩`. Consider the case `zero => exact ⟨1, one_pos, by simp⟩`. Consider the case `add x y _ _ hx hy`.

Take `⟨a, ha, hxa⟩` from `hx`. Take `⟨b, hb, hyb⟩` from `hy`. Use `⟨a * b, Nat.mul_pos ha hb, ?_⟩` and prove the remaining obligations. Rewrite using `[smul_add]`. Use `L.add_mem ?_ ?_` and prove the remaining obligations.

Rewrite using `[mul_comm, mul_smul]`. Conclude with `nsmul_mem hxa b`. Rewrite using `[mul_smul]`. Conclude with `nsmul_mem hyb a`. Consider the case `smul c x _ hx`.

Take `⟨k, hk, hkx⟩` from `hx`. Take `⟨d, hd, hdc⟩` from `exists_nat_mul_isIntegral c`. Use `⟨d * k, Nat.mul_pos hd hk, ?_⟩` and prove the remaining obligations. Set `a : 𝓞 E` to `⟨(d : E) * c, hdc⟩`. Establish `ha : (algebraMap (𝓞 E) E a) = (d : E) * c` using `rfl`.

Establish `key : (d * k) • (c • x) = a • (k • x)`. Rewrite using `[← algebraMap_smul E a (k • x), ha, mul_smul, mul_smul, Nat.cast_smul_eq_nsmul, smul_comm c k x]`. Rewrite using `[key]`. Conclude with `L.smul_mem a hkx`.
-/
theorem main : ∀ {E W : Type} [inst : Field E] [NumberField E] [inst_2 : AddCommGroup W] [inst_3 : Module E W]
    [inst_4 : Module (NumberField.RingOfIntegers E) W] [IsScalarTower (NumberField.RingOfIntegers E) E W]
    (L : Submodule (NumberField.RingOfIntegers E) W),
    ∀ x ∈ Submodule.span E (↑L : Set W), ∃ (k : ℕ), (0 : ℕ) < k ∧ k • x ∈ L := by
  intro E W _ _ _ _ _ _ L x hx
  induction hx using Submodule.span_induction with
  | mem x h => exact ⟨1, one_pos, by simpa using h⟩
  | zero => exact ⟨1, one_pos, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, hxa⟩ := hx
    obtain ⟨b, hb, hyb⟩ := hy
    refine ⟨a * b, Nat.mul_pos ha hb, ?_⟩
    rw [smul_add]
    refine L.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact nsmul_mem hxa b
    · rw [mul_smul]; exact nsmul_mem hyb a
  | smul c x _ hx =>
    obtain ⟨k, hk, hkx⟩ := hx
    obtain ⟨d, hd, hdc⟩ := exists_nat_mul_isIntegral c
    refine ⟨d * k, Nat.mul_pos hd hk, ?_⟩
    let a : 𝓞 E := ⟨(d : E) * c, hdc⟩
    have ha : (algebraMap (𝓞 E) E a) = (d : E) * c := rfl
    have key : (d * k) • (c • x) = a • (k • x) := by
      rw [← algebraMap_smul E a (k • x), ha, mul_smul, mul_smul, Nat.cast_smul_eq_nsmul, smul_comm c k x]
    rw [key]
    exact L.smul_mem a hkx

end GlobalTheory.ExistsNatMulIsIntegral₂
