import Mathlib

namespace GlobalTheory.IntSmulMemLatticeTwistedOperators

open NumberField

/- English proof (translation)
Take `⟨y, hy, hint⟩` from `IsAlgebraic.exists_integral_multiple (R := ℤ) ((IsFractionRing.isAlgebraic_iff ℤ ℚ E).mpr (Algebra.IsAlgebraic.isAlgebraic a))`. Use `⟨y, hy, ?_⟩` and prove the remaining obligations. Simplify `hint` using `[zsmul_eq_mul]`.
-/
theorem exists_int_mul_integral {E : Type} [Field E] [NumberField E] (a : E) :
    ∃ d : ℤ, d ≠ 0 ∧ IsIntegral ℤ ((d : E) * a) := by
  obtain ⟨y, hy, hint⟩ := IsAlgebraic.exists_integral_multiple (R := ℤ) ((IsFractionRing.isAlgebraic_iff ℤ ℚ E).mpr (Algebra.IsAlgebraic.isAlgebraic a))
  refine ⟨y, hy, ?_⟩
  simpa [zsmul_eq_mul] using hint

/- English proof (translation)
Establish `hv : v ∈ Submodule.span E (L : Set (Fin n → E))` using `by rw [hL.span_eq_top]; trivial`. Proceed by induction on `hv using Submodule.span_induction with`. Consider the case `mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩`. Consider the case `zero => exact ⟨1, one_ne_zero, by simp⟩`. Consider the case `add x y _ _ hx hy`.

Take `⟨c, hc, hcx⟩` from `hx`. Take `⟨d, hd, hdy⟩` from `hy`. Use `⟨c * d, mul_ne_zero hc hd, ?_⟩` and prove the remaining obligations. Rewrite using `[smul_add]`. Use `L.add_mem ?_ ?_` and prove the remaining obligations.

Rewrite using `[mul_comm, mul_smul]`. Conclude with `zsmul_mem hcx d`. Rewrite using `[mul_smul]`. Conclude with `zsmul_mem hdy c`. Consider the case `smul a x _ hx`.

Take `⟨c, hc, hcx⟩` from `hx`. Take `⟨d, hd, hint⟩` from `exists_int_mul_integral a`. Set `b : RingOfIntegers E` to `⟨(d : E) * a, hint⟩`. Use `⟨d * c, mul_ne_zero hd hc, ?_⟩` and prove the remaining obligations. Establish `key : (d * c) • (a • x) = b • (c • x)`.

Use extensionality with `i`. Simplify using `only [Pi.smul_apply, smul_eq_mul, zsmul_eq_mul, Int.cast_mul]`. Rewrite using `[Algebra.smul_def]`. Establish `hb : algebraMap (RingOfIntegers E) E b = (d : E) * a` using `rfl`. Rewrite using `[hb]`.

Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[key]`. Conclude with `L.smul_mem b hcx`.
-/
theorem exists_int_smul_mem {E : Type} [Field E] [NumberField E] {n : ℕ}
    (L : Submodule (RingOfIntegers E) (Fin n → E)) (hL : Submodule.IsLattice E L)
    (v : Fin n → E) : ∃ c : ℤ, c ≠ 0 ∧ c • v ∈ L := by
  have hv : v ∈ Submodule.span E (L : Set (Fin n → E)) := by rw [hL.span_eq_top]; trivial
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨c, hc, hcx⟩ := hx
    obtain ⟨d, hd, hdy⟩ := hy
    refine ⟨c * d, mul_ne_zero hc hd, ?_⟩
    rw [smul_add]
    refine L.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact zsmul_mem hcx d
    · rw [mul_smul]; exact zsmul_mem hdy c
  | smul a x _ hx =>
    obtain ⟨c, hc, hcx⟩ := hx
    obtain ⟨d, hd, hint⟩ := exists_int_mul_integral a
    let b : RingOfIntegers E := ⟨(d : E) * a, hint⟩
    refine ⟨d * c, mul_ne_zero hd hc, ?_⟩
    have key : (d * c) • (a • x) = b • (c • x) := by
      ext i
      simp only [Pi.smul_apply, smul_eq_mul, zsmul_eq_mul, Int.cast_mul]
      rw [Algebra.smul_def]
      have hb : algebraMap (RingOfIntegers E) E b = (d : E) * a := rfl
      rw [hb]
      simp
      ring
    rw [key]
    exact L.smul_mem b hcx

/- English proof (translation)
Introduce `L hL v` and use `exists_int_smul_mem L hL v`.
-/
theorem exists_nonzero_int_smul_mem_of_isLattice : ∀ {E : Type} [inst : Field E] [NumberField E] {n : ℕ} (L : Submodule (NumberField.RingOfIntegers E) (Fin n → E)), Submodule.IsLattice E L → ∀ (v : Fin n → E), ∃ (c : ℤ), c ≠ (0 : ℤ) ∧ c • v ∈ L :=
  fun L hL v => exists_int_smul_mem L hL v

end GlobalTheory.IntSmulMemLatticeTwistedOperators
