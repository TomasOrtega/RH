import Mathlib

namespace GlobalTheory.NatMultipleInLattice

/- English proof (translation)
Take `⟨y, hy0, hy⟩` from `exists_integral_multiples ℤ ℚ (L := E) {a}`. Establish `h1` using `hy a (Finset.mem_singleton_self a)`. Use `⟨y.natAbs, Int.natAbs_ne_zero.2 hy0, ?_⟩` and prove the remaining obligations. Break down `Int.natAbs_eq y with h | h` into its components or cases. Establish `e : ((y.natAbs : ℕ) : E) * a = y • a`.

Rewrite using `[zsmul_eq_mul]`. Use `congr 1`. Use `conv_rhs => rw [h]`. Simplify using the standard rewrite rules. Rewrite using `[e]`.

Conclude with `h1`. Establish `e : ((y.natAbs : ℕ) : E) * a = -(y • a)`. Rewrite using `[zsmul_eq_mul, ← neg_mul]`. Use `congr 1`. Use `conv_rhs => rw [h]`.

Simplify using the standard rewrite rules. Rewrite using `[e]`. Conclude with `h1.neg`.
-/
theorem exists_nat_mul_integral {E : Type} [Field E] [NumberField E] (a : E) :
    ∃ m : ℕ, m ≠ 0 ∧ IsIntegral ℤ ((m : E) * a) := by
  obtain ⟨y, hy0, hy⟩ := exists_integral_multiples ℤ ℚ (L := E) {a}
  have h1 := hy a (Finset.mem_singleton_self a)
  refine ⟨y.natAbs, Int.natAbs_ne_zero.2 hy0, ?_⟩
  rcases Int.natAbs_eq y with h | h
  · have e : ((y.natAbs : ℕ) : E) * a = y • a := by
      rw [zsmul_eq_mul]
      congr 1
      conv_rhs => rw [h]
      simp
    rw [e]
    exact h1
  · have e : ((y.natAbs : ℕ) : E) * a = -(y • a) := by
      rw [zsmul_eq_mul, ← neg_mul]
      congr 1
      conv_rhs => rw [h]
      simp
    rw [e]
    exact h1.neg

/- English proof (translation)
Establish `hx : x ∈ Submodule.span E (L : Set (Fin n → E))`. Rewrite using `[hL.span_eq_top]`. Conclude with `Submodule.mem_top`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem y hy => exact ⟨1, one_ne_zero, by rw [one_smul]; exact hy⟩`.

Consider the case `zero => exact ⟨1, one_ne_zero, by rw [one_smul]; exact L.zero_mem⟩`. Consider the case `add y z _ _ hy hz`. Take `⟨D, hD, hy⟩` from `hy`. Take `⟨F, hF, hz⟩` from `hz`. Use `⟨D * F, mul_ne_zero hD hF, ?_⟩` and prove the remaining obligations.

Rewrite using `[smul_add]`. Use `L.add_mem ?_ ?_` and prove the remaining obligations. Rewrite using `[mul_comm, mul_smul]`. Conclude with `L.toAddSubmonoid.nsmul_mem hy F`. Rewrite using `[mul_smul]`.

Conclude with `L.toAddSubmonoid.nsmul_mem hz D`. Consider the case `smul a y _ hy`. Take `⟨D, hD, hy⟩` from `hy`. Take `⟨m, hm, hi⟩` from `exists_nat_mul_integral a`. Use `⟨m * D, mul_ne_zero hm hD, ?_⟩` and prove the remaining obligations.

Establish `key` using `L.smul_mem (⟨(m : E) * a, hi⟩ : NumberField.RingOfIntegers E) hy`. Establish `: (m * D) • a • y = (⟨(m : E) * a, hi⟩ : NumberField.RingOfIntegers E) • D • y`. Establish `h3 : (⟨(m : E) * a, hi⟩ : NumberField.RingOfIntegers E) • D • y = ((m : E) * a) • D • y` using `rfl`. Rewrite using `[h3]`. Use extensionality with `i`.

Simplify using `only [Pi.smul_apply]`. Simplify using `only [nsmul_eq_mul, smul_eq_mul, Nat.cast_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`. Conclude with `key`.
-/
theorem exists_nsmul_mem_lattice {E : Type} [Field E] [NumberField E] {n : ℕ}
    (L : Submodule (NumberField.RingOfIntegers E) (Fin n → E)) (hL : Submodule.IsLattice E L)
    (x : Fin n → E) : ∃ D : ℕ, D ≠ 0 ∧ D • x ∈ L := by
  have hx : x ∈ Submodule.span E (L : Set (Fin n → E)) := by
    rw [hL.span_eq_top]; exact Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_ne_zero, by rw [one_smul]; exact hy⟩
  | zero => exact ⟨1, one_ne_zero, by rw [one_smul]; exact L.zero_mem⟩
  | add y z _ _ hy hz =>
    obtain ⟨D, hD, hy⟩ := hy
    obtain ⟨F, hF, hz⟩ := hz
    refine ⟨D * F, mul_ne_zero hD hF, ?_⟩
    rw [smul_add]
    refine L.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact L.toAddSubmonoid.nsmul_mem hy F
    · rw [mul_smul]; exact L.toAddSubmonoid.nsmul_mem hz D
  | smul a y _ hy =>
    obtain ⟨D, hD, hy⟩ := hy
    obtain ⟨m, hm, hi⟩ := exists_nat_mul_integral a
    refine ⟨m * D, mul_ne_zero hm hD, ?_⟩
    have key := L.smul_mem (⟨(m : E) * a, hi⟩ : NumberField.RingOfIntegers E) hy
    have : (m * D) • a • y =
        (⟨(m : E) * a, hi⟩ : NumberField.RingOfIntegers E) • D • y := by
      have h3 : (⟨(m : E) * a, hi⟩ : NumberField.RingOfIntegers E) • D • y
          = ((m : E) * a) • D • y := rfl
      rw [h3]
      ext i
      simp only [Pi.smul_apply]
      simp only [nsmul_eq_mul, smul_eq_mul, Nat.cast_mul]
      ring
    rw [this]; exact key

end GlobalTheory.NatMultipleInLattice
