import Mathlib

namespace GlobalTheory.NatMulIntegralNsmul

/- English proof (translation)
Establish `halg : IsAlgebraic ℤ a` using `(IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 (Algebra.IsAlgebraic.isAlgebraic a)`. Take `⟨y, hy, hint⟩` from `halg.exists_integral_multiple`. Use `⟨y.natAbs, Int.natAbs_pos.2 hy, ?_⟩` and prove the remaining obligations. Rewrite `hint` using `[zsmul_eq_mul]`. Establish `hc : ((y.natAbs : ℕ) : E) = ((y.natAbs : ℤ) : E)` using `(Int.cast_natCast _).symm`.

Break down `Int.natAbs_eq y with h | h` into its components or cases. Rewrite using `[hc, ← h]`. Conclude with `hint`. Establish `h2 : (y.natAbs : ℤ) = -y` using `by omega`. Rewrite using `[hc, h2, Int.cast_neg, neg_mul]`.

Conclude with `hint.neg`.
-/
theorem exists_nat_mul_integral {E : Type} [Field E] [NumberField E] (a : E) :
    ∃ M : ℕ, 0 < M ∧ IsIntegral ℤ ((M : E) * a) := by
  have halg : IsAlgebraic ℤ a :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 (Algebra.IsAlgebraic.isAlgebraic a)
  obtain ⟨y, hy, hint⟩ := halg.exists_integral_multiple
  refine ⟨y.natAbs, Int.natAbs_pos.2 hy, ?_⟩
  rw [zsmul_eq_mul] at hint
  have hc : ((y.natAbs : ℕ) : E) = ((y.natAbs : ℤ) : E) := (Int.cast_natCast _).symm
  rcases Int.natAbs_eq y with h | h
  · rw [hc, ← h]; exact hint
  · have h2 : (y.natAbs : ℤ) = -y := by omega
    rw [hc, h2, Int.cast_neg, neg_mul]
    exact hint.neg

/- English proof (translation)
Establish `hv : v ∈ Submodule.span E (Λ : Set (Fin n → E))`. Rewrite using `[h.span_eq_top]`. Conclude with `Submodule.mem_top`. Proceed by induction on `hv using Submodule.span_induction with`. Consider the case `mem x hx => exact ⟨1, Nat.one_pos, by simpa using hx⟩`.

Consider the case `zero => exact ⟨1, Nat.one_pos, by simp⟩`. Consider the case `add x y _ _ hx hy`. Take `⟨N, hN, hx⟩` from `hx`. Take `⟨M, hM, hy⟩` from `hy`. Use `⟨M * N, Nat.mul_pos hM hN, ?_⟩` and prove the remaining obligations.

Rewrite using `[smul_add]`. Use `Λ.add_mem ?_ ?_` and prove the remaining obligations. Rewrite using `[mul_smul]`. Conclude with `nsmul_mem hx M`. Rewrite using `[mul_comm, mul_smul]`.

Conclude with `nsmul_mem hy N`. Consider the case `smul a x _ hx`. Take `⟨N, hN, hx⟩` from `hx`. Take `⟨M, hM, hint⟩` from `exists_nat_mul_integral a`. Use `⟨M * N, Nat.mul_pos hM hN, ?_⟩` and prove the remaining obligations.

Take `⟨r, hr⟩ : ∃ r : NumberField.RingOfIntegers E, algebraMap (NumberField.RingOfIntegers E) E r = (M : E) * a` from `⟨⟨(M : E) * a, hint⟩, rfl⟩`. Establish `hmem` using `Λ.smul_mem r hx`. Establish `e : (M * N) • a • x = r • N • x`. Rewrite using `[← algebraMap_smul E r (N • x), hr]`. Use function extensionality and compare the values at `i`.

Simplify using `only [Pi.smul_apply, smul_eq_mul, nsmul_eq_mul, Nat.cast_mul, Pi.mul_apply, Pi.natCast_apply]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `hmem`.
-/
theorem exists_nsmul_mem {E : Type} [inst : Field E] [NumberField E] {n : ℕ}
    (Λ : Submodule (NumberField.RingOfIntegers E) (Fin n → E)) (h : Submodule.IsLattice E Λ)
    (v : Fin n → E) : ∃ (N : ℕ), (0 : ℕ) < N ∧ N • v ∈ Λ := by
  have hv : v ∈ Submodule.span E (Λ : Set (Fin n → E)) := by
    rw [h.span_eq_top]; exact Submodule.mem_top
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨1, Nat.one_pos, by simpa using hx⟩
  | zero => exact ⟨1, Nat.one_pos, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨N, hN, hx⟩ := hx
    obtain ⟨M, hM, hy⟩ := hy
    refine ⟨M * N, Nat.mul_pos hM hN, ?_⟩
    rw [smul_add]
    refine Λ.add_mem ?_ ?_
    · rw [mul_smul]; exact nsmul_mem hx M
    · rw [mul_comm, mul_smul]; exact nsmul_mem hy N
  | smul a x _ hx =>
    obtain ⟨N, hN, hx⟩ := hx
    obtain ⟨M, hM, hint⟩ := exists_nat_mul_integral a
    refine ⟨M * N, Nat.mul_pos hM hN, ?_⟩
    obtain ⟨r, hr⟩ : ∃ r : NumberField.RingOfIntegers E,
        algebraMap (NumberField.RingOfIntegers E) E r = (M : E) * a := ⟨⟨(M : E) * a, hint⟩, rfl⟩
    have hmem := Λ.smul_mem r hx
    have e : (M * N) • a • x = r • N • x := by
      rw [← algebraMap_smul E r (N • x), hr]
      funext i
      simp only [Pi.smul_apply, smul_eq_mul, nsmul_eq_mul, Nat.cast_mul, Pi.mul_apply,
        Pi.natCast_apply]
      ring
    rw [e]; exact hmem

end GlobalTheory.NatMulIntegralNsmul
