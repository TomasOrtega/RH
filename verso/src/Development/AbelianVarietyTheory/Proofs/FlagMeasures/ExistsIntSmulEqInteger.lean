import Mathlib

namespace GlobalTheory.IntSmulIntegerEq

/- English proof (translation)
Establish `hQ : IsAlgebraic ℚ c` using `Algebra.IsAlgebraic.isAlgebraic c`. Establish `hZ : IsAlgebraic ℤ c` using `(IsFractionRing.isAlgebraic_iff ℤ ℚ E).mpr hQ`. Take `⟨M, hM, hint⟩` from `hZ.exists_integral_multiple`. Conclude with `⟨M, hM, ⟨M • c, hint⟩, rfl⟩`.
-/
theorem exists_int_smul_eq_integer {E : Type} [Field E] [NumberField E] (c : E) :
    ∃ M : ℤ, M ≠ 0 ∧ ∃ a : NumberField.RingOfIntegers E,
      algebraMap (NumberField.RingOfIntegers E) E a = M • c := by
  have hQ : IsAlgebraic ℚ c := Algebra.IsAlgebraic.isAlgebraic c
  have hZ : IsAlgebraic ℤ c := (IsFractionRing.isAlgebraic_iff ℤ ℚ E).mpr hQ
  obtain ⟨M, hM, hint⟩ := hZ.exists_integral_multiple
  exact ⟨M, hM, ⟨M • c, hint⟩, rfl⟩

/- English proof (translation)
Establish `hw : w ∈ Submodule.span E (L : Set (Fin n → E))`. Rewrite using `[hL.span_eq_top]`. Discharge the goal by the elementary cases of `trivial`. Proceed by induction on `hw using Submodule.span_induction with`. Consider the case `mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩`.

Consider the case `zero => exact ⟨1, one_ne_zero, by simp⟩`. Consider the case `add x y _ _ hx hy`. Take `⟨N₁, h₁, hx⟩` from `hx`. Take `⟨N₂, h₂, hy⟩` from `hy`. Use `⟨N₁ * N₂, mul_ne_zero h₁ h₂, ?_⟩` and prove the remaining obligations.

Establish `e : (N₁ * N₂) • (x + y) = N₂ • (N₁ • x) + N₁ • (N₂ • y)`. Rewrite using `[smul_add, smul_smul, smul_smul, mul_comm N₂ N₁]`. Rewrite using `[e]`. Conclude with `L.add_mem (zsmul_mem hx N₂) (zsmul_mem hy N₁)`. Consider the case `smul c x _ hx`.

Take `⟨N, hN, hx⟩` from `hx`. Take `⟨M, hM, a, ha⟩` from `exists_int_smul_eq_integer c`. Use `⟨M * N, mul_ne_zero hM hN, ?_⟩` and prove the remaining obligations. Establish `e : (M * N) • (c • x) = a • (N • x)`. Rewrite using `[← algebraMap_smul E a, ha, smul_assoc, mul_smul, smul_comm N c x]`.

Rewrite using `[e]`. Conclude with `L.smul_mem a hx`.
-/
theorem exists_int_smul_mem {E : Type} [inst : Field E] [NumberField E] {n : ℕ}
    (L : Submodule (NumberField.RingOfIntegers E) (Fin n → E)) (hL : Submodule.IsLattice E L)
    (w : Fin n → E) : ∃ (N : ℤ), N ≠ (0 : ℤ) ∧ N • w ∈ L := by
  have hw : w ∈ Submodule.span E (L : Set (Fin n → E)) := by
    rw [hL.span_eq_top]; trivial
  induction hw using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨N₁, h₁, hx⟩ := hx
    obtain ⟨N₂, h₂, hy⟩ := hy
    refine ⟨N₁ * N₂, mul_ne_zero h₁ h₂, ?_⟩
    have e : (N₁ * N₂) • (x + y) = N₂ • (N₁ • x) + N₁ • (N₂ • y) := by
      rw [smul_add, smul_smul, smul_smul, mul_comm N₂ N₁]
    rw [e]
    exact L.add_mem (zsmul_mem hx N₂) (zsmul_mem hy N₁)
  | smul c x _ hx =>
    obtain ⟨N, hN, hx⟩ := hx
    obtain ⟨M, hM, a, ha⟩ := exists_int_smul_eq_integer c
    refine ⟨M * N, mul_ne_zero hM hN, ?_⟩
    have e : (M * N) • (c • x) = a • (N • x) := by
      rw [← algebraMap_smul E a, ha, smul_assoc, mul_smul, smul_comm N c x]
    rw [e]
    exact L.smul_mem a hx

end GlobalTheory.IntSmulIntegerEq
