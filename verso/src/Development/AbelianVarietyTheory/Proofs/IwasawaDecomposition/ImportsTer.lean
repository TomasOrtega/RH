import Mathlib

namespace GlobalTheory.IntSmulMemLattice

open NumberField

/- English proof (translation)
Establish `hden : ∀ a : E, ∃ d : ℤ, d ≠ 0 ∧ IsIntegral ℤ (d • a)` using `fun a => ((IsFractionRing.isAlgebraic_iff ℤ ℚ E).mpr (Algebra.IsAlgebraic.isAlgebraic a)).exists_integral_multiple`. Establish `hv : v ∈ Submodule.span E (L : Set V)` using `by rw [hL]; exact Submodule.mem_top`. Proceed by induction on `hv using Submodule.span_induction with`. Consider the case `mem x hx => exact ⟨1, one_ne_zero, by rw [one_smul]; exact hx⟩`. Consider the case `zero => exact ⟨1, one_ne_zero, by rw [smul_zero]; exact L.zero_mem⟩`.

Consider the case `add x y _ _ hx hy`. Take `⟨m, hm, hmx⟩` from `hx`. Take `⟨k, hk, hky⟩` from `hy`. Use `⟨m * k, mul_ne_zero hm hk, ?_⟩` and prove the remaining obligations. Establish `e1 : (m * k) • x = k • (m • x)` using `by rw [mul_comm, mul_smul]`.

Establish `e2 : (m * k) • y = m • (k • y)` using `by rw [mul_smul]`. Rewrite using `[smul_add, e1, e2]`. Conclude with `L.add_mem (zsmul_mem hmx k) (zsmul_mem hky m)`. Consider the case `smul a x _ hx`. Take `⟨m, hm, hmx⟩` from `hx`.

Take `⟨d, hd, hint⟩` from `hden a`. Use `⟨d * m, mul_ne_zero hd hm, ?_⟩` and prove the remaining obligations. Set `b : RingOfIntegers E` to `⟨d • a, hint⟩`. Establish `hb : algebraMap (RingOfIntegers E) E b = (d : E) * a`. Express the relevant statement in the definitionally equal form `d • a = (d : E) * a`.

Rewrite using `[zsmul_eq_mul]`. Establish `e : (d * m) • (a • x) = b • (m • x)`. Rewrite using `[← algebraMap_smul E b (m • x), hb, ← Int.cast_smul_eq_zsmul E (d * m), ← Int.cast_smul_eq_zsmul E m, smul_smul, smul_smul]`. Use `congr 1`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `L.smul_mem b hmx`.
-/
theorem exists_int_smul_mem {E V : Type} [Field E] [NumberField E] [AddCommGroup V] [Module E V]
    [Module (RingOfIntegers E) V] [IsScalarTower (RingOfIntegers E) E V]
    (L : Submodule (RingOfIntegers E) V) (hL : Submodule.span E (L : Set V) = ⊤) (v : V) :
    ∃ n : ℤ, n ≠ 0 ∧ n • v ∈ L := by
  have hden : ∀ a : E, ∃ d : ℤ, d ≠ 0 ∧ IsIntegral ℤ (d • a) := fun a =>
    ((IsFractionRing.isAlgebraic_iff ℤ ℚ E).mpr
      (Algebra.IsAlgebraic.isAlgebraic a)).exists_integral_multiple
  have hv : v ∈ Submodule.span E (L : Set V) := by rw [hL]; exact Submodule.mem_top
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by rw [one_smul]; exact hx⟩
  | zero => exact ⟨1, one_ne_zero, by rw [smul_zero]; exact L.zero_mem⟩
  | add x y _ _ hx hy =>
    obtain ⟨m, hm, hmx⟩ := hx
    obtain ⟨k, hk, hky⟩ := hy
    refine ⟨m * k, mul_ne_zero hm hk, ?_⟩
    have e1 : (m * k) • x = k • (m • x) := by rw [mul_comm, mul_smul]
    have e2 : (m * k) • y = m • (k • y) := by rw [mul_smul]
    rw [smul_add, e1, e2]
    exact L.add_mem (zsmul_mem hmx k) (zsmul_mem hky m)
  | smul a x _ hx =>
    obtain ⟨m, hm, hmx⟩ := hx
    obtain ⟨d, hd, hint⟩ := hden a
    refine ⟨d * m, mul_ne_zero hd hm, ?_⟩

    let b : RingOfIntegers E := ⟨d • a, hint⟩
    have hb : algebraMap (RingOfIntegers E) E b = (d : E) * a := by
      change d • a = (d : E) * a
      rw [zsmul_eq_mul]
    have e : (d * m) • (a • x) = b • (m • x) := by
      rw [← algebraMap_smul E b (m • x), hb, ← Int.cast_smul_eq_zsmul E (d * m),
        ← Int.cast_smul_eq_zsmul E m, smul_smul, smul_smul]
      congr 1
      push_cast
      ring
    rw [e]
    exact L.smul_mem b hmx

end GlobalTheory.IntSmulMemLattice
