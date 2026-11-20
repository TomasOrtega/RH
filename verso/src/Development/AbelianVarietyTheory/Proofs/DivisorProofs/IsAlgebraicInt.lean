import Mathlib

namespace GlobalTheory.AlgebraicIntegerMultiple

open NumberField

/- English proof (translation)
Establish `h : IsIntegral ℚ c` using `Algebra.IsIntegral.isIntegral c`. Conclude with `(IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 h.isAlgebraic`.
-/
theorem isAlgebraic_int {E : Type} [Field E] [NumberField E] (c : E) : IsAlgebraic ℤ c := by
  have h : IsIntegral ℚ c := Algebra.IsIntegral.isIntegral c
  exact (IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 h.isAlgebraic

/- English proof (translation)
Establish `hw : w ∈ Submodule.span E (L : Set (Fin d → E))`. Rewrite using `[hL.span_eq_top]`. Discharge the goal by the elementary cases of `trivial`. Proceed by induction on `hw using Submodule.span_induction with`. Consider the case `mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩`.

Consider the case `zero => exact ⟨1, one_ne_zero, by simp⟩`. Consider the case `add x y _ _ hx hy`. Take `⟨a, ha, hax⟩` from `hx`. Take `⟨b, hb, hby⟩` from `hy`. Use `⟨a * b, mul_ne_zero ha hb, ?_⟩` and prove the remaining obligations.

Establish `h1 : (a * b) • x = b • (a • x)` using `by rw [mul_comm, mul_smul]`. Establish `h2 : (a * b) • y = a • (b • y)` using `mul_smul a b y`. Rewrite using `[smul_add, h1, h2]`. Conclude with `L.add_mem (zsmul_mem hax b) (zsmul_mem hby a)`. Consider the case `smul c x _ hx`.

Take `⟨N, hN, hNx⟩` from `hx`. Take `⟨y, hy, hint⟩` from `(isAlgebraic_int c).exists_integral_multiple`. Set `a : RingOfIntegers E` to `⟨y • c, hint⟩`. Use `⟨y * N, mul_ne_zero hy hN, ?_⟩` and prove the remaining obligations. Establish `key : (y * N) • (c • x) = a • (N • x)`.

Rewrite using `[← algebraMap_smul E a (N • x)]`. Use extensionality with `i`. Simplify using `[a, Pi.smul_apply, zsmul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[key]`.

Conclude with `L.smul_mem a hNx`.
-/
theorem exists_int_smul_mem {E : Type} [Field E] [NumberField E] {d : ℕ}
    {L : Submodule (RingOfIntegers E) (Fin d → E)}
    (hL : Submodule.IsLattice E L) (w : Fin d → E) :
    ∃ N : ℤ, N ≠ 0 ∧ N • w ∈ L := by
  have hw : w ∈ Submodule.span E (L : Set (Fin d → E)) := by
    rw [hL.span_eq_top]; trivial
  induction hw using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨b, hb, hby⟩ := hy
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    have h1 : (a * b) • x = b • (a • x) := by rw [mul_comm, mul_smul]
    have h2 : (a * b) • y = a • (b • y) := mul_smul a b y
    rw [smul_add, h1, h2]
    exact L.add_mem (zsmul_mem hax b) (zsmul_mem hby a)
  | smul c x _ hx =>
    obtain ⟨N, hN, hNx⟩ := hx
    obtain ⟨y, hy, hint⟩ := (isAlgebraic_int c).exists_integral_multiple
    let a : RingOfIntegers E := ⟨y • c, hint⟩
    refine ⟨y * N, mul_ne_zero hy hN, ?_⟩
    have key : (y * N) • (c • x) = a • (N • x) := by
      rw [← algebraMap_smul E a (N • x)]
      ext i
      simp [a, Pi.smul_apply, zsmul_eq_mul]
      ring
    rw [key]
    exact L.smul_mem a hNx

end GlobalTheory.AlgebraicIntegerMultiple
