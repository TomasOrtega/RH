import Mathlib

namespace GlobalTheory.IntSmulMemSubmodule

/- English proof (translation)
Establish `hw : w ∈ Submodule.span E (L : Set (Fin n → E))`. Rewrite using `[hL.span_eq_top]`. Discharge the goal by the elementary cases of `trivial`. Proceed by induction on `hw using Submodule.span_induction with`. Consider the case `mem x hx => exact ⟨1, one_ne_zero, by rw [one_smul]; exact hx⟩`.

Consider the case `zero => exact ⟨1, one_ne_zero, by rw [one_smul]; exact L.zero_mem⟩`. Consider the case `add x y _ _ hx hy`. Take `⟨a, ha, hax⟩` from `hx`. Take `⟨b, hb, hby⟩` from `hy`. Use `⟨a * b, mul_ne_zero ha hb, ?_⟩` and prove the remaining obligations.

Establish `h : (a * b) • (x + y) = b • (a • x) + a • (b • y)`. Rewrite using `[smul_add, smul_smul, smul_smul, mul_comm b a]`. Rewrite using `[h]`. Conclude with `L.add_mem (zsmul_mem hax b) (zsmul_mem hby a)`. Consider the case `smul c x _ hx`.

Take `⟨a, ha, hax⟩` from `hx`. Establish `hc : IsAlgebraic ℤ c` using `(IsFractionRing.isAlgebraic_iff ℤ ℚ E).mpr (Algebra.IsAlgebraic.isAlgebraic c)`. Take `⟨d, hd, hdc⟩` from `hc.exists_integral_multiple`. Use `⟨d * a, mul_ne_zero hd ha, ?_⟩` and prove the remaining obligations. Set `r : NumberField.RingOfIntegers E` to `⟨d • c, hdc⟩`.

Establish `h : (d * a) • (c • x) = r • (a • x)`. Establish `h1 : r • (a • x) = (d • c) • (a • x)` using `rfl`. Rewrite using `[h1, smul_assoc, mul_smul, smul_comm a c x]`. Rewrite using `[h]`. Conclude with `L.smul_mem r hax`.
-/
theorem exists_int_smul_mem {E : Type} [inst : Field E] [NumberField E] {n : ℕ}
    (L : Submodule (NumberField.RingOfIntegers E) (Fin n → E)) (hL : Submodule.IsLattice E L)
    (w : Fin n → E) : ∃ (N : ℤ), N ≠ (0 : ℤ) ∧ N • w ∈ L := by
  have hw : w ∈ Submodule.span E (L : Set (Fin n → E)) := by
    rw [hL.span_eq_top]; trivial
  induction hw using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by rw [one_smul]; exact hx⟩
  | zero => exact ⟨1, one_ne_zero, by rw [one_smul]; exact L.zero_mem⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨b, hb, hby⟩ := hy
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    have h : (a * b) • (x + y) = b • (a • x) + a • (b • y) := by
      rw [smul_add, smul_smul, smul_smul, mul_comm b a]
    rw [h]
    exact L.add_mem (zsmul_mem hax b) (zsmul_mem hby a)
  | smul c x _ hx =>
    obtain ⟨a, ha, hax⟩ := hx
    have hc : IsAlgebraic ℤ c :=
      (IsFractionRing.isAlgebraic_iff ℤ ℚ E).mpr (Algebra.IsAlgebraic.isAlgebraic c)
    obtain ⟨d, hd, hdc⟩ := hc.exists_integral_multiple
    refine ⟨d * a, mul_ne_zero hd ha, ?_⟩
    let r : NumberField.RingOfIntegers E := ⟨d • c, hdc⟩
    have h : (d * a) • (c • x) = r • (a • x) := by
      have h1 : r • (a • x) = (d • c) • (a • x) := rfl
      rw [h1, smul_assoc, mul_smul, smul_comm a c x]
    rw [h]
    exact L.smul_mem r hax

end GlobalTheory.IntSmulMemSubmodule
