import Mathlib

namespace GlobalTheory.LatticeIntegerMultipleMembership

/- English proof (translation)
Establish `hy : y ∈ Submodule.span E (L : Set (Fin n → E))`. Rewrite using `[hL.span_eq_top]`. Conclude with `Submodule.mem_top`. Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem x hx => exact ⟨1, one_ne_zero, by rw [one_smul]; exact hx⟩`.

Consider the case `zero => exact ⟨1, one_ne_zero, by rw [one_smul]; exact L.zero_mem⟩`. Consider the case `add x z _ _ hx hz`. Take `⟨a, ha, hax⟩` from `hx`. Take `⟨b, hb, hbz⟩` from `hz`. Use `⟨a * b, mul_ne_zero ha hb, ?_⟩` and prove the remaining obligations.

Rewrite using `[smul_add]`. Use `L.add_mem ?_ ?_` and prove the remaining obligations. Rewrite using `[mul_comm, mul_smul]`. Conclude with `zsmul_mem hax b`. Rewrite using `[mul_smul]`.

Conclude with `zsmul_mem hbz a`. Consider the case `smul c x _ hx`. Take `⟨a, ha, hax⟩` from `hx`. Establish `hc : IsAlgebraic ℤ c` using `(IsFractionRing.isAlgebraic_iff ℤ ℚ E).mpr (Algebra.IsAlgebraic.isAlgebraic c)`. Take `⟨d, hd, hint⟩` from `hc.exists_integral_multiple`.

Use `⟨d * a, mul_ne_zero hd ha, ?_⟩` and prove the remaining obligations. Establish `h` using `L.smul_mem (⟨d • c, hint⟩ : NumberField.RingOfIntegers E) hax`. Establish `e : (d * a) • c • x = (⟨d • c, hint⟩ : NumberField.RingOfIntegers E) • a • x`. Express the relevant statement in the definitionally equal form `(d * a) • c • x = (d • c) • a • x`. Rewrite using `[mul_smul, smul_assoc, smul_comm a c x]`.

Rewrite using `[e]`. Conclude with `h`.
-/
theorem exists_int_smul_mem_of_isLattice {E : Type} [Field E] [NumberField E] {n : ℕ}
    (L : Submodule (NumberField.RingOfIntegers E) (Fin n → E)) (hL : Submodule.IsLattice E L)
    (y : Fin n → E) : ∃ (D : ℤ), D ≠ (0 : ℤ) ∧ D • y ∈ L := by
  have hy : y ∈ Submodule.span E (L : Set (Fin n → E)) := by
    rw [hL.span_eq_top]; exact Submodule.mem_top
  induction hy using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by rw [one_smul]; exact hx⟩
  | zero => exact ⟨1, one_ne_zero, by rw [one_smul]; exact L.zero_mem⟩
  | add x z _ _ hx hz =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨b, hb, hbz⟩ := hz
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    rw [smul_add]
    refine L.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact zsmul_mem hax b
    · rw [mul_smul]; exact zsmul_mem hbz a
  | smul c x _ hx =>
    obtain ⟨a, ha, hax⟩ := hx
    have hc : IsAlgebraic ℤ c :=
      (IsFractionRing.isAlgebraic_iff ℤ ℚ E).mpr (Algebra.IsAlgebraic.isAlgebraic c)
    obtain ⟨d, hd, hint⟩ := hc.exists_integral_multiple
    refine ⟨d * a, mul_ne_zero hd ha, ?_⟩
    have h := L.smul_mem (⟨d • c, hint⟩ : NumberField.RingOfIntegers E) hax
    have e : (d * a) • c • x
        = (⟨d • c, hint⟩ : NumberField.RingOfIntegers E) • a • x := by
      change (d * a) • c • x = (d • c) • a • x
      rw [mul_smul, smul_assoc, smul_comm a c x]
    rw [e]; exact h

end GlobalTheory.LatticeIntegerMultipleMembership
