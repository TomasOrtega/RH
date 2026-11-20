import Mathlib

namespace GlobalTheory.IntegerMultipleMembership

/- English proof (translation)
Establish `hz : z ∈ Submodule.span E (L : Set (Fin n → E))`. Rewrite using `[hL.span_eq_top]`. Discharge the goal by the elementary cases of `trivial`. Proceed by induction on `hz using Submodule.span_induction with`. Consider the case `mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩`.

Consider the case `zero => exact ⟨1, one_ne_zero, by simp⟩`. Consider the case `add x y _ _ hx hy`. Take `⟨a, ha, hax⟩` from `hx`. Take `⟨b, hb, hby⟩` from `hy`. Use `⟨a * b, mul_ne_zero ha hb, ?_⟩` and prove the remaining obligations.

Rewrite using `[smul_add]`. Use `L.add_mem ?_ ?_` and prove the remaining obligations. Rewrite using `[mul_comm, mul_smul]`. Conclude with `zsmul_mem hax b`. Rewrite using `[mul_smul]`.

Conclude with `zsmul_mem hby a`. Consider the case `smul c x _ hx`. Take `⟨a, ha, hax⟩` from `hx`. Establish `hc : IsAlgebraic ℤ c` using `(IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 (Algebra.IsAlgebraic.isAlgebraic c)`. Take `⟨k, hk, hkc⟩` from `hc.exists_integral_multiple`.

Use `⟨k * a, mul_ne_zero hk ha, ?_⟩` and prove the remaining obligations. Establish `h` using `L.smul_mem (⟨k • c, hkc⟩ : NumberField.RingOfIntegers E) hax`. Establish `e : (k * a) • c • x = (⟨k • c, hkc⟩ : NumberField.RingOfIntegers E) • a • x`. Express the relevant statement in the definitionally equal form `_ = (k • c) • a • x`. Rewrite using `[mul_smul, smul_comm a c x, smul_assoc]`.

Rewrite using `[e]`. Conclude with `h`.
-/
theorem exists_int_smul_mem {E : Type} [inst : Field E] [NumberField E] {n : ℕ}
    (L : Submodule (NumberField.RingOfIntegers E) (Fin n → E)) (hL : Submodule.IsLattice E L)
    (z : Fin n → E) : ∃ (m : ℤ), m ≠ (0 : ℤ) ∧ m • z ∈ L := by
  have hz : z ∈ Submodule.span E (L : Set (Fin n → E)) := by
    rw [hL.span_eq_top]; trivial
  induction hz using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨b, hb, hby⟩ := hy
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    rw [smul_add]
    refine L.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact zsmul_mem hax b
    · rw [mul_smul]; exact zsmul_mem hby a
  | smul c x _ hx =>
    obtain ⟨a, ha, hax⟩ := hx
    have hc : IsAlgebraic ℤ c :=
      (IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 (Algebra.IsAlgebraic.isAlgebraic c)
    obtain ⟨k, hk, hkc⟩ := hc.exists_integral_multiple
    refine ⟨k * a, mul_ne_zero hk ha, ?_⟩
    have h := L.smul_mem (⟨k • c, hkc⟩ : NumberField.RingOfIntegers E) hax
    have e : (k * a) • c • x
        = (⟨k • c, hkc⟩ : NumberField.RingOfIntegers E) • a • x := by
      change _ = (k • c) • a • x
      rw [mul_smul, smul_comm a c x, smul_assoc]
    rw [e]; exact h

end GlobalTheory.IntegerMultipleMembership
