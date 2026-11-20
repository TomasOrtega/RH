import Mathlib

namespace GlobalTheory.MulEqIntegerExists

open NumberField

/- English proof (translation)
Take `⟨a, b, hb, rfl⟩` from `IsFractionRing.div_surjective (A := RingOfIntegers E) c`. Establish `hb0 : b ≠ 0` using `nonZeroDivisors.ne_zero hb`. Use `⟨a, b, hb0, ?_⟩` and prove the remaining obligations. Establish `: algebraMap (RingOfIntegers E) E b ≠ 0` using `fun h => hb0 (IsFractionRing.injective (RingOfIntegers E) E (by rw [h, map_zero]))`. Rewrite using `[mul_div_assoc', mul_div_cancel_left₀ _ this]`.
-/
theorem exists_mul_eq_integer {E : Type} [Field E] [NumberField E] (c : E) :
    ∃ a b : RingOfIntegers E, b ≠ 0 ∧ (algebraMap (RingOfIntegers E) E b) * c
      = algebraMap (RingOfIntegers E) E a := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := RingOfIntegers E) c
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  refine ⟨a, b, hb0, ?_⟩
  have : algebraMap (RingOfIntegers E) E b ≠ 0 :=
    fun h => hb0 (IsFractionRing.injective (RingOfIntegers E) E (by rw [h, map_zero]))
  rw [mul_div_assoc', mul_div_cancel_left₀ _ this]

/- English proof (translation)
Establish `hy : y ∈ Submodule.span E (L : Set (Fin n → E))` using `by rw [hL]; trivial`. Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem x hx => exact ⟨1, one_ne_zero, by rw [one_smul]; exact hx⟩`. Consider the case `zero => exact ⟨1, one_ne_zero, by rw [smul_zero]; exact L.zero_mem⟩`. Consider the case `add x z _ _ hx hz`.

Take `⟨a, ha, hax⟩` from `hx`. Take `⟨b, hb, hbz⟩` from `hz`. Use `⟨a * b, mul_ne_zero ha hb, ?_⟩` and prove the remaining obligations. Rewrite using `[smul_add]`. Use `L.add_mem ?_ ?_` and prove the remaining obligations.

Rewrite using `[mul_comm, mul_smul]`. Conclude with `L.smul_mem b hax`. Rewrite using `[mul_smul]`. Conclude with `L.smul_mem a hbz`. Consider the case `smul c x _ hx`.

Take `⟨ν, hν, hνx⟩` from `hx`. Take `⟨a, b, hb, hab⟩` from `exists_mul_eq_integer c`. Use `⟨b * ν, mul_ne_zero hb hν, ?_⟩` and prove the remaining obligations. Establish `h : (b * ν) • (c • x) = a • (ν • x)`. Rewrite using `[← algebraMap_smul E (b * ν), ← algebraMap_smul E a, ← algebraMap_smul E ν, smul_smul, smul_smul, map_mul, ← hab]`.

Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h]`. Conclude with `L.smul_mem a hνx`.
-/
theorem exists_smul_mem {E : Type} [Field E] [NumberField E] {n : ℕ}
    (L : Submodule (RingOfIntegers E) (Fin n → E))
    (hL : Submodule.span E (L : Set (Fin n → E)) = ⊤) (y : Fin n → E) :
    ∃ ν : RingOfIntegers E, ν ≠ 0 ∧ ν • y ∈ L := by
  have hy : y ∈ Submodule.span E (L : Set (Fin n → E)) := by rw [hL]; trivial
  induction hy using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by rw [one_smul]; exact hx⟩
  | zero => exact ⟨1, one_ne_zero, by rw [smul_zero]; exact L.zero_mem⟩
  | add x z _ _ hx hz =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨b, hb, hbz⟩ := hz
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    rw [smul_add]
    refine L.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact L.smul_mem b hax
    · rw [mul_smul]; exact L.smul_mem a hbz
  | smul c x _ hx =>
    obtain ⟨ν, hν, hνx⟩ := hx
    obtain ⟨a, b, hb, hab⟩ := exists_mul_eq_integer c
    refine ⟨b * ν, mul_ne_zero hb hν, ?_⟩
    have h : (b * ν) • (c • x) = a • (ν • x) := by
      rw [← algebraMap_smul E (b * ν), ← algebraMap_smul E a, ← algebraMap_smul E ν,
        smul_smul, smul_smul, map_mul, ← hab]
      congr 1
      ring
    rw [h]
    exact L.smul_mem a hνx

end GlobalTheory.MulEqIntegerExists
