import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModQPrin
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModJTau
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN

/- English proof (translation)
Introduce `Ω _ ε f f' l m h h' hl hf hc hexp`. Take `⟨⟨N, hN, hden⟩, C, hC⟩` from `hexp`. Establish `hl0 : l ≠ 0` using `hl.ne'`. Use `⟨⟨N * l.den, Nat.mul_pos hN l.den_pos, ?_⟩, max (C / l) 0, ?_⟩` and prove the remaining obligations. Introduce `s hs`.

Establish `hr : h.coeff (s / l) ≠ 0`. Introduce `h0`. Apply `hs` to reduce the goal to its premises. Use `hc (s / l)` as an intermediate fact. Rewrite `this` using `[div_mul_cancel₀ _ hl0, h0, map_zero, mul_zero]`.

Conclude with `(map_eq_zero ε).1 this`. Take `⟨n, hn⟩` from `hden _ hr`. Use `⟨n * l.num, ?_⟩` and prove the remaining obligations. Establish `hs' : s = s / l * l` using `by field_simp`. Establish `hN0 : (N : ℚ) ≠ 0` using `by exact_mod_cast hN.ne'`.

Establish `hd0 : (l.den : ℚ) ≠ 0` using `by exact_mod_cast l.den_pos.ne'`. Rewrite using `[hs', hn]`. Use `push_cast`. Rewrite using `[← Rat.mul_den_eq_num l]`. Clear the denominators using the available nonvanishing facts.

Introduce `z hz`. Establish `hz0 : 0 < z.im` using `lt_of_le_of_lt (le_max_right _ _) hz`. Establish `hlz : C < ((l : ℂ) * z + (m : ℂ)).im`. Establish `h1 : C / l < z.im` using `lt_of_le_of_lt (le_max_left _ _) hz`. Establish `h2 : C < z.im * l` using `(div_lt_iff₀ (by exact_mod_cast hl)).1 h1`.

Simplify `h2` using `[mul_comm]`. Rewrite using `[hf z hz0]`. Establish `key` using `hC _ hlz`. Rewrite using `[← (Equiv.mulRight₀ l hl0).hasSum_iff]`. Use `key using 1` and compare the differences between its conclusion and the goal.

Use function extensionality and compare the values at `r`. Establish `he : (Equiv.mulRight₀ l hl0) r = r * l` using `rfl`. Simplify using `only [Function.comp, he, hc r]`. Rewrite using `[mul_comm (Complex.exp _) (ε (h.coeff r)), mul_assoc, ← Complex.exp_add]`. Use `congr 2`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem isExp_comp_affine : ∀ (Ω : Type) [Field Ω] (ε : Ω →+* ℂ) (f f' : ℍ → ℂ) (l m : ℚ) (h h' : HahnSeries ℚ Ω), 0 < l →
    (∀ z ∈ Hs, up f' z = up f ((l : ℂ) * z + m)) →
    (∀ r : ℚ, ε (h'.coeff (r * l)) = Complex.exp (2 * Real.pi * Complex.I * ((r * m : ℚ) : ℂ)) * ε (h.coeff r)) →
    IsExp ε f h → IsExp ε f' h' := by
  intro Ω _ ε f f' l m h h' hl hf hc hexp
  obtain ⟨⟨N, hN, hden⟩, C, hC⟩ := hexp
  have hl0 : l ≠ 0 := hl.ne'
  refine ⟨⟨N * l.den, Nat.mul_pos hN l.den_pos, ?_⟩, max (C / l) 0, ?_⟩
  · intro s hs
    have hr : h.coeff (s / l) ≠ 0 := by
      intro h0
      apply hs
      have := hc (s / l)
      rw [div_mul_cancel₀ _ hl0, h0, map_zero, mul_zero] at this
      exact (map_eq_zero ε).1 this
    obtain ⟨n, hn⟩ := hden _ hr
    refine ⟨n * l.num, ?_⟩
    have hs' : s = s / l * l := by field_simp
    have hN0 : (N : ℚ) ≠ 0 := by exact_mod_cast hN.ne'
    have hd0 : (l.den : ℚ) ≠ 0 := by exact_mod_cast l.den_pos.ne'
    rw [hs', hn]
    push_cast
    rw [← Rat.mul_den_eq_num l]
    field_simp
  · intro z hz
    have hz0 : 0 < z.im := lt_of_le_of_lt (le_max_right _ _) hz
    have hlz : C < ((l : ℂ) * z + (m : ℂ)).im := by
      have h1 : C / l < z.im := lt_of_le_of_lt (le_max_left _ _) hz
      have h2 : C < z.im * l := (div_lt_iff₀ (by exact_mod_cast hl)).1 h1
      simpa [mul_comm] using h2
    rw [hf z hz0]
    have key := hC _ hlz
    rw [← (Equiv.mulRight₀ l hl0).hasSum_iff]
    convert key using 1
    funext r
    have he : (Equiv.mulRight₀ l hl0) r = r * l := rfl
    simp only [Function.comp, he, hc r]
    rw [mul_comm (Complex.exp _) (ε (h.coeff r)), mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast
    ring

end GlobalTheory.FN
