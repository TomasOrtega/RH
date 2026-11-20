import Mathlib
import Formalism.DegreeFormula.PointDegree.PowSum
import Formalism.DegreeFormula.PointDegree.PermExpInj
import Development.AbelianVarietyTheory.Definitions.Foundations.CurveCl
open MvPolynomial Formalism.DegreeFormula GlobalTheory.FlagPoly

namespace GlobalTheory

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[Ideal.span_le]`. Introduce and unpack `_ ⟨k, ⟨hk1, hkN⟩, rfl⟩`. Establish `he : ∀ j, 1 ≤ j → j ≤ N → esymm (Fin N) ℝ j ∈ Ideal.span ((fun k => esymm (Fin N) ℝ k) '' Set.Icc 1 N)` using `fun j h1 h2 => Ideal.subset_span ⟨j, ⟨h1, h2⟩, rfl⟩`. Use `show psum (Fin N) ℝ k ∈ Ideal.span _`.

Rewrite using `[psum_eq_mul_esymm_sub_sum (Fin N) ℝ k hk1]`. Use `Ideal.sub_mem _ (Ideal.mul_mem_left _ _ (he k hk1 hkN)) ?_` and prove the remaining obligations. Use `Ideal.sum_mem _ fun a ha => ?_` and prove the remaining obligations. Rewrite `ha` using `[Finset.mem_filter, Set.mem_Ioo]`. Conclude with `Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ (he a.1 ha.2.1 (ha.2.2.le.trans hkN)))`.

Rewrite using `[Ideal.span_le]`. Introduce and unpack `_ ⟨k, ⟨hk1, hkN⟩, rfl⟩`. Establish `hp : ∀ j, 1 ≤ j → j ≤ N → psum (Fin N) ℝ j ∈ Ideal.span ((fun k => psum (Fin N) ℝ k) '' Set.Icc 1 N)` using `fun j h1 h2 => Ideal.subset_span ⟨j, ⟨h1, h2⟩, rfl⟩`. Establish `h : (k : MvPolynomial (Fin N) ℝ) * esymm (Fin N) ℝ k ∈ Ideal.span ((fun k => psum (Fin N) ℝ k) '' Set.Icc 1 N)`. Rewrite using `[mul_esymm_eq_sum (Fin N) ℝ k]`.

Use `Ideal.mul_mem_left _ _ (Ideal.sum_mem _ fun a ha => ?_)` and prove the remaining obligations. Rewrite `ha` using `[Finset.mem_filter, Finset.HasAntidiagonal.mem_antidiagonal]`. Conclude with `Ideal.mul_mem_left _ _ (hp a.2 (by omega) (by omega))`. Establish `hk : (k : ℝ) ≠ 0` using `by exact_mod_cast (by omega : k ≠ 0)`. Establish `h2` using `Ideal.mul_mem_left _ (C (k : ℝ)⁻¹) h`.

Use `show esymm (Fin N) ℝ k ∈ Ideal.span _`. Rewrite `h2` using `[← mul_assoc, ← map_natCast (C : ℝ →+* MvPolynomial (Fin N) ℝ) k, ← map_mul, inv_mul_cancel₀ hk, map_one, one_mul]`. Then use the resulting hypothesis.
-/
theorem span_psum_eq_span_esymm (N : ℕ) :
    Ideal.span ((fun k => psum (Fin N) ℝ k) '' Set.Icc 1 N) =
      Ideal.span ((fun k => esymm (Fin N) ℝ k) '' Set.Icc 1 N) := by
  apply le_antisymm
  · rw [Ideal.span_le]
    rintro _ ⟨k, ⟨hk1, hkN⟩, rfl⟩
    have he : ∀ j, 1 ≤ j → j ≤ N → esymm (Fin N) ℝ j ∈
        Ideal.span ((fun k => esymm (Fin N) ℝ k) '' Set.Icc 1 N) :=
      fun j h1 h2 => Ideal.subset_span ⟨j, ⟨h1, h2⟩, rfl⟩
    show psum (Fin N) ℝ k ∈ Ideal.span _
    rw [psum_eq_mul_esymm_sub_sum (Fin N) ℝ k hk1]
    refine Ideal.sub_mem _ (Ideal.mul_mem_left _ _ (he k hk1 hkN)) ?_
    refine Ideal.sum_mem _ fun a ha => ?_
    rw [Finset.mem_filter, Set.mem_Ioo] at ha
    exact Ideal.mul_mem_right _ _
      (Ideal.mul_mem_left _ _ (he a.1 ha.2.1 (ha.2.2.le.trans hkN)))
  · rw [Ideal.span_le]
    rintro _ ⟨k, ⟨hk1, hkN⟩, rfl⟩
    have hp : ∀ j, 1 ≤ j → j ≤ N → psum (Fin N) ℝ j ∈
        Ideal.span ((fun k => psum (Fin N) ℝ k) '' Set.Icc 1 N) :=
      fun j h1 h2 => Ideal.subset_span ⟨j, ⟨h1, h2⟩, rfl⟩
    have h : (k : MvPolynomial (Fin N) ℝ) * esymm (Fin N) ℝ k ∈
        Ideal.span ((fun k => psum (Fin N) ℝ k) '' Set.Icc 1 N) := by
      rw [mul_esymm_eq_sum (Fin N) ℝ k]
      refine Ideal.mul_mem_left _ _ (Ideal.sum_mem _ fun a ha => ?_)
      rw [Finset.mem_filter, Finset.HasAntidiagonal.mem_antidiagonal] at ha
      exact Ideal.mul_mem_left _ _ (hp a.2 (by omega) (by omega))
    have hk : (k : ℝ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
    have h2 := Ideal.mul_mem_left _ (C (k : ℝ)⁻¹) h
    show esymm (Fin N) ℝ k ∈ Ideal.span _
    rwa [← mul_assoc, ← map_natCast (C : ℝ →+* MvPolynomial (Fin N) ℝ) k, ← map_mul,
      inv_mul_cancel₀ hk, map_one, one_mul] at h2

end GlobalTheory
