import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OmAOneApply
open Matrix MeasureTheory ValuativeRel GlobalTheory.SplitFlip GlobalTheory.SmGL GlobalTheory.WeilM GlobalTheory.RankFibre GlobalTheory.SplitWeil GlobalTheory.RankFibreKer

namespace GlobalTheory.RankFibreKer

/- English proof (translation)
Introduce and unpack `⟨J, hJ, hZ⟩ ⟨J', hJ', hgZ⟩`. Establish `m1 : minor Z J = 1` using `by rw [minor, hJ, det_one]`. Establish `m1' : minor (g.val * Z) J' = 1` using `by rw [minor, hJ', det_one]`. Establish `e1 : valuation k (g.val.det) * valuation k (minor Z J') = 1`. Rewrite using `[← map_mul, ← minor_mul, m1', map_one]`.

Establish `hg : valuation k (g.val.det) ≤ 1`. Use `(hgZ J).1` as an intermediate fact. Rewrite `this` using `[minor_mul, m1, mul_one]`. Then use the resulting hypothesis. Establish `hZJ' : valuation k (minor Z J') = 1`. Use `le_antisymm (hZ J').1 ?_` and prove the remaining obligations.

Combine the equalities or inequalities in the displayed calculation. Establish `hg1 : valuation k (g.val.det) = 1` using `by rwa [hZJ', mul_one] at e1`. Establish `hJJ : J = J'`. Break down `lt_trichotomy (idx J') (idx J) with h | h | h` into its components or cases. Conclude with `absurd ((hZ J').2 h) (by rw [hZJ']; exact lt_irrefl _)`.

Conclude with `(idx.injective h).symm`. Use `(hgZ J).2 h` as an intermediate fact. Rewrite `this` using `[minor_mul, m1, mul_one, hg1]`. Conclude with `absurd this (lt_irrefl _)`. Substitute `hJJ` using the available equality.

Establish `hsub : (g.val * Z).submatrix id J = g.val * Z.submatrix id J`. Use extensionality with `i j`. Simplify using `[Matrix.mul_apply, submatrix_apply]`. Rewrite `hJ'` using `[hsub, hJ, Matrix.mul_one]`. Conclude with `Units.ext hJ'`.
-/
theorem eq_one_of_mem_slice_of_mul_mem_slice (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (a d : ℕ) (Z : Matrix (Fin a) (Fin d) k) (g : GL (Fin a) k) :
    Z ∈ slice k a d → g.val * Z ∈ slice k a d → g = 1 := by
  rintro ⟨J, hJ, hZ⟩ ⟨J', hJ', hgZ⟩
  have m1 : minor Z J = 1 := by rw [minor, hJ, det_one]
  have m1' : minor (g.val * Z) J' = 1 := by rw [minor, hJ', det_one]
  have e1 : valuation k (g.val.det) * valuation k (minor Z J') = 1 := by
    rw [← map_mul, ← minor_mul, m1', map_one]
  have hg : valuation k (g.val.det) ≤ 1 := by
    have := (hgZ J).1
    rwa [minor_mul, m1, mul_one] at this
  have hZJ' : valuation k (minor Z J') = 1 := by
    refine le_antisymm (hZ J').1 ?_
    calc (1 : ValueGroupWithZero k) = valuation k (g.val.det) * valuation k (minor Z J') := e1.symm
      _ ≤ 1 * valuation k (minor Z J') := mul_le_mul_of_nonneg_right hg zero_le'
      _ = valuation k (minor Z J') := one_mul _
  have hg1 : valuation k (g.val.det) = 1 := by rwa [hZJ', mul_one] at e1
  have hJJ : J = J' := by
    rcases lt_trichotomy (idx J') (idx J) with h | h | h
    · exact absurd ((hZ J').2 h) (by rw [hZJ']; exact lt_irrefl _)
    · exact (idx.injective h).symm
    · have := (hgZ J).2 h
      rw [minor_mul, m1, mul_one, hg1] at this
      exact absurd this (lt_irrefl _)
  subst hJJ
  have hsub : (g.val * Z).submatrix id J = g.val * Z.submatrix id J := by
    ext i j; simp [Matrix.mul_apply, submatrix_apply]
  rw [hsub, hJ, Matrix.mul_one] at hJ'
  exact Units.ext hJ'

end GlobalTheory.RankFibreKer
