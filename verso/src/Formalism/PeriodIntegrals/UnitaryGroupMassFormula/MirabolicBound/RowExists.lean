import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MirabolicBound.Development

namespace PI.GGMirBoundW

open Finset Matrix

noncomputable section

open Classical

/- English proof (translation)
Introduce `F _ _ n r hr`. Choose the witnesses or unpack the hypotheses as in `⟨k, hk⟩ : ∃ k, r k ≠ 0 := by`. Assume the negation of the conclusion as `h`. Use `push_neg at h`. Conclude with `hr (funext h)`.

Use `set σ : Equiv.Perm (Fin (n + 1)) := Equiv.swap k (Fin.last n) with hσ`. Use `set A : Matrix (Fin (n + 1)) (Fin (n + 1)) F := Matrix.updateRow 1 (Fin.last n) (fun j => r (σ j)) with hA`. Establish `hAtri : A.BlockTriangular OrderDual.toDual`. Introduce `i j hij`. Establish `hij' : i < j` using `hij`.

Establish `hi : i ≠ Fin.last n` using `fun h => by`. Substitute `h` using the available equality. Conclude with `absurd hij' (not_lt.mpr (Fin.le_last j))`. Rewrite using `[hA, Matrix.updateRow_ne hi, Matrix.one_apply_ne (ne_of_lt hij')]`. Establish `hdetA : A.det = r k`.

Rewrite using `[Matrix.det_of_lowerTriangular A hAtri, Finset.prod_eq_single (Fin.last n)]`. Rewrite using `[hA, Matrix.updateRow_self]`. Simplify using `[hσ]`. Introduce `i _ hi`. Rewrite using `[hA, Matrix.updateRow_ne hi, Matrix.one_apply_eq]`.

Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`. Use `set B := A.submatrix id σ with hB`. Establish `hdetB : B.det ≠ 0`. Rewrite using `[hB, Matrix.det_permute', hdetA]`.

Use `mul_ne_zero ?_ hk` and prove the remaining obligations. Apply the tactic sequence `rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]`. Establish `hunit : IsUnit B` using `(Matrix.isUnit_iff_isUnit_det B).mpr (isUnit_iff_ne_zero.mpr hdetB)`. Use `⟨hunit.unit, fun j => ?_⟩` and prove the remaining obligations. Rewrite using `[IsUnit.unit_spec]`.

Simplify using `[hB, hA, hσ, Matrix.updateRow_self, Equiv.swap_apply_self]`.
-/
theorem rowExists : RowExists := by
  intro F _ _ n r hr
  obtain ⟨k, hk⟩ : ∃ k, r k ≠ 0 := by
    by_contra h
    push_neg at h
    exact hr (funext h)
  set σ : Equiv.Perm (Fin (n + 1)) := Equiv.swap k (Fin.last n) with hσ
  set A : Matrix (Fin (n + 1)) (Fin (n + 1)) F :=
    Matrix.updateRow 1 (Fin.last n) (fun j => r (σ j)) with hA
  have hAtri : A.BlockTriangular OrderDual.toDual := by
    intro i j hij
    have hij' : i < j := hij
    have hi : i ≠ Fin.last n := fun h => by
      subst h
      exact absurd hij' (not_lt.mpr (Fin.le_last j))
    rw [hA, Matrix.updateRow_ne hi, Matrix.one_apply_ne (ne_of_lt hij')]
  have hdetA : A.det = r k := by
    rw [Matrix.det_of_lowerTriangular A hAtri, Finset.prod_eq_single (Fin.last n)]
    · rw [hA, Matrix.updateRow_self]
      simp [hσ]
    · intro i _ hi
      rw [hA, Matrix.updateRow_ne hi, Matrix.one_apply_eq]
    · intro h
      exact absurd (Finset.mem_univ _) h
  set B := A.submatrix id σ with hB
  have hdetB : B.det ≠ 0 := by
    rw [hB, Matrix.det_permute', hdetA]
    refine mul_ne_zero ?_ hk
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
  have hunit : IsUnit B := (Matrix.isUnit_iff_isUnit_det B).mpr (isUnit_iff_ne_zero.mpr hdetB)
  refine ⟨hunit.unit, fun j => ?_⟩
  rw [IsUnit.unit_spec]
  simp [hB, hA, hσ, Matrix.updateRow_self, Equiv.swap_apply_self]

end

end PI.GGMirBoundW
