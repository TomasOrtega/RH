import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSingle
open Matrix Formalism.UG Formalism.L2.DIV GlobalTheory.LevNorm

namespace GlobalTheory

/- English proof (translation)
Use `set S := Algebra.adjoin R ((fun x : GL (Fin n) R => (x : Matrix (Fin n) (Fin n) R)) '' Set.univ)`. Establish `hoff : ∀ i j : Fin n, i ≠ j → Matrix.single i j (1:R) ∈ S`. Introduce `i j hij`. Establish `hu : IsUnit (Matrix.transvection i j (1:R))` using `(Matrix.isUnit_iff_isUnit_det _).mpr (by rw [det_transvection_of_ne _ _ hij]; exact isUnit_one)`. Establish `hmem : Matrix.transvection i j (1:R) ∈ S` using `Algebra.subset_adjoin ⟨hu.unit, Set.mem_univ _, rfl⟩`.

Establish `: Matrix.single i j (1:R) = Matrix.transvection i j 1 - 1`. Simplify using `[Matrix.transvection]`. Rewrite using `[this]`. Conclude with `S.sub_mem hmem S.one_mem`. Establish `hall : ∀ i j : Fin n, Matrix.single i j (1:R) ∈ S`.

Introduce `i j`. Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Distinguish the cases in `h : ∃ k, k ≠ i`. Take `⟨k, hk⟩` from `h`.

Establish `: Matrix.single i i (1:R) = Matrix.single i k 1 * Matrix.single k i 1`. Rewrite using `[Matrix.single_mul_single_same, mul_one]`. Rewrite using `[this]`. Conclude with `S.mul_mem (hoff _ _ (Ne.symm hk)) (hoff _ _ hk)`. Use `push_neg at h`.

Establish `: Matrix.single i i (1:R) = 1`. Use extensionality with `a b`. Rewrite using `[h a, h b]`. Simplify using the standard rewrite rules. Rewrite using `[this]`.

Conclude with `S.one_mem`. Conclude with `hoff i j hij`. Rewrite using `[eq_top_iff]`. Introduce `M _`. Rewrite using `[Matrix.matrix_eq_sum_single M]`.

Use `S.sum_mem fun i _ => S.sum_mem fun j _ => ?_` and prove the remaining obligations. Establish `: Matrix.single i j (M i j) = M i j • Matrix.single i j 1`. Rewrite using `[Matrix.smul_single, smul_eq_mul, mul_one]`. Rewrite using `[this]`. Conclude with `S.smul_mem (hall i j) _`.
-/
theorem adjoin_range_GL_eq_top (R : Type) [CommRing R] (n : ℕ) :
    Algebra.adjoin R ((fun x : GL (Fin n) R => (x : Matrix (Fin n) (Fin n) R)) '' Set.univ) = ⊤ := by
  set S := Algebra.adjoin R ((fun x : GL (Fin n) R => (x : Matrix (Fin n) (Fin n) R)) '' Set.univ)
  have hoff : ∀ i j : Fin n, i ≠ j → Matrix.single i j (1:R) ∈ S := by
    intro i j hij
    have hu : IsUnit (Matrix.transvection i j (1:R)) :=
      (Matrix.isUnit_iff_isUnit_det _).mpr (by rw [det_transvection_of_ne _ _ hij]; exact isUnit_one)
    have hmem : Matrix.transvection i j (1:R) ∈ S :=
      Algebra.subset_adjoin ⟨hu.unit, Set.mem_univ _, rfl⟩
    have : Matrix.single i j (1:R) = Matrix.transvection i j 1 - 1 := by
      simp [Matrix.transvection]
    rw [this]; exact S.sub_mem hmem S.one_mem
  have hall : ∀ i j : Fin n, Matrix.single i j (1:R) ∈ S := by
    intro i j
    by_cases hij : i = j
    · subst hij
      by_cases h : ∃ k, k ≠ i
      · obtain ⟨k, hk⟩ := h
        have : Matrix.single i i (1:R) = Matrix.single i k 1 * Matrix.single k i 1 := by
          rw [Matrix.single_mul_single_same, mul_one]
        rw [this]; exact S.mul_mem (hoff _ _ (Ne.symm hk)) (hoff _ _ hk)
      · push_neg at h
        have : Matrix.single i i (1:R) = 1 := by
          ext a b
          rw [h a, h b]; simp
        rw [this]; exact S.one_mem
    · exact hoff i j hij
  rw [eq_top_iff]
  intro M _
  rw [Matrix.matrix_eq_sum_single M]
  refine S.sum_mem fun i _ => S.sum_mem fun j _ => ?_
  have : Matrix.single i j (M i j) = M i j • Matrix.single i j 1 := by
    rw [Matrix.smul_single, smul_eq_mul, mul_one]
  rw [this]; exact S.smul_mem (hall i j) _

end GlobalTheory
