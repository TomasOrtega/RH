import Mathlib
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsCoinv
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset

noncomputable section

/- English proof (translation)
Introduce `σ R _ p a m d hp`. Establish `hterm : ∀ i, homogeneousComponent d (p * homogeneousComponent i a) = if d = m + i then p * homogeneousComponent i a else 0` using `fun i => homogeneousComponent_of_mem ((mem_homogeneousSubmodule _ _).mpr (hp.mul (homogeneousComponent_isHomogeneous i a)))`. Use `conv_lhs => rw [← sum_homogeneousComponent a, Finset.mul_sum, map_sum]`. Repeatedly rewrite using `[hterm]`. Use `split_ifs with hmd`.

Establish `hcongr : ∀ i ∈ range (a.totalDegree + 1), (if d = m + i then p * homogeneousComponent i a else 0) = if d - m = i then p * homogeneousComponent i a else 0`. Introduce `i _`. Use `congr 1`. Conclude with `propext ⟨fun h => by omega, fun h => by omega⟩`. Rewrite using `[Finset.sum_congr rfl hcongr, Finset.sum_ite_eq]`.

Use `split_ifs with hmem`. Both sides reduce to the same expression. Rewrite `hmem` using `[Finset.mem_range, not_lt]`. Rewrite using `[homogeneousComponent_eq_zero (d - m) a (by omega), mul_zero]`. Conclude with `Finset.sum_eq_zero fun i _ => if_neg (by omega)`.
-/
theorem HomogeneousComponentMul.proof : HomogeneousComponentMul.Statement := by
  intro σ R _ p a m d hp
  have hterm : ∀ i, homogeneousComponent d (p * homogeneousComponent i a) =
      if d = m + i then p * homogeneousComponent i a else 0 := fun i =>
    homogeneousComponent_of_mem
      ((mem_homogeneousSubmodule _ _).mpr (hp.mul (homogeneousComponent_isHomogeneous i a)))
  conv_lhs => rw [← sum_homogeneousComponent a, Finset.mul_sum, map_sum]
  simp_rw [hterm]
  split_ifs with hmd
  · have hcongr : ∀ i ∈ range (a.totalDegree + 1),
        (if d = m + i then p * homogeneousComponent i a else 0) =
          if d - m = i then p * homogeneousComponent i a else 0 := by
      intro i _
      congr 1
      exact propext ⟨fun h => by omega, fun h => by omega⟩
    rw [Finset.sum_congr rfl hcongr, Finset.sum_ite_eq]
    split_ifs with hmem
    · rfl
    · rw [Finset.mem_range, not_lt] at hmem
      rw [homogeneousComponent_eq_zero (d - m) a (by omega), mul_zero]
  · exact Finset.sum_eq_zero fun i _ => if_neg (by omega)

end

end GroundTheory.Heights₂.Heights.RestTerms
