import Mathlib
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Statements
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsSchur
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.JacobiTrudi
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset

/- English proof (translation)
Introduce `σ _ _ r k nu hanti hsum`. Distinguish the cases in `hrk : r ≤ k`. Conclude with `(Schur.schur_padPartition σ nu k hrk).symm`. Use `replace hrk : k < r := Nat.lt_of_not_le hrk`. Establish `hzero : ∀ i : Fin r, k ≤ (i : ℕ) → nu i = 0`.

Introduce `i hi`. Assume the negation of the conclusion as `hne`. Establish `hpos : 1 ≤ nu i` using `Nat.one_le_iff_ne_zero.mpr hne`. Establish `h1 : ∑ j ∈ Finset.Iic i, 1 ≤ ∑ j ∈ Finset.Iic i, nu j` using `Finset.sum_le_sum fun j hj => le_trans hpos (hanti (Finset.mem_Iic.mp hj))`. Establish `h2 : ∑ j ∈ Finset.Iic i, nu j ≤ ∑ j, nu j` using `Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => Nat.zero_le _)`.

Simplify using `only [Finset.sum_const, smul_eq_mul, mul_one, Fin.card_Iic] at h1`. Use linear arithmetic over natural numbers and integers. Establish `heq : nu = Schur.padPartition r (fun i : Fin k => if h : (i : ℕ) < r then nu ⟨i, h⟩ else 0)`. Use function extensionality and compare the values at `i`. Simplify using `only [Schur.padPartition]`.

Distinguish the cases in `hik : (i : ℕ) < k`. Simplify using `[hik, i.isLt]`. Simplify using `only [hik, dite_false]`. Conclude with `hzero i (by omega)`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem SchSchurRowsToK.proof : SchSchurRowsToK.Statement := by
  intro σ _ _ r k nu hanti hsum
  by_cases hrk : r ≤ k
  · exact (Schur.schur_padPartition σ nu k hrk).symm
  · replace hrk : k < r := Nat.lt_of_not_le hrk
    have hzero : ∀ i : Fin r, k ≤ (i : ℕ) → nu i = 0 := by
      intro i hi
      by_contra hne
      have hpos : 1 ≤ nu i := Nat.one_le_iff_ne_zero.mpr hne
      have h1 : ∑ j ∈ Finset.Iic i, 1 ≤ ∑ j ∈ Finset.Iic i, nu j :=
        Finset.sum_le_sum fun j hj => le_trans hpos (hanti (Finset.mem_Iic.mp hj))
      have h2 : ∑ j ∈ Finset.Iic i, nu j ≤ ∑ j, nu j :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun _ _ _ => Nat.zero_le _)
      simp only [Finset.sum_const, smul_eq_mul, mul_one, Fin.card_Iic] at h1
      omega
    have heq : nu = Schur.padPartition r
        (fun i : Fin k => if h : (i : ℕ) < r then nu ⟨i, h⟩ else 0) := by
      funext i
      simp only [Schur.padPartition]
      by_cases hik : (i : ℕ) < k
      · simp [hik, i.isLt]
      · simp only [hik, dite_false]
        exact hzero i (by omega)
    calc schur σ nu
        = schur σ (Schur.padPartition r
            (fun i : Fin k => if h : (i : ℕ) < r then nu ⟨i, h⟩ else 0)) :=
          congrArg (schur σ) heq
      _ = _ := Schur.schur_padPartition σ _ r hrk.le

end GroundTheory.Heights₂.Heights.RestTerms
