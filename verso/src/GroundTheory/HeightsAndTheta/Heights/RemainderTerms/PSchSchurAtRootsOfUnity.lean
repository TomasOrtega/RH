import Mathlib
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Statements
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsSchur
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset

noncomputable section

/- English proof (translation)
Establish `h1 : (Iic i).card • 1 ≤ ∑ j ∈ Iic i, nu j` using `Finset.card_nsmul_le_sum _ _ _ fun j hj => le_trans hi (hanti (Finset.mem_Iic.mp hj))`. Establish `h2 : ∑ j ∈ Iic i, nu j ≤ ∑ j, nu j` using `Finset.sum_le_sum_of_subset (Finset.subset_univ _)`. Rewrite `h1` using `[Fin.card_Iic, smul_eq_mul, mul_one]`. Use linear arithmetic over natural numbers and integers.
-/
theorem schurAtRoots_place_lt {r k : ℕ} (nu : Fin r → ℕ) (hanti : Antitone nu)
    (hsum : ∑ i, nu i = k) (i : Fin r) (hi : 1 ≤ nu i) : (i : ℕ) < k := by
  have h1 : (Iic i).card • 1 ≤ ∑ j ∈ Iic i, nu j :=
    Finset.card_nsmul_le_sum _ _ _ fun j hj => le_trans hi (hanti (Finset.mem_Iic.mp hj))
  have h2 : ∑ j ∈ Iic i, nu j ≤ ∑ j, nu j :=
    Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  rw [Fin.card_Iic, smul_eq_mul, mul_one] at h1
  omega

/- English proof (translation)
Introduce `N r k nu hk hkN hanti hsum`. Use `set nu' : Fin k → ℕ := fun i => if h : (i : ℕ) < r then nu ⟨i, h⟩ else 0 with hnu'`. Establish `hplace` using `schurAtRoots_place_lt nu hanti hsum`. Establish `hanti' : Antitone nu'`. Introduce `i j hij`.

Simplify using `only [hnu']`. Distinguish the cases in `hj : (j : ℕ) < r`. Establish `hi : (i : ℕ) < r` using `lt_of_le_of_lt (Fin.le_def.mp hij) hj`. Rewrite using `[dif_pos hi, dif_pos hj]`. Conclude with `hanti (Fin.le_def.mpr (Fin.le_def.mp hij))`.

Rewrite using `[dif_neg hj]`. Conclude with `Nat.zero_le _`. Establish `hsum' : ∑ i, nu' i = k` using `by set g : ℕ → ℕ := fun i => if h : i < r then nu ⟨i, h⟩ else 0 with hg`. Establish `e1 : ∑ i, nu' i = ∑ i ∈ range k, g i`. Rewrite using `[← Fin.sum_univ_eq_sum_range]`.

Establish `e2 : ∑ i, nu i = ∑ i ∈ range r, g i`. Rewrite using `[← Fin.sum_univ_eq_sum_range]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Simplify using `only [hg, dif_pos i.isLt]`. Establish `hgk : ∀ i, k ≤ i → g i = 0`.

Introduce `i hi`. Simplify using `only [hg]`. Use `split_ifs with h`. Assume the negation of the conclusion as `hne`. Use `hplace ⟨i, h⟩ (Nat.one_le_iff_ne_zero.mpr hne)` as an intermediate fact.

Simplify using `at this`. Use linear arithmetic over natural numbers and integers. Both sides reduce to the same expression. Establish `hgr : ∀ i, r ≤ i → g i = 0`. Introduce `i hi; simp only [hg]; rw [dif_neg (by omega)]`.

Establish `e3 : ∑ i ∈ range k, g i = ∑ i ∈ range (r + k), g i` using `Finset.sum_subset (Finset.range_mono (by omega)) fun i _ hni => hgk i (not_lt.mp (fun h => hni (Finset.mem_range.mpr h)))`. Establish `e4 : ∑ i ∈ range r, g i = ∑ i ∈ range (r + k), g i` using `Finset.sum_subset (Finset.range_mono (by omega)) fun i _ hni => hgr i (not_lt.mp (fun h => hni (Finset.mem_range.mpr h)))`. Rewrite using `[e1, e3, ← e4, ← e2, hsum]`. Rewrite using `[h1 (Fin N) r k nu hanti hsum, h2 N k k _ hk hkN, h3 k nu' hk hanti' hsum']`. Establish `hcond : (∀ i : Fin k, (i : ℕ) ≠ 0 → nu' i ≤ 1) ↔ (∀ i : Fin r, (i : ℕ) ≠ 0 → nu i ≤ 1)`.

Prove the components needed by the constructor for the conclusion. Introduce `H i hi0`. Distinguish the cases in `hz : nu i = 0`. Rewrite using `[hz]`. Conclude with `Nat.zero_le _`.

Establish `hik` using `hplace i (Nat.one_le_iff_ne_zero.mpr hz)`. Use `H ⟨i, hik⟩ hi0` as an intermediate fact. Simplify using `only [hnu', dif_pos i.isLt] at this`. Conclude with `this`. Introduce `H i hi0`.

Simplify using `only [hnu']`. Use `split_ifs with h`. Conclude with `H ⟨i, h⟩ hi0`. Conclude with `Nat.zero_le _`. Establish `hcard : (univ.filter fun i : Fin k => (i : ℕ) ≠ 0 ∧ nu' i = 1).card = (univ.filter fun i : Fin r => (i : ℕ) ≠ 0 ∧ nu i = 1).card`.

Use `Finset.card_bij' (fun i hi => ⟨i, by` and prove the remaining obligations. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and, hnu'] at hi`. Assume the negation of the conclusion as `h`. Rewrite `hi` using `[dif_neg h]`. Use the proof step `omega⟩)`.

Use the proof step `(fun i hi => ⟨i, by`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and] at hi`. Conclude with `hplace i (by omega)⟩) ?_ ?_ ?_ ?_`. Introduce `i hi`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and, hnu'] at hi ⊢`.

Take `⟨h0, h1⟩` from `hi`. Use `split_ifs at h1 with h`. Conclude with `⟨h0, h1⟩`. Introduce `i hi`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and, hnu'] at hi ⊢`.

Use `⟨hi.1, ?_⟩` and prove the remaining obligations. Rewrite using `[dif_pos i.isLt]`. Conclude with `hi.2`. Introduce `i hi`. Both sides reduce to the same expression.

Introduce `i hi`. Both sides reduce to the same expression. Simplify using `only [hcond, hcard]`.
-/
theorem SchSchurAtRootsOfUnity.proof (h1 : SchSchurRowsToK.Statement)
    (h2 : SchSchurEvalMatrix.Statement) (h3 : SchJTMatrixDetAtRoots.Statement) :
    SchSchurAtRootsOfUnity.Statement := by
  intro N r k nu hk hkN hanti hsum
  set nu' : Fin k → ℕ := fun i => if h : (i : ℕ) < r then nu ⟨i, h⟩ else 0 with hnu'
  have hplace := schurAtRoots_place_lt nu hanti hsum

  have hanti' : Antitone nu' := by
    intro i j hij
    simp only [hnu']
    by_cases hj : (j : ℕ) < r
    · have hi : (i : ℕ) < r := lt_of_le_of_lt (Fin.le_def.mp hij) hj
      rw [dif_pos hi, dif_pos hj]
      exact hanti (Fin.le_def.mpr (Fin.le_def.mp hij))
    · rw [dif_neg hj]; exact Nat.zero_le _

  have hsum' : ∑ i, nu' i = k := by
    set g : ℕ → ℕ := fun i => if h : i < r then nu ⟨i, h⟩ else 0 with hg
    have e1 : ∑ i, nu' i = ∑ i ∈ range k, g i := by
      rw [← Fin.sum_univ_eq_sum_range]
    have e2 : ∑ i, nu i = ∑ i ∈ range r, g i := by
      rw [← Fin.sum_univ_eq_sum_range]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [hg, dif_pos i.isLt]
    have hgk : ∀ i, k ≤ i → g i = 0 := by
      intro i hi
      simp only [hg]
      split_ifs with h
      · by_contra hne
        have := hplace ⟨i, h⟩ (Nat.one_le_iff_ne_zero.mpr hne)
        simp at this; omega
      · rfl
    have hgr : ∀ i, r ≤ i → g i = 0 := by
      intro i hi; simp only [hg]; rw [dif_neg (by omega)]
    have e3 : ∑ i ∈ range k, g i = ∑ i ∈ range (r + k), g i :=
      Finset.sum_subset (Finset.range_mono (by omega)) fun i _ hni =>
         hgk i (not_lt.mp (fun h => hni (Finset.mem_range.mpr h)))
    have e4 : ∑ i ∈ range r, g i = ∑ i ∈ range (r + k), g i :=
      Finset.sum_subset (Finset.range_mono (by omega)) fun i _ hni =>
         hgr i (not_lt.mp (fun h => hni (Finset.mem_range.mpr h)))
    rw [e1, e3, ← e4, ← e2, hsum]
  rw [h1 (Fin N) r k nu hanti hsum, h2 N k k _ hk hkN, h3 k nu' hk hanti' hsum']

  have hcond : (∀ i : Fin k, (i : ℕ) ≠ 0 → nu' i ≤ 1) ↔ (∀ i : Fin r, (i : ℕ) ≠ 0 → nu i ≤ 1) := by
    constructor
    · intro H i hi0
      by_cases hz : nu i = 0
      · rw [hz]; exact Nat.zero_le _
      · have hik := hplace i (Nat.one_le_iff_ne_zero.mpr hz)
        have := H ⟨i, hik⟩ hi0
        simp only [hnu', dif_pos i.isLt] at this
        exact this
    · intro H i hi0
      simp only [hnu']
      split_ifs with h
      · exact H ⟨i, h⟩ hi0
      · exact Nat.zero_le _

  have hcard : (univ.filter fun i : Fin k => (i : ℕ) ≠ 0 ∧ nu' i = 1).card =
      (univ.filter fun i : Fin r => (i : ℕ) ≠ 0 ∧ nu i = 1).card := by
    refine Finset.card_bij'
      (fun i hi => ⟨i, by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, hnu'] at hi
        by_contra h; rw [dif_neg h] at hi; omega⟩)
      (fun i hi => ⟨i, by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
        exact hplace i (by omega)⟩) ?_ ?_ ?_ ?_
    · intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, hnu'] at hi ⊢
      obtain ⟨h0, h1⟩ := hi
      split_ifs at h1 with h
      exact ⟨h0, h1⟩
    · intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, hnu'] at hi ⊢
      refine ⟨hi.1, ?_⟩
      rw [dif_pos i.isLt]; exact hi.2
    · intro i hi; rfl
    · intro i hi; rfl
  simp only [hcond, hcard]

end

end GroundTheory.Heights₂.Heights.RestTerms
