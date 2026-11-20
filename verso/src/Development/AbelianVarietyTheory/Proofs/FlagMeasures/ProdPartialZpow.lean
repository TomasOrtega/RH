import Mathlib
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SumFinEqSumCastLEOfVanish

open Matrix Finset Formalism.MainNotions.S GlobalTheory.Dec

namespace GlobalTheory.PhiTriangular

/- English proof (translation)
Set `m : ℕ → ℤ` to `fun k => if h : k < n then muInt lam ⟨k, h⟩ else 0`. Establish `h1 : ∀ i : Fin n, (if l ≤ i then sInt lam i else 0) = m (max i.val l.val) - m (max (i.val + 1) l.val)`. Introduce `i`. Distinguish the cases in `h : l ≤ i`. Establish `h' : l.val ≤ i.val` using `h`.

Rewrite using `[if_pos h, max_eq_left h', max_eq_left (by omega : l.val ≤ i.val + 1)]`. Simplify using `only [m, sInt, dif_pos i.isLt]`. Establish `h' : i.val < l.val` using `by simpa using h`. Rewrite using `[if_neg h, max_eq_right h'.le, max_eq_right (by omega : i.val + 1 ≤ l.val), sub_self]`. Simplify using `only [h1]`.

Rewrite using `[Fin.sum_univ_eq_sum_range (fun k => m (max k l.val) - m (max (k + 1) l.val)) n, Finset.sum_range_sub' (fun k => m (max k l.val)) n, max_eq_right (Nat.zero_le _), max_eq_left l.isLt.le]`. Simplify using `[m]`.
-/
theorem sum_sInt_from {n : ℕ} (lam : Fin n → ℝ) (l : Fin n) :
    ∑ i : Fin n, (if l ≤ i then sInt lam i else 0) = muInt lam l := by
  let m : ℕ → ℤ := fun k => if h : k < n then muInt lam ⟨k, h⟩ else 0
  have h1 : ∀ i : Fin n, (if l ≤ i then sInt lam i else 0) =
      m (max i.val l.val) - m (max (i.val + 1) l.val) := by
    intro i
    by_cases h : l ≤ i
    · have h' : l.val ≤ i.val := h
      rw [if_pos h, max_eq_left h', max_eq_left (by omega : l.val ≤ i.val + 1)]
      simp only [m, sInt, dif_pos i.isLt]
    · have h' : i.val < l.val := by simpa using h
      rw [if_neg h, max_eq_right h'.le, max_eq_right (by omega : i.val + 1 ≤ l.val), sub_self]
  simp only [h1]
  rw [Fin.sum_univ_eq_sum_range (fun k => m (max k l.val) - m (max (k + 1) l.val)) n,
    Finset.sum_range_sub' (fun k => m (max k l.val)) n, max_eq_right (Nat.zero_le _),
    max_eq_left l.isLt.le]
  simp [m]

/- English proof (translation)
Use `Finset.prod_of_injOn (Fin.castLE i.isLt) ((Fin.castLE_injective _).injOn) (by simp) ?_ ?_` and prove the remaining obligations. Introduce `k _ hk`. Rewrite using `[if_neg]`. Introduce `h`. Conclude with `hk ⟨⟨k.val, Nat.lt_succ_of_le h⟩, by simp, rfl⟩`.

Introduce `j _`. Rewrite using `[if_pos]`. Conclude with `Nat.le_of_lt_succ j.isLt`.
-/
theorem prod_castLE_succ {n : ℕ} (d : Fin n → ℂ) (i : Fin n) :
    ∏ j : Fin (i.val + 1), d (Fin.castLE i.isLt j) = ∏ l : Fin n, if l ≤ i then d l else 1 := by
  refine Finset.prod_of_injOn (Fin.castLE i.isLt) ((Fin.castLE_injective _).injOn) (by simp) ?_ ?_
  · intro k _ hk
    rw [if_neg]
    intro h
    exact hk ⟨⟨k.val, Nat.lt_succ_of_le h⟩, by simp, rfl⟩
  · intro j _
    rw [if_pos]
    exact Nat.le_of_lt_succ j.isLt

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp`. Consider the case `insert i s hi ih => rw [Finset.sum_insert hi, Finset.prod_insert hi, zpow_add₀ ha, ih]`.
-/
theorem zpow_finset_sum {ι : Type} (s : Finset ι) (f : ι → ℤ) {a : ℂ} (ha : a ≠ 0) :
    a ^ (∑ i ∈ s, f i) = ∏ i ∈ s, a ^ f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.prod_insert hi, zpow_add₀ ha, ih]

/- English proof (translation)
Simplify using `only [prod_castLE_succ, ← Finset.prod_zpow]`. Rewrite using `[Finset.prod_comm]`. Use `Finset.prod_congr rfl fun l _ => ?_` and prove the remaining obligations. Rewrite using `[← sum_sInt_from, ← Finset.sum_neg_distrib, zpow_finset_sum _ _ (hd l)]`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations.

Apply the tactic sequence `by_cases h : l ≤ i <;> simp [h]`.
-/
theorem prod_partial_zpow {n : ℕ} (lam : Fin n → ℝ) (d : Fin n → ℂ) (hd : ∀ l, d l ≠ 0) :
    ∏ i : Fin n, (∏ j : Fin (i.val + 1), d (Fin.castLE i.isLt j)) ^ (-(sInt lam i)) =
      ∏ l, d l ^ (-(muInt lam l)) := by
  simp only [prod_castLE_succ, ← Finset.prod_zpow]
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun l _ => ?_
  rw [← sum_sInt_from, ← Finset.sum_neg_distrib, zpow_finset_sum _ _ (hd l)]
  refine Finset.prod_congr rfl fun i _ => ?_
  by_cases h : l ≤ i <;> simp [h]

/- English proof (translation)
Introduce `n lam c z c' hc hc' hd hz`. Establish `hd' : ∀ l, c l l * c' l l ≠ 0` using `fun l => mul_ne_zero (hd l).1 (hd l).2`. Use `⟨fun i => ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[GlobalTheory.LeadMinorTri.leadMinor_lower_mul_mul_upper n c z c' hc hc']`. Conclude with `mul_ne_zero (Finset.prod_ne_zero_iff.2 fun j _ => hd' _) (hz i)`.

Unfold `Phi`. Simplify using `only [GlobalTheory.LeadMinorTri.leadMinor_lower_mul_mul_upper n c z c' hc hc', mul_zpow _ (leadMinor z _ _)]`. Rewrite using `[Finset.prod_mul_distrib, prod_partial_zpow lam (fun l => c l l * c' l l) hd']`.
-/
theorem phiTri : PhiTri := by
  intro n lam c z c' hc hc' hd hz
  have hd' : ∀ l, c l l * c' l l ≠ 0 := fun l => mul_ne_zero (hd l).1 (hd l).2
  refine ⟨fun i => ?_, ?_⟩
  · rw [GlobalTheory.LeadMinorTri.leadMinor_lower_mul_mul_upper n c z c' hc hc']
    exact mul_ne_zero (Finset.prod_ne_zero_iff.2 fun j _ => hd' _) (hz i)
  · unfold Phi
    simp only [GlobalTheory.LeadMinorTri.leadMinor_lower_mul_mul_upper n c z c' hc hc', mul_zpow _ (leadMinor z _ _)]
    rw [Finset.prod_mul_distrib, prod_partial_zpow lam (fun l => c l l * c' l l) hd']

end GlobalTheory.PhiTriangular
