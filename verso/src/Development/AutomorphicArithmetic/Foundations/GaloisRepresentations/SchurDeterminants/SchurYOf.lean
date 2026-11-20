import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SchurDeterminants.PairSplit

open Finset MvPolynomial UpperTheory.Gal.Schur

/- English proof (translation)
Introduce `hOff hSplit R _ _ n lam g y hu`. Establish `hv : IsUnit (vdm g)`. Unfold `vdm`. Use `IsUnit.prod_iff.mpr fun i _ => IsUnit.prod_iff.mpr fun j hj => ?_` and prove the remaining obligations. Establish `hij : i < j` using `by simpa using hj`.

Simplify using `using (hu i j (ne_of_gt hij)).neg`. Establish `hScale : ∀ i, vdm (scaleAt y i g) = (-1) ^ (i : ℕ) * vdmAway i g * ∏ k ∈ univ.erase i, (y * g i - g k)`. Introduce `i`. Rewrite using `[hSplit R n (scaleAt y i g) i]`. Use `congr 1`.

Use `congr 1`. Unfold `vdmAway`. Use `Finset.prod_congr rfl fun a ha => Finset.prod_congr rfl fun b hb => ?_` and prove the remaining obligations. Establish `ha' : a ≠ i` using `Finset.ne_of_mem_erase ha`. Establish `hb' : b ≠ i` using `Finset.ne_of_mem_erase hb`.

Simplify using `[scaleAt, ha', hb']`. Use `Finset.prod_congr rfl fun k hk => ?_` and prove the remaining obligations. Establish `hk' : k ≠ i` using `Finset.ne_of_mem_erase hk`. Simplify using `[scaleAt, hk']`. Establish `key : ∀ i, (∏ k ∈ univ.erase i, (g k - y * g i) * Ring.inverse (g k - g i)) * ∏ k ∈ univ.erase i, (g i - g k) = ∏ k ∈ univ.erase i, (y * g i - g k)`.

Introduce `i`. Rewrite using `[← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun k hk => ?_` and prove the remaining obligations. Establish `hki : k ≠ i` using `Finset.ne_of_mem_erase hk`. Rewrite using `[show g i - g k = -(g k - g i) by ring, mul_neg, mul_assoc, Ring.inverse_mul_cancel _ (hu i k hki), mul_one]`.

Expand and normalize the polynomial expressions, which then agree. Apply `hv.mul_right_cancel` to reduce the goal to its premises. Establish `hR : sch lam g * (∑ i : Fin n, y ^ (lam i + (n - 1 - (i : ℕ)))) * vdm g = sch lam g * vdm g * ∑ i : Fin n, y ^ (lam i + (n - 1 - (i : ℕ)))` using `by ring`. Rewrite using `[hR, ← hOff R n lam g y, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[hScale i, hSplit R n g i, ← key i]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem UpperTheory.Gal.Schur.schurY_of :
    SchurYClr → VdmSplit → SchurY := by
  intro hOff hSplit R _ _ n lam g y hu
  have hv : IsUnit (vdm g) := by
    unfold vdm
    refine IsUnit.prod_iff.mpr fun i _ => IsUnit.prod_iff.mpr fun j hj => ?_
    have hij : i < j := by simpa using hj
    simpa using (hu i j (ne_of_gt hij)).neg
  have hScale : ∀ i, vdm (scaleAt y i g) =
      (-1) ^ (i : ℕ) * vdmAway i g * ∏ k ∈ univ.erase i, (y * g i - g k) := by
    intro i
    rw [hSplit R n (scaleAt y i g) i]
    congr 1
    · congr 1
      unfold vdmAway
      refine Finset.prod_congr rfl fun a ha => Finset.prod_congr rfl fun b hb => ?_
      have ha' : a ≠ i := Finset.ne_of_mem_erase ha
      have hb' : b ≠ i := Finset.ne_of_mem_erase hb
      simp [scaleAt, ha', hb']
    · refine Finset.prod_congr rfl fun k hk => ?_
      have hk' : k ≠ i := Finset.ne_of_mem_erase hk
      simp [scaleAt, hk']
  have key : ∀ i, (∏ k ∈ univ.erase i, (g k - y * g i) * Ring.inverse (g k - g i)) *
      ∏ k ∈ univ.erase i, (g i - g k) = ∏ k ∈ univ.erase i, (y * g i - g k) := by
    intro i
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k hk => ?_
    have hki : k ≠ i := Finset.ne_of_mem_erase hk
    rw [show g i - g k = -(g k - g i) by ring, mul_neg, mul_assoc,
      Ring.inverse_mul_cancel _ (hu i k hki), mul_one]
    ring
  apply hv.mul_right_cancel
  have hR : sch lam g * (∑ i : Fin n, y ^ (lam i + (n - 1 - (i : ℕ)))) * vdm g =
      sch lam g * vdm g * ∑ i : Fin n, y ^ (lam i + (n - 1 - (i : ℕ))) := by ring
  rw [hR, ← hOff R n lam g y, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hScale i, hSplit R n g i, ← key i]
  ring
