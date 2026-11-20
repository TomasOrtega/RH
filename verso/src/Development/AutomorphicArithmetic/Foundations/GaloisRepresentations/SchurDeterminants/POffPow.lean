import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SchurDeterminants.PairSplit

open Finset MvPolynomial UpperTheory.Gal.Schur

/- English proof (translation)
Introduce `hS hV hP R _ _ n lam g y`. Establish `key : ∀ i : Fin n, vdm (scaleOff y i g) = y ^ (n - 1).choose 2 * ((-1) ^ (i : ℕ) * vdmAway i g * ∏ k ∈ univ.erase i, (g i - y * g k))`. Introduce `i`. Establish `h1 : vdmAway i (scaleOff y i g) = y ^ (n - 1).choose 2 * vdmAway i g`. Rewrite using `[← (hP n i).2, ← Finset.prod_pow_eq_pow_sum]`.

Unfold `vdmAway`. Rewrite using `[← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun a ha => ?_` and prove the remaining obligations. Establish `ha' : a ≠ i` using `(Finset.mem_erase.mp ha).1`. Combine the equalities or inequalities in the displayed calculation.

Use `Finset.prod_congr rfl fun b hb => ?_` and prove the remaining obligations. Establish `hb' : b ≠ i` using `(Finset.mem_erase.mp hb).1`. Simplify using `[scaleOff, ha', hb', mul_sub]`. Use `_ = y ^ ((Finset.Ioi a).erase i).card * ∏ b ∈ (Finset.Ioi a).erase i, (g a - g b) := by`. Rewrite using `[Finset.prod_mul_distrib, Finset.prod_const]`.

Establish `h2 : ∏ k ∈ univ.erase i, (scaleOff y i g i - scaleOff y i g k) = ∏ k ∈ univ.erase i, (g i - y * g k)`. Use `Finset.prod_congr rfl fun k hk => ?_` and prove the remaining obligations. Establish `hk' : k ≠ i` using `(Finset.mem_erase.mp hk).1`. Simplify using `[scaleOff, hk']`. Rewrite using `[hV R n (scaleOff y i g) i, h1, h2]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hL : y ^ (n - 1).choose 2 * ∑ i, sch lam (scaleOff y i g) * ((-1) ^ (i : ℕ) * vdmAway i g * ∏ k ∈ univ.erase i, (g i - y * g k)) = ∑ i, sch lam (scaleOff y i g) * vdm (scaleOff y i g)`. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[key i]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hR : ∀ i : Fin n, y ^ (∑ k ∈ univ.erase i, (lam k + (n - 1 - (k : ℕ)))) = y ^ (n - 1).choose 2 * y ^ (∑ k ∈ univ.erase i, lam k + (i : ℕ))`. Introduce `i`. Rewrite using `[Finset.sum_add_distrib, (hP n i).1, ← pow_add]`. Use `congr 1`.

Use linear arithmetic over natural numbers and integers. Rewrite using `[hL, hS R n lam g y, Finset.sum_congr rfl fun i _ => hR i, ← Finset.mul_sum]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem UpperTheory.Gal.Schur.offClrPow_of :
    SchurYOffClr → VdmSplit → PairCount → OffClrPow := by
  intro hS hV hP R _ _ n lam g y
  have key : ∀ i : Fin n, vdm (scaleOff y i g) = y ^ (n - 1).choose 2 *
      ((-1) ^ (i : ℕ) * vdmAway i g * ∏ k ∈ univ.erase i, (g i - y * g k)) := by
    intro i
    have h1 : vdmAway i (scaleOff y i g) = y ^ (n - 1).choose 2 * vdmAway i g := by
      rw [← (hP n i).2, ← Finset.prod_pow_eq_pow_sum]
      unfold vdmAway
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun a ha => ?_
      have ha' : a ≠ i := (Finset.mem_erase.mp ha).1
      calc ∏ b ∈ (Finset.Ioi a).erase i, (scaleOff y i g a - scaleOff y i g b)
          = ∏ b ∈ (Finset.Ioi a).erase i, (y * (g a - g b)) := by
            refine Finset.prod_congr rfl fun b hb => ?_
            have hb' : b ≠ i := (Finset.mem_erase.mp hb).1
            simp [scaleOff, ha', hb', mul_sub]
        _ = y ^ ((Finset.Ioi a).erase i).card * ∏ b ∈ (Finset.Ioi a).erase i, (g a - g b) := by
            rw [Finset.prod_mul_distrib, Finset.prod_const]
    have h2 : ∏ k ∈ univ.erase i, (scaleOff y i g i - scaleOff y i g k) =
        ∏ k ∈ univ.erase i, (g i - y * g k) := by
      refine Finset.prod_congr rfl fun k hk => ?_
      have hk' : k ≠ i := (Finset.mem_erase.mp hk).1
      simp [scaleOff, hk']
    rw [hV R n (scaleOff y i g) i, h1, h2]
    ring
  have hL : y ^ (n - 1).choose 2 * ∑ i, sch lam (scaleOff y i g) *
      ((-1) ^ (i : ℕ) * vdmAway i g * ∏ k ∈ univ.erase i, (g i - y * g k)) =
      ∑ i, sch lam (scaleOff y i g) * vdm (scaleOff y i g) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [key i]
    ring
  have hR : ∀ i : Fin n, y ^ (∑ k ∈ univ.erase i, (lam k + (n - 1 - (k : ℕ)))) =
      y ^ (n - 1).choose 2 * y ^ (∑ k ∈ univ.erase i, lam k + (i : ℕ)) := by
    intro i
    rw [Finset.sum_add_distrib, (hP n i).1, ← pow_add]
    congr 1
    omega
  rw [hL, hS R n lam g y, Finset.sum_congr rfl fun i _ => hR i, ← Finset.mul_sum]
  ring
