import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.HeckeTraceSemi

set_option autoImplicit false

open Polynomial

namespace UpperTheory.Gal.LocalSmoothExtension

/- English proof (translation)
Introduce `F _ _ P hP`. Establish `hP0 : P ≠ 0` using `fun h => hP (by simp [h])`. Establish `hc : (P.coeff 0)⁻¹ ≠ 0` using `inv_ne_zero hP`. Establish `hrr : ∀ Q : F[X], Q.coeff 0 ≠ 0 → Q.reverse.reverse = Q`. Introduce `Q hQ`.

Establish `hQd : Q.reverse.natDegree = Q.natDegree`. Rewrite using `[reverse_natDegree, natTrailingDegree_eq_zero.mpr (Or.inr hQ), Nat.sub_zero]`. Use extensionality with `n`. Rewrite using `[coeff_reverse, hQd, coeff_reverse, revAt_invol]`. Establish `hdeg : P.reverse.natDegree = P.natDegree`.

Rewrite using `[reverse_natDegree, natTrailingDegree_eq_zero.mpr (Or.inr hP), Nat.sub_zero]`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Unfold `invPol`. Rewrite using `[natDegree_C_mul hc, hdeg]`. Unfold `invPol`.

Rewrite using `[mul_coeff_zero, coeff_C_zero, coeff_zero_reverse]`. Conclude with `mul_ne_zero hc (leadingCoeff_ne_zero.mpr hP0)`. Introduce `hs`. Unfold `invPol`. Establish `hrs : P.reverse.Separable`.

Rewrite using `[PerfectField.separable_iff_squarefree]`. Introduce `x hx`. Take `⟨y, hy⟩` from `hx`. Establish `hx0 : x.coeff 0 ≠ 0`. Introduce `h0`.

Establish `h1 : P.reverse.coeff 0 = 0`. Rewrite using `[hy, mul_coeff_zero, mul_coeff_zero, h0, zero_mul, zero_mul]`. Rewrite `h1` using `[coeff_zero_reverse]`. Conclude with `leadingCoeff_ne_zero.mpr hP0 h1`. Establish `hPx : x.reverse * x.reverse ∣ P`.

Use `⟨y.reverse, ?_⟩` and prove the remaining obligations. Rewrite using `[← hrr P hP, hy, reverse_mul_of_domain, reverse_mul_of_domain]`. Establish `hu : IsUnit x.reverse` using `hs.squarefree _ hPx`. Establish `hxd : x.natDegree = 0`. Establish `h1 : x.reverse.natDegree = 0` using `natDegree_eq_zero_of_isUnit hu`.

Rewrite `h1` using `[reverse_natDegree, natTrailingDegree_eq_zero.mpr (Or.inr hx0), Nat.sub_zero]`. Then use the resulting hypothesis. Rewrite using `[eq_C_of_natDegree_eq_zero hxd]`. Conclude with `isUnit_C.mpr (IsUnit.mk0 _ hx0)`. Rewrite using `[mul_comm]`. Conclude with `hrs.mul_unit (isUnit_C.mpr (IsUnit.mk0 _ hc))`.
-/
theorem invPolProps_of (hR : InvRoots) : InvPolProps := by
  intro F _ _ P hP
  have hP0 : P ≠ 0 := fun h => hP (by simp [h])
  have hc : (P.coeff 0)⁻¹ ≠ 0 := inv_ne_zero hP
  have hrr : ∀ Q : F[X], Q.coeff 0 ≠ 0 → Q.reverse.reverse = Q := by
    intro Q hQ
    have hQd : Q.reverse.natDegree = Q.natDegree := by
      rw [reverse_natDegree, natTrailingDegree_eq_zero.mpr (Or.inr hQ), Nat.sub_zero]
    ext n
    rw [coeff_reverse, hQd, coeff_reverse, revAt_invol]
  have hdeg : P.reverse.natDegree = P.natDegree := by
    rw [reverse_natDegree, natTrailingDegree_eq_zero.mpr (Or.inr hP), Nat.sub_zero]
  refine ⟨?_, ?_, ?_⟩
  · unfold invPol
    rw [natDegree_C_mul hc, hdeg]
  · unfold invPol
    rw [mul_coeff_zero, coeff_C_zero, coeff_zero_reverse]
    exact mul_ne_zero hc (leadingCoeff_ne_zero.mpr hP0)
  · intro hs
    unfold invPol
    have hrs : P.reverse.Separable := by
      rw [PerfectField.separable_iff_squarefree]
      intro x hx
      obtain ⟨y, hy⟩ := hx
      have hx0 : x.coeff 0 ≠ 0 := by
        intro h0
        have h1 : P.reverse.coeff 0 = 0 := by
          rw [hy, mul_coeff_zero, mul_coeff_zero, h0, zero_mul, zero_mul]
        rw [coeff_zero_reverse] at h1
        exact leadingCoeff_ne_zero.mpr hP0 h1
      have hPx : x.reverse * x.reverse ∣ P := by
        refine ⟨y.reverse, ?_⟩
        rw [← hrr P hP, hy, reverse_mul_of_domain, reverse_mul_of_domain]
      have hu : IsUnit x.reverse := hs.squarefree _ hPx
      have hxd : x.natDegree = 0 := by
        have h1 : x.reverse.natDegree = 0 := natDegree_eq_zero_of_isUnit hu
        rwa [reverse_natDegree, natTrailingDegree_eq_zero.mpr (Or.inr hx0), Nat.sub_zero] at h1
      rw [eq_C_of_natDegree_eq_zero hxd]
      exact isUnit_C.mpr (IsUnit.mk0 _ hx0)
    rw [mul_comm]
    exact hrs.mul_unit (isUnit_C.mpr (IsUnit.mk0 _ hc))

end UpperTheory.Gal.LocalSmoothExtension
