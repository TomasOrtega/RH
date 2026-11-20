import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullFrameRight
open GlobalTheory.WholeFlag GlobalTheory.WholeFlag.Glue
open scoped Matrix

set_option autoImplicit false

namespace GlobalTheory.WholeFlag.Glue

/- English proof (translation)
Unfold `antiDiag`. Simplify using `only [Matrix.mulVec, dotProduct, Matrix.of_apply]`. Rewrite using `[Finset.sum_eq_single i.rev]`. Establish `h : (i : ℕ) + (i.rev : ℕ) = g - 1`. Use `i.2` as an intermediate fact.

Rewrite using `[Fin.val_rev]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[if_pos h, one_mul]`. Introduce `k _ hk`. Establish `h : ¬ ((i : ℕ) + (k : ℕ) = g - 1)`.

Introduce `h`. Apply `hk` to reduce the goal to its premises. Use `i.2` as an intermediate fact. Apply `Fin.ext` to reduce the goal to its premises. Rewrite using `[Fin.val_rev]`.

Use linear arithmetic over natural numbers and integers. Rewrite using `[if_neg h, zero_mul]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`.
-/
theorem antiDiag_mulVec_rev {κ : Type} [Field κ] {g : ℕ} (b : Fin g → κ) (i : Fin g) :
    (antiDiag κ g *ᵥ b) i = b i.rev := by
  unfold antiDiag
  simp only [Matrix.mulVec, dotProduct, Matrix.of_apply]
  rw [Finset.sum_eq_single i.rev]
  · have h : (i : ℕ) + (i.rev : ℕ) = g - 1 := by
      have := i.2
      rw [Fin.val_rev]; omega
    rw [if_pos h, one_mul]
  · intro k _ hk
    have h : ¬ ((i : ℕ) + (k : ℕ) = g - 1) := by
      intro h
      apply hk
      have := i.2
      apply Fin.ext
      rw [Fin.val_rev]; omega
    rw [if_neg h, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

/- English proof (translation)
Use function extensionality and compare the values at `r`. Rewrite using `[Pi.add_apply]`. Simplify using `only [Matrix.mulVec, dotProduct]`. Rewrite using `[Fin.sum_univ_add]`. Simplify using `only [fullFrame_left, fullFrame_right]`.
-/
theorem fullFrame_mulVec_halves {κ : Type} [Field κ] {g : ℕ} (U : Matrix (Fin (g + g)) (Fin g) κ)
    (J : Matrix (Fin (g + g)) (Fin (g + g)) κ) (Lft : Matrix (Fin g) (Fin (g + g)) κ) (v : Fin (g + g) → κ) :
    fullFrame U J Lft *ᵥ v = U *ᵥ (fun k => v (Fin.castAdd g k)) +
      (J⁻¹ * Lft.transpose * antiDiag κ g) *ᵥ (fun k => v (Fin.natAdd g k)) := by
  funext r
  rw [Pi.add_apply]
  simp only [Matrix.mulVec, dotProduct]
  rw [Fin.sum_univ_add]
  simp only [fullFrame_left, fullFrame_right]

/- English proof (translation)
Introduce `hdet`. Take `⟨v, hv0, hv⟩` from `Matrix.exists_mulVec_eq_zero_iff.2 hdet`. Rewrite `hv` using `[fullFrame_mulVec_halves]`. Use `set a : Fin g → κ := fun k => v (Fin.castAdd g k) with ha`. Use `set b : Fin g → κ := fun k => v (Fin.natAdd g k) with hb`.

Establish `key : U.transpose * J * (J⁻¹ * Lft.transpose * antiDiag κ g) = antiDiag κ g`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_assoc]`. Use `_ = (Lft * U).transpose * antiDiag κ g := by`. Rewrite using `[Matrix.mul_nonsing_inv J hJ, Matrix.mul_one, Matrix.transpose_mul]`.

Use `_ = antiDiag κ g := by rw [hL, Matrix.transpose_one, Matrix.one_mul]`. Establish `h1` using `congrArg (fun w => (U.transpose * J) *ᵥ w) hv`. Simplify using `only [Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.mulVec_zero] at h1`. Rewrite `h1` using `[hU, key, Matrix.zero_mulVec, zero_add]`. Establish `hb0 : b = 0`.

Use function extensionality and compare the values at `k`. Use `congrFun h1 k.rev` as an intermediate fact. Rewrite `this` using `[antiDiag_mulVec_rev, Fin.rev_rev]`. Conclude with `this`. Rewrite `hv` using `[hb0, Matrix.mulVec_zero, add_zero]`.

Establish `ha0 : a = 0`. Establish `h2` using `congrArg (fun w => Lft *ᵥ w) hv`. Simplify using `only [Matrix.mulVec_mulVec, Matrix.mulVec_zero] at h2`. Rewrite `h2` using `[hL, Matrix.one_mulVec]`. Then use the resulting hypothesis. Apply `hv0` to reduce the goal to its premises.

Use function extensionality and compare the values at `c`. Use `Fin.addCases (fun k => ?_) (fun k => ?_) c` and prove the remaining obligations. Conclude with `congrFun ha0 k`. Conclude with `congrFun hb0 k`.
-/
theorem fullFrame_det_ne_zero_field {κ : Type} [Field κ] {g : ℕ} (U : Matrix (Fin (g + g)) (Fin g) κ)
    (Lft : Matrix (Fin g) (Fin (g + g)) κ) (J : Matrix (Fin (g + g)) (Fin (g + g)) κ) (hJ : IsUnit J.det)
    (hL : Lft * U = 1) (hU : U.transpose * J * U = 0) : (fullFrame U J Lft).det ≠ 0 := by
  intro hdet
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
  rw [fullFrame_mulVec_halves] at hv
  set a : Fin g → κ := fun k => v (Fin.castAdd g k) with ha
  set b : Fin g → κ := fun k => v (Fin.natAdd g k) with hb
  have key : U.transpose * J * (J⁻¹ * Lft.transpose * antiDiag κ g) = antiDiag κ g := by
    calc U.transpose * J * (J⁻¹ * Lft.transpose * antiDiag κ g)
        = U.transpose * (J * J⁻¹) * Lft.transpose * antiDiag κ g := by
          simp only [Matrix.mul_assoc]
      _ = (Lft * U).transpose * antiDiag κ g := by
          rw [Matrix.mul_nonsing_inv J hJ, Matrix.mul_one, Matrix.transpose_mul]
      _ = antiDiag κ g := by rw [hL, Matrix.transpose_one, Matrix.one_mul]
  have h1 := congrArg (fun w => (U.transpose * J) *ᵥ w) hv
  simp only [Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.mulVec_zero] at h1
  rw [hU, key, Matrix.zero_mulVec, zero_add] at h1
  have hb0 : b = 0 := by
    funext k
    have := congrFun h1 k.rev
    rw [antiDiag_mulVec_rev, Fin.rev_rev] at this
    exact this
  rw [hb0, Matrix.mulVec_zero, add_zero] at hv
  have ha0 : a = 0 := by
    have h2 := congrArg (fun w => Lft *ᵥ w) hv
    simp only [Matrix.mulVec_mulVec, Matrix.mulVec_zero] at h2
    rwa [hL, Matrix.one_mulVec] at h2
  apply hv0
  funext c
  refine Fin.addCases (fun k => ?_) (fun k => ?_) c
  · exact congrFun ha0 k
  · exact congrFun hb0 k

end GlobalTheory.WholeFlag.Glue
