import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeSizeContinuity.LatSizeContOfSteps
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.HermDefON

noncomputable section

open Matrix
open scoped ComplexOrder

namespace PI.UnitaryGroupMassFormula.LSC.DeterminantMonotonicity

/- English proof (translation)
Unfold `nsq dotProduct`. Use `push_cast`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Simplify using `[Complex.conj_mul']`.
-/
lemma star_dot_self {n : ℕ} (w : Fin n → ℂ) : star w ⬝ᵥ w = ((nsq w : ℝ) : ℂ) := by
  unfold nsq dotProduct
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [Complex.conj_mul']

/- English proof (translation)
Rewrite using `[← mulVec_mulVec, dotProduct_mulVec, ← star_mulVec, star_dot_self]`.
-/
lemma quad {n j : ℕ} (C : Matrix (Fin n) (Fin j) ℂ) (z : Fin j → ℂ) :
    star z ⬝ᵥ ((Cᴴ * C) *ᵥ z) = ((nsq (C *ᵥ z) : ℝ) : ℂ) := by
  rw [← mulVec_mulVec, dotProduct_mulVec, ← star_mulVec, star_dot_self]

/- English proof (translation)
Rewrite using `[← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, ← star_mulVec]`.
-/
lemma sandwich {j : ℕ} (y X : Matrix (Fin j) (Fin j) ℂ) (v : Fin j → ℂ) :
    star v ⬝ᵥ ((yᴴ * X * y) *ᵥ v) = star (y *ᵥ v) ⬝ᵥ (X *ᵥ (y *ᵥ v)) := by
  rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, ← star_mulVec]

/- English proof (translation)
The claim follows from `Finset.sum_nonneg fun _ _ => by positivity`.
-/
lemma nsq_nonneg {n : ℕ} (w : Fin n → ℂ) : 0 ≤ nsq w :=
  Finset.sum_nonneg fun _ _ => by positivity

end PI.UnitaryGroupMassFormula.LSC.DeterminantMonotonicity

namespace PI.UnitaryGroupMassFormula.LSC

open DeterminantMonotonicity in
/- English proof (translation)
Introduce `n j C M κ hκ hM`. Establish `hB : (Cᴴ * C).PosSemidef` using `posSemidef_conjTranspose_mul_self C`. Establish `hA : ((M * C)ᴴ * (M * C)).PosSemidef` using `posSemidef_conjTranspose_mul_self (M * C)`. Establish `hBre : 0 ≤ ((Cᴴ * C).det).re`. Simplify using `using (Complex.le_def.mp hB.det_nonneg).1`.

Use `⟨hBre, ?_⟩` and prove the remaining obligations. Establish `hqA : ∀ z : Fin j → ℂ, star z ⬝ᵥ (((M * C)ᴴ * (M * C)) *ᵥ z) = ((nsq (M *ᵥ (C *ᵥ z)) : ℝ) : ℂ)`. Introduce `z`. Rewrite using `[quad, mulVec_mulVec]`. Distinguish the cases in `h0 : (Cᴴ * C).det = 0`.

Take `⟨z, hz, hBz⟩` from `exists_mulVec_eq_zero_iff.mpr h0`. Establish `h1 : nsq (C *ᵥ z) = 0`. Use `quad C z` as an intermediate fact. Rewrite `this` using `[hBz, dotProduct_zero]`. Conclude with `this.symm` after adjusting the coercions.

Establish `h2 : nsq (M *ᵥ (C *ᵥ z)) = 0` using `le_antisymm (by simpa [h1] using hM (C *ᵥ z)) (nsq_nonneg _)`. Establish `h3 : ((M * C)ᴴ * (M * C)) *ᵥ z = 0`. Rewrite using `[← hA.dotProduct_mulVec_zero_iff, hqA, h2]`. Simplify using the standard rewrite rules. Establish `h4 : ((M * C)ᴴ * (M * C)).det = 0` using `exists_mulVec_eq_zero_iff.mp ⟨z, hz, h3⟩`.

Rewrite using `[h4, h0]`. Simplify using the standard rewrite rules. Establish `hPD : (Cᴴ * C).PosDef` using `hB.posDef_iff_det_ne_zero.mpr h0`. Take `⟨y, hy, hyB⟩` from `posDefCongruentOne j _ hPD`. Establish `hN : (yᴴ * ((M * C)ᴴ * (M * C)) * y).PosSemidef` using `hA.conjTranspose_mul_mul_same y`.

Establish `hev : ∀ i, hN.1.eigenvalues i ≤ κ`. Introduce `i`. Establish `hv1 : star (⇑(hN.1.eigenvectorBasis i) : Fin j → ℂ) ⬝ᵥ ⇑(hN.1.eigenvectorBasis i) = 1`. Rewrite using `[dotProduct_comm]`. Simplify using `only [← EuclideanSpace.inner_eq_star_dotProduct, inner_self_eq_norm_sq_to_K, hN.1.eigenvectorBasis.orthonormal.1 i]`.

Simplify using the standard rewrite rules. Establish `hBv : star (⇑(hN.1.eigenvectorBasis i) : Fin j → ℂ) ⬝ᵥ ((yᴴ * (Cᴴ * C) * y) *ᵥ ⇑(hN.1.eigenvectorBasis i)) = 1`. Rewrite using `[hyB, one_mulVec, hv1]`. Rewrite `hBv` using `[sandwich, quad]`. Establish `hn1 : nsq (C *ᵥ (y *ᵥ ⇑(hN.1.eigenvectorBasis i))) = 1` using `by exact_mod_cast hBv`.

Rewrite using `[hN.1.eigenvalues_eq, sandwich, hqA]`. Use `hM (C *ᵥ (y *ᵥ ⇑(hN.1.eigenvectorBasis i)))` as an intermediate fact. Rewrite `this` using `[hn1, mul_one]`. Simplify using `using this`. Establish `hdetN : (yᴴ * ((M * C)ᴴ * (M * C)) * y).det = ((∏ i, hN.1.eigenvalues i : ℝ) : ℂ)`.

Rewrite using `[hN.1.det_eq_prod_eigenvalues]`. Use `push_cast`. Both sides reduce to the same expression. Establish `hP : ∏ i, hN.1.eigenvalues i ≤ κ ^ j`. Combine the equalities or inequalities in the displayed calculation.

Establish `hd0 : y.det ≠ 0` using `hy.ne_zero`. Establish `hnd : 0 < Complex.normSq y.det` using `Complex.normSq_pos.mpr hd0`. Establish `e1 : ((Complex.normSq y.det : ℝ) : ℂ) * ((M * C)ᴴ * (M * C)).det = ((∏ i, hN.1.eigenvalues i : ℝ) : ℂ)`. Rewrite using `[← hdetN, det_mul, det_mul, det_conjTranspose, Complex.normSq_eq_conj_mul_self]`. Simplify using `only [Complex.star_def]`.

Expand and normalize the polynomial expressions, which then agree. Establish `e2 : ((Complex.normSq y.det : ℝ) : ℂ) * (Cᴴ * C).det = 1`. Use `congrArg Matrix.det hyB` as an intermediate fact. Rewrite `this` using `[det_mul, det_mul, det_conjTranspose, det_one]`. Rewrite using `[Complex.normSq_eq_conj_mul_self, ← this]`.

Simplify using `only [Complex.star_def]`. Expand and normalize the polynomial expressions, which then agree. Establish `r1` using `congrArg Complex.re e1`. Establish `r2` using `congrArg Complex.re e2`. Rewrite `r1` using `[Complex.re_ofReal_mul, Complex.ofReal_re]`.

Rewrite `r2` using `[Complex.re_ofReal_mul, Complex.one_re]`. Use `le_of_mul_le_mul_left ?_ hnd` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.
-/
theorem determinant_monotone : DetMono := by
  intro n j C M κ hκ hM
  classical
  have hB : (Cᴴ * C).PosSemidef := posSemidef_conjTranspose_mul_self C
  have hA : ((M * C)ᴴ * (M * C)).PosSemidef := posSemidef_conjTranspose_mul_self (M * C)
  have hBre : 0 ≤ ((Cᴴ * C).det).re := by
    simpa using (Complex.le_def.mp hB.det_nonneg).1
  refine ⟨hBre, ?_⟩
  have hqA : ∀ z : Fin j → ℂ, star z ⬝ᵥ (((M * C)ᴴ * (M * C)) *ᵥ z) = ((nsq (M *ᵥ (C *ᵥ z)) : ℝ) : ℂ) := by
    intro z; rw [quad, mulVec_mulVec]
  by_cases h0 : (Cᴴ * C).det = 0
  · obtain ⟨z, hz, hBz⟩ := exists_mulVec_eq_zero_iff.mpr h0
    have h1 : nsq (C *ᵥ z) = 0 := by
      have := quad C z
      rw [hBz, dotProduct_zero] at this
      exact_mod_cast this.symm
    have h2 : nsq (M *ᵥ (C *ᵥ z)) = 0 :=
      le_antisymm (by simpa [h1] using hM (C *ᵥ z)) (nsq_nonneg _)
    have h3 : ((M * C)ᴴ * (M * C)) *ᵥ z = 0 := by
      rw [← hA.dotProduct_mulVec_zero_iff, hqA, h2]; simp
    have h4 : ((M * C)ᴴ * (M * C)).det = 0 := exists_mulVec_eq_zero_iff.mp ⟨z, hz, h3⟩
    rw [h4, h0]; simp
  · have hPD : (Cᴴ * C).PosDef := hB.posDef_iff_det_ne_zero.mpr h0
    obtain ⟨y, hy, hyB⟩ := posDefCongruentOne j _ hPD
    have hN : (yᴴ * ((M * C)ᴴ * (M * C)) * y).PosSemidef := hA.conjTranspose_mul_mul_same y
    have hev : ∀ i, hN.1.eigenvalues i ≤ κ := by
      intro i
      have hv1 : star (⇑(hN.1.eigenvectorBasis i) : Fin j → ℂ) ⬝ᵥ ⇑(hN.1.eigenvectorBasis i) = 1 := by
        rw [dotProduct_comm]
        simp only [← EuclideanSpace.inner_eq_star_dotProduct, inner_self_eq_norm_sq_to_K,
          hN.1.eigenvectorBasis.orthonormal.1 i]
        simp
      have hBv : star (⇑(hN.1.eigenvectorBasis i) : Fin j → ℂ) ⬝ᵥ
          ((yᴴ * (Cᴴ * C) * y) *ᵥ ⇑(hN.1.eigenvectorBasis i)) = 1 := by
        rw [hyB, one_mulVec, hv1]
      rw [sandwich, quad] at hBv
      have hn1 : nsq (C *ᵥ (y *ᵥ ⇑(hN.1.eigenvectorBasis i))) = 1 := by exact_mod_cast hBv
      rw [hN.1.eigenvalues_eq, sandwich, hqA]
      have := hM (C *ᵥ (y *ᵥ ⇑(hN.1.eigenvectorBasis i)))
      rw [hn1, mul_one] at this
      simpa using this
    have hdetN : (yᴴ * ((M * C)ᴴ * (M * C)) * y).det = ((∏ i, hN.1.eigenvalues i : ℝ) : ℂ) := by
      rw [hN.1.det_eq_prod_eigenvalues]; push_cast; rfl
    have hP : ∏ i, hN.1.eigenvalues i ≤ κ ^ j := by
      calc ∏ i, hN.1.eigenvalues i ≤ ∏ _i : Fin j, κ :=
            Finset.prod_le_prod (fun i _ => hN.eigenvalues_nonneg i) (fun i _ => hev i)
        _ = κ ^ j := by simp
    have hd0 : y.det ≠ 0 := hy.ne_zero
    have hnd : 0 < Complex.normSq y.det := Complex.normSq_pos.mpr hd0
    have e1 : ((Complex.normSq y.det : ℝ) : ℂ) * ((M * C)ᴴ * (M * C)).det
        = ((∏ i, hN.1.eigenvalues i : ℝ) : ℂ) := by
      rw [← hdetN, det_mul, det_mul, det_conjTranspose, Complex.normSq_eq_conj_mul_self]
      simp only [Complex.star_def]; ring
    have e2 : ((Complex.normSq y.det : ℝ) : ℂ) * (Cᴴ * C).det = 1 := by
      have := congrArg Matrix.det hyB
      rw [det_mul, det_mul, det_conjTranspose, det_one] at this
      rw [Complex.normSq_eq_conj_mul_self, ← this]
      simp only [Complex.star_def]; ring
    have r1 := congrArg Complex.re e1
    have r2 := congrArg Complex.re e2
    rw [Complex.re_ofReal_mul, Complex.ofReal_re] at r1
    rw [Complex.re_ofReal_mul, Complex.one_re] at r2
    refine le_of_mul_le_mul_left ?_ hnd
    calc Complex.normSq y.det * (((M * C)ᴴ * (M * C)).det).re = ∏ i, hN.1.eigenvalues i := r1
      _ ≤ κ ^ j := hP
      _ = κ ^ j * (Complex.normSq y.det * ((Cᴴ * C).det).re) := by rw [r2, mul_one]
      _ = Complex.normSq y.det * (κ ^ j * ((Cᴴ * C).det).re) := by ring

end PI.UnitaryGroupMassFormula.LSC
