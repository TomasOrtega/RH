import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousFourierGau
open MeasureTheory Complex Matrix GlobalTheory.RealWeil
open scoped RealInnerProductSpace ContDiff Real ComplexOrder

namespace GlobalTheory.MatrixGaussian

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/- English proof (translation)
Take `⟨B, hB, hBA⟩ : ∃ B : Matrix ι ι ℂ, IsUnit B ∧ A + Aᴴ = star B * B` from `by open scoped MatrixOrder in`. Conclude with `CStarAlgebra.isStrictlyPositive_iff_eq_star_mul_self.1 hA.isStrictlyPositive`. Establish `hBd : IsUnit B.det` using `(Matrix.isUnit_iff_isUnit_det B).1 hB`. Use `set C := B⁻¹ with hC`. Establish `h1 : B * C = 1` using `Matrix.mul_nonsing_inv B hBd`.

Use `set A' := Cᴴ * A * C with hA'`. Establish `h2 : A' + A'ᴴ = 1`. Establish `: A' + A'ᴴ = Cᴴ * (A + Aᴴ) * C`. Simplify using `only [hA', conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]`. Rewrite using `[this, hBA, star_eq_conjTranspose]`.

Combine the equalities or inequalities in the displayed calculation. Simplify using `only [conjTranspose_mul, Matrix.mul_assoc]`. Use `_ = 1 := by rw [h1]; simp`. Establish `hK : (I • (A' - A'ᴴ)).IsHermitian`. Unfold `Matrix.IsHermitian`.

Rewrite using `[conjTranspose_smul, conjTranspose_sub, conjTranspose_conjTranspose]`. Simplify using `only [RCLike.star_def, conj_I, neg_smul, ← smul_neg, neg_sub]`. Use `set U : Matrix ι ι ℂ := (hK.eigenvectorUnitary : Matrix ι ι ℂ) with hU`. Establish `hUU : Uᴴ * U = 1` using `hK.eigenvectorUnitary.2.1`. Establish `hD : Uᴴ * (I • (A' - A'ᴴ)) * U = diagonal (RCLike.ofReal ∘ hK.eigenvalues)`.

Use `hK.conjStarAlgAut_star_eigenvectorUnitary` as an intermediate fact. Simplify `this` using `[Unitary.conjStarAlgAut_apply, star_eq_conjTranspose]`. Establish `h3 : A' = (1 / 2 : ℂ) • (1 - I • (I • (A' - A'ᴴ)))`. Rewrite using `[← h2, smul_smul, I_mul_I]`. Use `module`.

Use `⟨C * U, fun i => (1 / 2 : ℂ) * (1 - I * (hK.eigenvalues i : ℂ)), ?_, fun i => by simp, ?_⟩` and prove the remaining obligations. Rewrite using `[det_mul]`. Use `mul_ne_zero ?_ ?_` and prove the remaining obligations. Introduce `h`. Use `congrArg det h1` as an intermediate fact.

Simplify using `[h] at this`. Introduce `h`. Use `congrArg det hUU` as an intermediate fact. Simplify using `[h] at this`. Combine the equalities or inequalities in the displayed calculation.

Simplify using `only [hA', conjTranspose_mul, Matrix.mul_assoc]`. Use `_ = Uᴴ * ((1 / 2 : ℂ) • (1 - I • (I • (A' - A'ᴴ)))) * U := by rw [← h3]`. Use `_ = (1 / 2 : ℂ) • (Uᴴ * U - I • (Uᴴ * (I • (A' - A'ᴴ)) * U)) := by`. Generalize the expression as in `I • (A' - A'ᴴ) = K`. Simplify using `only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one]`.

Use `_ = _ := by`. Rewrite using `[hD, hUU]`. Use extensionality with `i j`. Distinguish the cases in `h : i = j`. Substitute `h` using the available equality.

Simplify using the standard rewrite rules. Simplify using `[h]`.
-/
theorem exists_congr_diagonal (A : Matrix ι ι ℂ) (hA : (A + Aᴴ).PosDef) :
    ∃ (M : Matrix ι ι ℂ) (d : ι → ℂ), M.det ≠ 0 ∧ (∀ i, 0 < (d i).re) ∧ Mᴴ * A * M = diagonal d := by
  obtain ⟨B, hB, hBA⟩ : ∃ B : Matrix ι ι ℂ, IsUnit B ∧ A + Aᴴ = star B * B := by
    open scoped MatrixOrder in
    exact CStarAlgebra.isStrictlyPositive_iff_eq_star_mul_self.1 hA.isStrictlyPositive
  have hBd : IsUnit B.det := (Matrix.isUnit_iff_isUnit_det B).1 hB
  set C := B⁻¹ with hC
  have h1 : B * C = 1 := Matrix.mul_nonsing_inv B hBd
  set A' := Cᴴ * A * C with hA'
  have h2 : A' + A'ᴴ = 1 := by
    have : A' + A'ᴴ = Cᴴ * (A + Aᴴ) * C := by
      simp only [hA', conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_add, Matrix.add_mul,
        Matrix.mul_assoc]
    rw [this, hBA, star_eq_conjTranspose]
    calc Cᴴ * (Bᴴ * B) * C = (B * C)ᴴ * (B * C) := by
          simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = 1 := by rw [h1]; simp
  have hK : (I • (A' - A'ᴴ)).IsHermitian := by
    unfold Matrix.IsHermitian
    rw [conjTranspose_smul, conjTranspose_sub, conjTranspose_conjTranspose]
    simp only [RCLike.star_def, conj_I, neg_smul, ← smul_neg, neg_sub]
  set U : Matrix ι ι ℂ := (hK.eigenvectorUnitary : Matrix ι ι ℂ) with hU
  have hUU : Uᴴ * U = 1 := hK.eigenvectorUnitary.2.1
  have hD : Uᴴ * (I • (A' - A'ᴴ)) * U = diagonal (RCLike.ofReal ∘ hK.eigenvalues) := by
    have := hK.conjStarAlgAut_star_eigenvectorUnitary
    simpa [Unitary.conjStarAlgAut_apply, star_eq_conjTranspose] using this
  have h3 : A' = (1 / 2 : ℂ) • (1 - I • (I • (A' - A'ᴴ))) := by
    rw [← h2, smul_smul, I_mul_I]
    module
  refine ⟨C * U, fun i => (1 / 2 : ℂ) * (1 - I * (hK.eigenvalues i : ℂ)), ?_, fun i => by simp, ?_⟩
  · rw [det_mul]
    refine mul_ne_zero ?_ ?_
    · intro h
      have := congrArg det h1
      simp [h] at this
    · intro h
      have := congrArg det hUU
      simp [h] at this
  · calc (C * U)ᴴ * A * (C * U) = Uᴴ * A' * U := by
          simp only [hA', conjTranspose_mul, Matrix.mul_assoc]
      _ = Uᴴ * ((1 / 2 : ℂ) • (1 - I • (I • (A' - A'ᴴ)))) * U := by rw [← h3]
      _ = (1 / 2 : ℂ) • (Uᴴ * U - I • (Uᴴ * (I • (A' - A'ᴴ)) * U)) := by
          generalize I • (A' - A'ᴴ) = K
          simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one]
      _ = _ := by
          rw [hD, hUU]
          ext i j
          by_cases h : i = j
          · subst h; simp
          · simp [h]

/- English proof (translation)
Rewrite using `[← Complex.exp_sum, dotProduct, Finset.mul_sum]`. Use `congr 1`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[mulVec_diagonal, ← Complex.conj_mul', Pi.star_apply, RCLike.star_def]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exp_diagonal (d z : ι → ℂ) :
    cexp (-(π : ℂ) * (star z ⬝ᵥ (diagonal d) *ᵥ z)) = ∏ i, cexp (-(π * d i) * (‖z i‖ : ℂ) ^ 2) := by
  rw [← Complex.exp_sum, dotProduct, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mulVec_diagonal, ← Complex.conj_mul', Pi.star_apply, RCLike.star_def]
  ring

/- English proof (translation)
Establish `hb : ∀ i, 0 < ((π : ℂ) * d i).re` using `fun i => by`. Simplify using `using mul_pos Real.pi_pos (hd i)`. Simplify using `only [exp_diagonal]`. Prove the components needed by the constructor for the conclusion. Use `Integrable.fintype_prod (f := fun i (w : ℂ) => cexp (-(π * d i) * (‖w‖ : ℂ) ^ 2)) fun i => ?_` and prove the remaining obligations.

Simplify using `using GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := ℂ) (hb i) 0 0`. Rewrite using `[integral_fintype_prod_volume_eq_prod (fun i (w : ℂ) => cexp (-(π * d i) * (‖w‖ : ℂ) ^ 2)), det_diagonal, ← Finset.prod_inv_distrib]`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[GaussianFourier.integral_cexp_neg_mul_sq_norm (hb i), Complex.finrank_real_complex]`. Establish `hπ : (π : ℂ) ≠ 0` using `by exact_mod_cast Real.pi_ne_zero`.

Establish `: ((2 : ℕ) : ℂ) / 2 = 1` using `by norm_num`. Rewrite using `[this, cpow_one, div_mul_cancel_left₀ hπ]`.
-/
theorem gaussian_diagonal (d : ι → ℂ) (hd : ∀ i, 0 < (d i).re) :
    Integrable (fun z : ι → ℂ => cexp (-(π : ℂ) * (star z ⬝ᵥ (diagonal d) *ᵥ z))) ∧
      ∫ z : ι → ℂ, cexp (-(π : ℂ) * (star z ⬝ᵥ (diagonal d) *ᵥ z)) = (diagonal d).det⁻¹ := by
  have hb : ∀ i, 0 < ((π : ℂ) * d i).re := fun i => by
    simpa using mul_pos Real.pi_pos (hd i)
  simp only [exp_diagonal]
  constructor
  · refine Integrable.fintype_prod (f := fun i (w : ℂ) => cexp (-(π * d i) * (‖w‖ : ℂ) ^ 2)) fun i => ?_
    simpa using GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := ℂ) (hb i) 0 0
  · rw [integral_fintype_prod_volume_eq_prod (fun i (w : ℂ) => cexp (-(π * d i) * (‖w‖ : ℂ) ^ 2)),
      det_diagonal, ← Finset.prod_inv_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [GaussianFourier.integral_cexp_neg_mul_sq_norm (hb i), Complex.finrank_real_complex]
    have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have : ((2 : ℕ) : ℂ) / 2 = 1 := by norm_num
    rw [this, cpow_one, div_mul_cancel_left₀ hπ]

/- English proof (translation)
Establish `hdet : LinearMap.det ((Matrix.toLin' M).restrictScalars ℝ) = normSq M.det`. Rewrite using `[LinearMap.det_restrictScalars, LinearMap.det_toLin', Algebra.norm_complex_apply]`. Use `Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure (ι → ℂ)) (f := (Matrix.toLin' M).restrictScalars ℝ) (by rw [hdet]; simpa using hM)` as an intermediate fact. Rewrite `this` using `[hdet, abs_of_nonneg (inv_nonneg.2 (normSq_nonneg _))]`. Conclude with `this`.
-/
theorem map_mulVec_volume (M : Matrix ι ι ℂ) (hM : M.det ≠ 0) :
    Measure.map (fun z : ι → ℂ => M *ᵥ z) volume = ENNReal.ofReal (normSq M.det)⁻¹ • volume := by
  have hdet : LinearMap.det ((Matrix.toLin' M).restrictScalars ℝ) = normSq M.det := by
    rw [LinearMap.det_restrictScalars, LinearMap.det_toLin', Algebra.norm_complex_apply]
  have := Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure (ι → ℂ))
    (f := (Matrix.toLin' M).restrictScalars ℝ) (by rw [hdet]; simpa using hM)
  rw [hdet, abs_of_nonneg (inv_nonneg.2 (normSq_nonneg _))] at this
  exact this

/- English proof (translation)
Take `⟨M, d, hM, hd, hMA⟩` from `exists_congr_diagonal A hA`. Take `⟨hi, he⟩` from `gaussian_diagonal d hd`. Establish `hn : 0 < normSq M.det` using `normSq_pos.2 hM`. Establish `hdet : (diagonal d).det = (normSq M.det : ℂ) * A.det`. Rewrite using `[← hMA, det_mul, det_mul, det_conjTranspose, normSq_eq_conj_mul_self, RCLike.star_def]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hd0 : (diagonal d).det ≠ 0`. Rewrite using `[det_diagonal]`. Use `Finset.prod_ne_zero_iff.2 fun i _ h => ?_` and prove the remaining obligations. Use `hd i` as an intermediate fact.

Simplify using `[h] at this`. Establish `hA0 : A.det ≠ 0` using `fun h => hd0 (by rw [hdet, h, mul_zero])`. Establish `hcomp : ∀ z : ι → ℂ, star (M *ᵥ z) ⬝ᵥ A *ᵥ (M *ᵥ z) = star z ⬝ᵥ (diagonal d) *ᵥ z` using `fun z => by`. Rewrite using `[← hMA, star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec]`. Establish `hc : Continuous fun z : ι → ℂ => cexp (-(π : ℂ) * (star z ⬝ᵥ A *ᵥ z))` using `by fun_prop`.

Establish `hcM : Continuous fun z : ι → ℂ => M *ᵥ z` using `by fun_prop`. Establish `hmap` using `map_mulVec_volume M hM`. Use `⟨hA0, ?_, ?_⟩` and prove the remaining obligations. Establish `h` using `(integrable_map_measure (μ := volume) hc.aestronglyMeasurable hcM.measurable.aemeasurable).2 (by simpa only [Function.comp_def, hcomp] using hi)`. Rewrite `h` using `[hmap]`.

Conclude with `(integrable_smul_measure (by simpa using hn) ENNReal.ofReal_ne_top).1 h`. Establish `h` using `integral_map (μ := volume) hcM.measurable.aemeasurable hc.aestronglyMeasurable`. Simplify using `only [hcomp] at h`. Rewrite `h` using `[hmap, integral_smul_measure, he, hdet, ENNReal.toReal_ofReal (inv_nonneg.2 hn.le), real_smul, mul_inv, ofReal_inv]`. Conclude with `mul_left_cancel₀ (inv_ne_zero (by exact_mod_cast hn.ne')) h`.
-/
theorem integral_gaussian (ι : Type) [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ) (hA : (A + Aᴴ).PosDef) :
    A.det ≠ 0 ∧ Integrable (fun z : ι → ℂ => cexp (-(π : ℂ) * (star z ⬝ᵥ A *ᵥ z))) ∧
      ∫ z : ι → ℂ, cexp (-(π : ℂ) * (star z ⬝ᵥ A *ᵥ z)) = A.det⁻¹ := by
  obtain ⟨M, d, hM, hd, hMA⟩ := exists_congr_diagonal A hA
  obtain ⟨hi, he⟩ := gaussian_diagonal d hd
  have hn : 0 < normSq M.det := normSq_pos.2 hM
  have hdet : (diagonal d).det = (normSq M.det : ℂ) * A.det := by
    rw [← hMA, det_mul, det_mul, det_conjTranspose, normSq_eq_conj_mul_self, RCLike.star_def]
    ring
  have hd0 : (diagonal d).det ≠ 0 := by
    rw [det_diagonal]
    refine Finset.prod_ne_zero_iff.2 fun i _ h => ?_
    have := hd i
    simp [h] at this
  have hA0 : A.det ≠ 0 := fun h => hd0 (by rw [hdet, h, mul_zero])
  have hcomp : ∀ z : ι → ℂ, star (M *ᵥ z) ⬝ᵥ A *ᵥ (M *ᵥ z) = star z ⬝ᵥ (diagonal d) *ᵥ z := fun z => by
    rw [← hMA, star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec]
  have hc : Continuous fun z : ι → ℂ => cexp (-(π : ℂ) * (star z ⬝ᵥ A *ᵥ z)) := by fun_prop
  have hcM : Continuous fun z : ι → ℂ => M *ᵥ z := by fun_prop
  have hmap := map_mulVec_volume M hM
  refine ⟨hA0, ?_, ?_⟩
  · have h := (integrable_map_measure (μ := volume) hc.aestronglyMeasurable hcM.measurable.aemeasurable).2
      (by simpa only [Function.comp_def, hcomp] using hi)
    rw [hmap] at h
    exact (integrable_smul_measure (by simpa using hn) ENNReal.ofReal_ne_top).1 h
  · have h := integral_map (μ := volume) hcM.measurable.aemeasurable hc.aestronglyMeasurable
    simp only [hcomp] at h
    rw [hmap, integral_smul_measure, he, hdet, ENNReal.toReal_ofReal (inv_nonneg.2 hn.le), real_smul,
      mul_inv, ofReal_inv] at h
    exact mul_left_cancel₀ (inv_ne_zero (by exact_mod_cast hn.ne')) h

end GlobalTheory.MatrixGaussian
