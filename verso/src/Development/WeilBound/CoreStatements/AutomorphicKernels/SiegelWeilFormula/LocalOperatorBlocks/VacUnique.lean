import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalOperatorBlocks.ContinuousWeightFactorUnitary
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalOperatorBlocks.GaussSec

noncomputable section

open scoped Matrix
open MeasureTheory PositivityTheory.Rg.Sw PositivityTheory.SiegelWeilFormula

namespace PositivityTheory.SiegelWeilFormula.KLI

variable {m n : ℕ}

/- English proof (translation)
Simplify using `[Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, Matrix.mulVec_mulVec, Matrix.star_eq_conjTranspose, Matrix.mul_assoc]`.
-/
private theorem star_mulVec_dotProduct_mulVec_conj (U M : Matrix (Fin n) (Fin n) ℂ) (y : Fin n → ℂ) :
    star (U *ᵥ y) ⬝ᵥ (M *ᵥ (U *ᵥ y)) = star y ⬝ᵥ ((star U * M * U) *ᵥ y) := by
  simp [Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, Matrix.mulVec_mulVec,
    Matrix.star_eq_conjTranspose, Matrix.mul_assoc]

/- English proof (translation)
Establish `hn : Complex.normSq U.det = 1`. Establish `h` using `Matrix.det_of_mem_unitary hU`. Establish `h2 : star U.det * U.det = 1` using `Unitary.star_mul_self_of_mem h`. Establish `h3 : ((Complex.normSq U.det : ℝ) : ℂ) = 1`. Rewrite using `[Complex.normSq_eq_conj_mul_self]`.

Conclude with `h2`. Conclude with `h3` after adjusting the coercions. Establish `hsU : star U * U = 1` using `Matrix.mem_unitaryGroup_iff'.mp hU`. Establish `hUs : U * star U = 1` using `Matrix.mem_unitaryGroup_iff.mp hU`. Set `e : (Fin n → ℂ) ≃ᵐ (Fin n → ℂ)` to `{ toFun := fun y => U *ᵥ y invFun := fun v => star U *ᵥ v left_inv := fun y => by simp [Matrix.mulVec_mulVec, hsU] right_inv := fun v => by simp [Matrix.mulVec_mulVec, hUs] measurable_toFun := (Continuous.matrix_mulVec continuous_const continuous_id).measurable measurable_invFun …`.

Set `L : (Fin n → ℂ) →ₗ[ℝ] (Fin n → ℂ)` to `(Matrix.toLin' U).restrictScalars ℝ`. Establish `hdet : LinearMap.det L = 1`. Simplify using `only [L]`. Rewrite using `[LinearMap.det_restrictScalars, LinearMap.det_toLin', Algebra.norm_complex_apply, hn]`. Establish `hmap : MeasureTheory.Measure.map (⇑e) MeasureTheory.volume = MeasureTheory.volume`.

Establish `he : (⇑e) = ⇑L`. Use function extensionality and compare the values at `y`. Both sides reduce to the same expression. Rewrite using `[he, MeasureTheory.Measure.map_linearMap_addHaar_eq_smul_addHaar _ (by rw [hdet]; exact one_ne_zero), hdet]`. Simplify using the standard rewrite rules.

Establish `h` using `MeasureTheory.integral_map_equiv (μ := MeasureTheory.volume) e f`. Rewrite `h` using `[hmap]`. Conclude with `h.symm`.
-/
private theorem integral_comp_unitary_mulVec (U : Matrix (Fin n) (Fin n) ℂ) (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ)
    (f : (Fin n → ℂ) → ℂ) : ∫ y, f (U *ᵥ y) = ∫ v, f v := by
  have hn : Complex.normSq U.det = 1 := by
    have h := Matrix.det_of_mem_unitary hU
    have h2 : star U.det * U.det = 1 := Unitary.star_mul_self_of_mem h
    have h3 : ((Complex.normSq U.det : ℝ) : ℂ) = 1 := by
      rw [Complex.normSq_eq_conj_mul_self]
      exact h2
    exact_mod_cast h3
  have hsU : star U * U = 1 := Matrix.mem_unitaryGroup_iff'.mp hU
  have hUs : U * star U = 1 := Matrix.mem_unitaryGroup_iff.mp hU
  let e : (Fin n → ℂ) ≃ᵐ (Fin n → ℂ) :=
    { toFun := fun y => U *ᵥ y
      invFun := fun v => star U *ᵥ v
      left_inv := fun y => by simp [Matrix.mulVec_mulVec, hsU]
      right_inv := fun v => by simp [Matrix.mulVec_mulVec, hUs]
      measurable_toFun := (Continuous.matrix_mulVec continuous_const continuous_id).measurable
      measurable_invFun := (Continuous.matrix_mulVec continuous_const continuous_id).measurable }
  let L : (Fin n → ℂ) →ₗ[ℝ] (Fin n → ℂ) := (Matrix.toLin' U).restrictScalars ℝ
  have hdet : LinearMap.det L = 1 := by
    simp only [L]
    rw [LinearMap.det_restrictScalars, LinearMap.det_toLin', Algebra.norm_complex_apply, hn]
  have hmap : MeasureTheory.Measure.map (⇑e) MeasureTheory.volume = MeasureTheory.volume := by
    have he : (⇑e) = ⇑L := by
      funext y
      rfl
    rw [he, MeasureTheory.Measure.map_linearMap_addHaar_eq_smul_addHaar _
      (by rw [hdet]; exact one_ne_zero), hdet]
    simp
  have h := MeasureTheory.integral_map_equiv (μ := MeasureTheory.volume) e f
  rw [hmap] at h
  exact h.symm

/- English proof (translation)
Simplify using `only [Matrix.mulVec_diagonal, dotProduct, Pi.star_apply]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self]`. Simplify using `only [RCLike.star_def]`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem star_dotProduct_diagonal_mulVec_eq_sum (d y : Fin n → ℂ) :
    star y ⬝ᵥ (Matrix.diagonal d *ᵥ y) = ∑ k, d k * ((‖y k‖ ^ 2 : ℝ) : ℂ) := by
  simp only [Matrix.mulVec_diagonal, dotProduct, Pi.star_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self]
  simp only [RCLike.star_def]
  ring

/- English proof (translation)
Repeatedly rewrite using `[Complex.exp_sum]`. Rewrite using `[integral_fintype_prod_volume_eq_prod (f := fun k (z : ℂ) => Complex.exp (d k * ((‖z‖ ^ 2 : ℝ) : ℂ)))]`. Use `Finset.prod_congr rfl fun k _ => ?_` and prove the remaining obligations. Establish `hf : (fun z : ℂ => Complex.exp (d k * ((‖z‖ ^ 2 : ℝ) : ℂ))) = fun z : ℂ => Complex.exp (-(-d k) * (‖z‖ : ℂ) ^ 2)`. Use function extensionality and compare the values at `z`.

Use `push_cast`. Put the polynomial expressions in normal form. Rewrite using `[hf, GaussianFourier.integral_cexp_neg_mul_sq_norm (hd k)]`. Simplify using the standard rewrite rules.
-/
private theorem integral_cexp_diagonal_eq_prod_pi_div (d : Fin n → ℂ) (hd : ∀ k, 0 < (-d k).re) :
    ∫ y : Fin n → ℂ, Complex.exp (∑ k, d k * ((‖y k‖ ^ 2 : ℝ) : ℂ)) = ∏ k, (Real.pi : ℂ) / (-d k) := by
  simp_rw [Complex.exp_sum]
  rw [integral_fintype_prod_volume_eq_prod
    (f := fun k (z : ℂ) => Complex.exp (d k * ((‖z‖ ^ 2 : ℝ) : ℂ)))]
  refine Finset.prod_congr rfl fun k _ => ?_
  have hf : (fun z : ℂ => Complex.exp (d k * ((‖z‖ ^ 2 : ℝ) : ℂ))) =
      fun z : ℂ => Complex.exp (-(-d k) * (‖z‖ : ℂ) ^ 2) := by
    funext z
    push_cast
    ring_nf
  rw [hf, GaussianFourier.integral_cexp_neg_mul_sq_norm (hd k)]
  simp

/- English proof (translation)
Rewrite using `[← integral_comp_unitary_mulVec U hU]`. Simplify using `only [star_mulVec_dotProduct_mulVec_conj, hM, star_dotProduct_diagonal_mulVec_eq_sum]`. Rewrite using `[integral_cexp_diagonal_eq_prod_pi_div d hd]`. Establish `hsU : star U * U = 1` using `Matrix.mem_unitaryGroup_iff'.mp hU`. Establish `hdet : (-M).det = ∏ k, (-d k)`.

Establish `h1 : (star U * (-M) * U).det = (-M).det`. Rewrite using `[Matrix.det_mul, Matrix.det_mul, mul_comm (star U).det, mul_assoc, ← Matrix.det_mul, hsU, Matrix.det_one, mul_one]`. Establish `h2 : -Matrix.diagonal d = Matrix.diagonal (fun k => -d k)`. Use extensionality with `i j`. Distinguish the cases in `hij : i = j`.

Substitute `hij` using the available equality. Simplify using the standard rewrite rules. Simplify using `[Matrix.diagonal_apply_ne _ hij]`. Rewrite using `[← h1, Matrix.mul_neg, Matrix.neg_mul, hM, h2, Matrix.det_diagonal]`. Rewrite using `[hdet, ← Finset.prod_mul_distrib]`.

Rewrite using `[Finset.prod_congr rfl fun k _ => div_mul_cancel₀ (Real.pi : ℂ) (fun h => by`. Use `hd k` as an intermediate fact. Rewrite `this` using `[h]`. Simplify using `at this)]`. Simplify using the standard rewrite rules.
-/
private theorem integral_cexp_quadratic_mul_det_neg_eq_pi_pow (M U : Matrix (Fin n) (Fin n) ℂ) (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ)
    (d : Fin n → ℂ) (hd : ∀ k, 0 < (-d k).re) (hM : star U * M * U = Matrix.diagonal d) :
    (∫ v : Fin n → ℂ, Complex.exp (star v ⬝ᵥ (M *ᵥ v))) * (-M).det = (Real.pi : ℂ) ^ n := by
  rw [← integral_comp_unitary_mulVec U hU]
  simp only [star_mulVec_dotProduct_mulVec_conj, hM, star_dotProduct_diagonal_mulVec_eq_sum]
  rw [integral_cexp_diagonal_eq_prod_pi_div d hd]
  have hsU : star U * U = 1 := Matrix.mem_unitaryGroup_iff'.mp hU
  have hdet : (-M).det = ∏ k, (-d k) := by
    have h1 : (star U * (-M) * U).det = (-M).det := by
      rw [Matrix.det_mul, Matrix.det_mul, mul_comm (star U).det, mul_assoc, ← Matrix.det_mul, hsU,
        Matrix.det_one, mul_one]
    have h2 : -Matrix.diagonal d = Matrix.diagonal (fun k => -d k) := by
      ext i j
      by_cases hij : i = j
      · subst hij
        simp
      · simp [Matrix.diagonal_apply_ne _ hij]
    rw [← h1, Matrix.mul_neg, Matrix.neg_mul, hM, h2, Matrix.det_diagonal]
  rw [hdet, ← Finset.prod_mul_distrib]
  rw [Finset.prod_congr rfl fun k _ => div_mul_cancel₀ (Real.pi : ℂ) (fun h => by
    have := hd k
    rw [h] at this
    simp at this)]
  simp

/- English proof (translation)
Establish `hn : ∀ z : ℂ, (‖z‖ : ℂ) ^ 2 = star z * z`. Introduce `z`. Use `Complex.normSq_eq_norm_sq z` as an intermediate fact. Rewrite using `[← Complex.ofReal_pow, ← this, Complex.normSq_eq_conj_mul_self]`. Both sides reduce to the same expression.

Rewrite using `[← Complex.exp_sum]`. Simplify using `only [evX, map_one, one_mul, gs]`. Rewrite using `[← Complex.exp_add]`. Use `congr 1`. Simplify using `only [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_add, dotProduct_smul, Finset.sum_add_distrib, Matrix.trace, Matrix.diag, Matrix.mul_apply, gramX_tr_g, dotProduct, Matrix.mulVec, Matrix.transpose_apply, Pi.star_apply, smul_eq_mul, Pi.smul_apply]`.

Use `push_cast`. Simplify using `only [hn, Finset.mul_sum, Finset.sum_neg_distrib, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.transpose_apply, smul_eq_mul, mul_add, add_mul, Finset.sum_add_distrib, ite_mul, mul_ite, zero_mul, mul_zero, mul_one, one_mul, Finset.sum_ite_eq, Finset.mem_univ, if_t …`. Use `congr 1`. Rewrite using `[← Finset.sum_neg_distrib]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations.

Rewrite using `[← Finset.sum_neg_distrib]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Use `conv_lhs => enter [2, y]`. Rewrite using `[Finset.sum_comm]`.

Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem evX_one_mul_gs_mul_cexp_eq_prod (b : Matrix (Fin n) (Fin n) ℂ) (c t : ℝ) (x : Fin m → Fin n → ℂ) :
    evX (1 : PX m n) x * gs c x * Complex.exp (Complex.I * ↑t * (b * gramX (fun _ : Fin m => true) x).trace)
      = ∏ a, Complex.exp (star (x a) ⬝ᵥ
          ((-(c : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) + (Complex.I * (t : ℂ)) • bᵀ) *ᵥ x a)) := by
  have hn : ∀ z : ℂ, (‖z‖ : ℂ) ^ 2 = star z * z := by
    intro z
    have := Complex.normSq_eq_norm_sq z
    rw [← Complex.ofReal_pow, ← this, Complex.normSq_eq_conj_mul_self]
    rfl
  rw [← Complex.exp_sum]
  simp only [evX, map_one, one_mul, gs]
  rw [← Complex.exp_add]
  congr 1
  simp only [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_add, dotProduct_smul,
    Finset.sum_add_distrib, Matrix.trace, Matrix.diag, Matrix.mul_apply, gramX_tr_g, dotProduct, Matrix.mulVec,
    Matrix.transpose_apply, Pi.star_apply, smul_eq_mul, Pi.smul_apply]
  push_cast
  simp only [hn, Finset.mul_sum, Finset.sum_neg_distrib, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply,
    Matrix.transpose_apply, smul_eq_mul, mul_add, add_mul, Finset.sum_add_distrib, ite_mul, mul_ite, zero_mul,
    mul_zero, mul_one, one_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  congr 1
  · rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  · conv_lhs => enter [2, y]; rw [Finset.sum_comm]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
    ring

/- English proof (translation)
Establish `hmR : mR (jG n * nG b) = Matrix.fromBlocks 0 1 (-1) (-b)`. Rewrite using `[mR_mul, mR_jG, mR_nG hb]`. Simplify using `[JJ, nU, Matrix.fromBlocks_multiply]`. Establish `hD : (mR (jG n * nG b)).det = (JJ n).det`. Rewrite using `[mR_mul, mR_jG, mR_nG hb, Matrix.det_mul]`.

Simplify using `[nU, Matrix.det_fromBlocks_zero₂₁]`. Simplify using `only [F0, f0, u1, u2]`. Rewrite using `[hD, hmR]`. Simplify using `only [Matrix.toBlocks_fromBlocks₂₁, Matrix.toBlocks_fromBlocks₂₂]`. Break down `Int.units_eq_one_or sg with rfl | rfl` into its components or cases.

Simplify using `only [pOf, qOf, if_true]`. Establish `hM : Complex.I • (-1 : Matrix (Fin n) (Fin n) ℂ) + -b = (-(Complex.I * (((1 : ℤˣ) : ℤ) : ℂ))) • (1 - (Complex.I * (((1 : ℤˣ) : ℤ) : ℂ)) • b)`. Use extensionality with `i j`. Simplify using `[Matrix.one_apply]`. Apply the tactic sequence `split_ifs <;> ring_nf <;> simp [Complex.I_sq] <;> ring`.

Rewrite using `[hM, Matrix.det_smul, Fintype.card_fin]`. Simplify using the standard rewrite rules. Simplify using `only [pOf, qOf]`. Establish `hne : (-1 : ℤˣ) ≠ 1` using `by decide`. Simplify using `only [hne, if_false]`.

Establish `hM : -(Complex.I • (-1 : Matrix (Fin n) (Fin n) ℂ)) + -b = (-(Complex.I * (((-1 : ℤˣ) : ℤ) : ℂ))) • (1 - (Complex.I * (((-1 : ℤˣ) : ℤ) : ℂ)) • b)`. Use extensionality with `i j`. Simplify using `[Matrix.one_apply]`. Apply the tactic sequence `split_ifs <;> ring_nf <;> simp [Complex.I_sq] <;> ring`. Rewrite using `[hM, Matrix.det_smul, Fintype.card_fin]`.

Simplify using the standard rewrite rules.
-/
private theorem F0_jG_mul_nG_eq (sg : ℤˣ) (e : ℤ) (b : Matrix (Fin n) (Fin n) ℂ) (hb : bᴴ = b) :
    F0 (pOf sg m) (qOf sg m) e (jG n * nG b) =
      (JJ n).det ^ e * ((-(Complex.I * ((sg : ℤ) : ℂ))) ^ n *
        (1 - (Complex.I * ((sg : ℤ) : ℂ)) • b).det) ^ (-(m : ℤ)) := by
  have hmR : mR (jG n * nG b) = Matrix.fromBlocks 0 1 (-1) (-b) := by
    rw [mR_mul, mR_jG, mR_nG hb]
    simp [JJ, nU, Matrix.fromBlocks_multiply]
  have hD : (mR (jG n * nG b)).det = (JJ n).det := by
    rw [mR_mul, mR_jG, mR_nG hb, Matrix.det_mul]
    simp [nU, Matrix.det_fromBlocks_zero₂₁]
  simp only [F0, f0, u1, u2]
  rw [hD, hmR]
  simp only [Matrix.toBlocks_fromBlocks₂₁, Matrix.toBlocks_fromBlocks₂₂]
  rcases Int.units_eq_one_or sg with rfl | rfl
  · simp only [pOf, qOf, if_true]
    have hM : Complex.I • (-1 : Matrix (Fin n) (Fin n) ℂ) + -b =
        (-(Complex.I * (((1 : ℤˣ) : ℤ) : ℂ))) • (1 - (Complex.I * (((1 : ℤˣ) : ℤ) : ℂ)) • b) := by
      ext i j
      simp [Matrix.one_apply]
      split_ifs <;> ring_nf <;> simp [Complex.I_sq] <;> ring
    rw [hM, Matrix.det_smul, Fintype.card_fin]
    simp
  · simp only [pOf, qOf]
    have hne : (-1 : ℤˣ) ≠ 1 := by decide
    simp only [hne, if_false]
    have hM : -(Complex.I • (-1 : Matrix (Fin n) (Fin n) ℂ)) + -b =
        (-(Complex.I * (((-1 : ℤˣ) : ℤ) : ℂ))) • (1 - (Complex.I * (((-1 : ℤˣ) : ℤ) : ℂ)) • b) := by
      ext i j
      simp [Matrix.one_apply]
      split_ifs <;> ring_nf <;> simp [Complex.I_sq] <;> ring
    rw [hM, Matrix.det_smul, Fintype.card_fin]
    simp

/- English proof (translation)
Establish `hs : ((sg : ℤ) : ℂ) = 1 ∨ ((sg : ℤ) : ℂ) = -1`. Apply the tactic sequence `rcases Int.units_eq_one_or sg with h | h <;> simp [h]`. Establish `hIs : Complex.I * ((sg : ℤ) : ℂ) ≠ 0`. Apply the tactic sequence `rcases hs with h | h <;> simp [h, Complex.I_ne_zero]`. Establish `hpi : (Real.pi : ℂ) ≠ 0` using `by exact_mod_cast Real.pi_ne_zero`.

Establish `h2 : (((2 * Real.pi : ℝ)) : ℂ) ≠ 0`. Use `push_cast`. Conclude with `mul_ne_zero two_ne_zero hpi`. Use `⟨(JJ n).det ^ e * ((-(Complex.I * ((sg : ℤ) : ℂ))) ^ n) ^ (-(m : ℤ)) * ((((2 * Real.pi : ℝ)) : ℂ) ^ n / (Real.pi : ℂ) ^ n) ^ m, ?_, ?_⟩` and prove the remaining obligations. Conclude with `mul_ne_zero (mul_ne_zero (zpow_ne_zero _ JJ_det_ne) (zpow_ne_zero _ (pow_ne_zero _ (neg_ne_zero.mpr hIs)))) (pow_ne_zero _ (div_ne_zero (pow_ne_zero _ h2) (pow_ne_zero _ hpi)))`.

Introduce `b hb`. Establish `hA : bᵀ.IsHermitian` using `(show b.IsHermitian from hb).transpose`. Establish `hU : (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) ∈ Matrix.unitaryGroup (Fin n) ℂ` using `hA.eigenvectorUnitary.2`. Establish `hsU : star (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) * (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) = 1` using `Matrix.mem_unitaryGroup_iff'.mp hU`. Establish `hspec : star (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) * bᵀ * (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) = Matrix.diagonal (Complex.ofReal ∘ hA.eigenvalues)`.

Use `hA.conjStarAlgAut_star_eigenvectorUnitary` as an intermediate fact. Simplify `this` using `[Unitary.conjStarAlgAut_apply, mul_assoc]`. Establish `hMd : star (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) * (-(((2 * Real.pi : ℝ)) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) + (Complex.I * (((2 * Real.pi * ((sg : ℤ) : ℝ)) : ℝ) : ℂ)) • bᵀ) * (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) = Matrix.diagonal (fun k => -(((2 * R …`. Establish `e1 : star (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) * (-(((2 * Real.pi : ℝ)) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) + (Complex.I * (((2 * Real.pi * ((sg : ℤ) : ℝ)) : ℝ) : ℂ)) • bᵀ) * (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) = -(((2 * Real.pi : ℝ)) : ℂ) • (star ( …`. Simplify using `only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]`.

Rewrite using `[e1, hsU, hspec]`. Use extensionality with `i j`. Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Simplify using the standard rewrite rules.

Simplify using `[Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij]`. Establish `hd : ∀ k, 0 < (-(-(((2 * Real.pi : ℝ)) : ℂ) + Complex.I * (((2 * Real.pi * ((sg : ℤ) : ℝ)) : ℝ) : ℂ) * (hA.eigenvalues k : ℂ))).re`. Introduce `k`. Simplify using `[Complex.mul_re]`. Conclude with `Real.pi_pos`.

Establish `hJ` using `integral_cexp_quadratic_mul_det_neg_eq_pi_pow _ _ hU _ hd hMd`. Establish `hnegM : -(-(((2 * Real.pi : ℝ)) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) + (Complex.I * (((2 * Real.pi * ((sg : ℤ) : ℝ)) : ℝ) : ℂ)) • bᵀ) = (((2 * Real.pi : ℝ)) : ℂ) • (1 - (Complex.I * ((sg : ℤ) : ℂ)) • b)ᵀ`. Use extensionality with `i j`. Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality.

Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree. Simplify using `[Matrix.one_apply_ne hij]`. Expand and normalize the polynomial expressions, which then agree. Rewrite `hJ` using `[hnegM, Matrix.det_smul, Matrix.det_transpose, Fintype.card_fin]`.

Establish `hsec : secN (fun _ : Fin m => true) (2 * Real.pi) (2 * Real.pi * ((sg : ℤ) : ℝ)) (1 : PX m n) b = (∫ v : Fin n → ℂ, Complex.exp (star v ⬝ᵥ ((-(((2 * Real.pi : ℝ)) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) + (Complex.I * (((2 * Real.pi * ((sg : ℤ) : ℝ)) : ℝ) : ℂ)) • bᵀ) *ᵥ v))) ^ m`. Simplify using `only [secN]`. Simplify using `only [evX_one_mul_gs_mul_cexp_eq_prod]`. Establish `hp` using `integral_fintype_prod_volume_eq_pow (ι := Fin m) (fun v : Fin n → ℂ => Complex.exp (star v ⬝ᵥ ((-(((2 * Real.pi : ℝ)) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) + (Complex.I * (((2 * Real.pi * ((sg : ℤ) : ℝ)) : ℝ) : ℂ)) • bᵀ) *ᵥ v)))`. Rewrite `hp` using `[Fintype.card_fin]`.

Conclude with `hp`. Rewrite using `[F0_jG_mul_nG_eq sg e b hb, hsec]`. Generalize the expression as in `(∫ v : Fin n → ℂ, Complex.exp (star v ⬝ᵥ ((-(((2 * Real.pi : ℝ)) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) + (Complex.I * (((2 * Real.pi * ((sg : ℤ) : ℝ)) : ℝ) : ℂ)) • bᵀ) *ᵥ v))) = J at hJ ⊢`. Generalize the expression as in `(1 - (Complex.I * ((sg : ℤ) : ℂ)) • b).det = Δ at hJ ⊢`. Establish `hΔ : Δ ≠ 0`.

Introduce and unpack `rfl`. Simplify using `at hJ`. Conclude with `pow_ne_zero _ hpi hJ.symm`. Establish `hJ' : J = (Real.pi : ℂ) ^ n / ((((2 * Real.pi : ℝ)) : ℂ) ^ n * Δ)` using `eq_div_of_mul_eq (mul_ne_zero (pow_ne_zero _ h2) hΔ) hJ`. Rewrite using `[hJ', mul_zpow, zpow_neg, zpow_neg, zpow_natCast, zpow_natCast]`.

Clear the denominators using the available nonvanishing facts. Rewrite using `[mul_assoc, mul_assoc, ← mul_pow, ← mul_pow]`. Establish `hx : Δ * ((((2 * Real.pi : ℝ)) : ℂ) ^ n / (Real.pi : ℂ) ^ n * ((Real.pi : ℂ) ^ n / ((((2 * Real.pi : ℝ)) : ℂ) ^ n * Δ))) = 1`. Clear the denominators using the available nonvanishing facts. Rewrite using `[hx, one_pow, mul_one]`.
-/
theorem gauss_cell (sg : ℤˣ) (e : ℤ) : ∃ κ : ℂ, κ ≠ 0 ∧ ∀ b : Matrix (Fin n) (Fin n) ℂ, bᴴ = b →
    F0 (pOf sg m) (qOf sg m) e (jG n * nG b) =
      κ * secN (fun _ : Fin m => true) (2 * Real.pi) (2 * Real.pi * ((sg : ℤ) : ℝ)) (1 : PX m n) b := by
  have hs : ((sg : ℤ) : ℂ) = 1 ∨ ((sg : ℤ) : ℂ) = -1 := by
    rcases Int.units_eq_one_or sg with h | h <;> simp [h]
  have hIs : Complex.I * ((sg : ℤ) : ℂ) ≠ 0 := by
    rcases hs with h | h <;> simp [h, Complex.I_ne_zero]
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have h2 : (((2 * Real.pi : ℝ)) : ℂ) ≠ 0 := by
    push_cast
    exact mul_ne_zero two_ne_zero hpi
  refine ⟨(JJ n).det ^ e * ((-(Complex.I * ((sg : ℤ) : ℂ))) ^ n) ^ (-(m : ℤ)) *
      ((((2 * Real.pi : ℝ)) : ℂ) ^ n / (Real.pi : ℂ) ^ n) ^ m, ?_, ?_⟩
  · exact mul_ne_zero (mul_ne_zero (zpow_ne_zero _ JJ_det_ne)
      (zpow_ne_zero _ (pow_ne_zero _ (neg_ne_zero.mpr hIs))))
      (pow_ne_zero _ (div_ne_zero (pow_ne_zero _ h2) (pow_ne_zero _ hpi)))
  · intro b hb
    have hA : bᵀ.IsHermitian := (show b.IsHermitian from hb).transpose
    have hU : (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) ∈ Matrix.unitaryGroup (Fin n) ℂ :=
      hA.eigenvectorUnitary.2
    have hsU : star (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) *
        (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) = 1 := Matrix.mem_unitaryGroup_iff'.mp hU
    have hspec : star (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) * bᵀ *
        (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) =
        Matrix.diagonal (Complex.ofReal ∘ hA.eigenvalues) := by
      have := hA.conjStarAlgAut_star_eigenvectorUnitary
      simpa [Unitary.conjStarAlgAut_apply, mul_assoc] using this
    have hMd : star (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) *
        (-(((2 * Real.pi : ℝ)) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) +
          (Complex.I * (((2 * Real.pi * ((sg : ℤ) : ℝ)) : ℝ) : ℂ)) • bᵀ) *
        (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) =
        Matrix.diagonal (fun k => -(((2 * Real.pi : ℝ)) : ℂ) +
          Complex.I * (((2 * Real.pi * ((sg : ℤ) : ℝ)) : ℝ) : ℂ) * (hA.eigenvalues k : ℂ)) := by
      have e1 : star (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) *
          (-(((2 * Real.pi : ℝ)) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) +
            (Complex.I * (((2 * Real.pi * ((sg : ℤ) : ℝ)) : ℝ) : ℂ)) • bᵀ) *
          (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) =
          -(((2 * Real.pi : ℝ)) : ℂ) • (star (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) *
            (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ)) +
          (Complex.I * (((2 * Real.pi * ((sg : ℤ) : ℝ)) : ℝ) : ℂ)) •
            (star (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) * bᵀ *
              (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ)) := by
        simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]
      rw [e1, hsU, hspec]
      ext i j
      by_cases hij : i = j
      · subst hij
        simp
      · simp [Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij]
    have hd : ∀ k, 0 < (-(-(((2 * Real.pi : ℝ)) : ℂ) +
        Complex.I * (((2 * Real.pi * ((sg : ℤ) : ℝ)) : ℝ) : ℂ) * (hA.eigenvalues k : ℂ))).re := by
      intro k
      simp [Complex.mul_re]
      exact Real.pi_pos
    have hJ := integral_cexp_quadratic_mul_det_neg_eq_pi_pow _ _ hU _ hd hMd
    have hnegM : -(-(((2 * Real.pi : ℝ)) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) +
        (Complex.I * (((2 * Real.pi * ((sg : ℤ) : ℝ)) : ℝ) : ℂ)) • bᵀ) =
        (((2 * Real.pi : ℝ)) : ℂ) • (1 - (Complex.I * ((sg : ℤ) : ℂ)) • b)ᵀ := by
      ext i j
      by_cases hij : i = j
      · subst hij
        simp
        ring
      · simp [Matrix.one_apply_ne hij]
        ring
    rw [hnegM, Matrix.det_smul, Matrix.det_transpose, Fintype.card_fin] at hJ
    have hsec : secN (fun _ : Fin m => true) (2 * Real.pi) (2 * Real.pi * ((sg : ℤ) : ℝ)) (1 : PX m n) b =
        (∫ v : Fin n → ℂ, Complex.exp (star v ⬝ᵥ
          ((-(((2 * Real.pi : ℝ)) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) +
            (Complex.I * (((2 * Real.pi * ((sg : ℤ) : ℝ)) : ℝ) : ℂ)) • bᵀ) *ᵥ v))) ^ m := by
      simp only [secN]
      simp only [evX_one_mul_gs_mul_cexp_eq_prod]
      have hp := integral_fintype_prod_volume_eq_pow (ι := Fin m) (fun v : Fin n → ℂ =>
        Complex.exp (star v ⬝ᵥ ((-(((2 * Real.pi : ℝ)) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) +
            (Complex.I * (((2 * Real.pi * ((sg : ℤ) : ℝ)) : ℝ) : ℂ)) • bᵀ) *ᵥ v)))
      rw [Fintype.card_fin] at hp
      exact hp
    rw [F0_jG_mul_nG_eq sg e b hb, hsec]
    generalize (∫ v : Fin n → ℂ, Complex.exp (star v ⬝ᵥ
          ((-(((2 * Real.pi : ℝ)) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) +
            (Complex.I * (((2 * Real.pi * ((sg : ℤ) : ℝ)) : ℝ) : ℂ)) • bᵀ) *ᵥ v))) = J at hJ ⊢
    generalize (1 - (Complex.I * ((sg : ℤ) : ℂ)) • b).det = Δ at hJ ⊢
    have hΔ : Δ ≠ 0 := by
      rintro rfl
      simp at hJ
      exact pow_ne_zero _ hpi hJ.symm
    have hJ' : J = (Real.pi : ℂ) ^ n / ((((2 * Real.pi : ℝ)) : ℂ) ^ n * Δ) :=
      eq_div_of_mul_eq (mul_ne_zero (pow_ne_zero _ h2) hΔ) hJ
    rw [hJ', mul_zpow, zpow_neg, zpow_neg, zpow_natCast, zpow_natCast]
    field_simp
    rw [mul_assoc, mul_assoc, ← mul_pow, ← mul_pow]
    have hx : Δ * ((((2 * Real.pi : ℝ)) : ℂ) ^ n / (Real.pi : ℂ) ^ n *
        ((Real.pi : ℂ) ^ n / ((((2 * Real.pi : ℝ)) : ℂ) ^ n * Δ))) = 1 := by
      field_simp
    rw [hx, one_pow, mul_one]

/- English proof (translation)
Take `⟨κ, hκ, hF⟩` from `gauss_cell (m := m) (n := n) sg e`. Establish `hpar : ∀ (a b : Matrix (Fin n) (Fin n) ℂ), IsUnit a.det → bᴴ = b → (mR (mG a * nG b)).toBlocks₂₁ = 0`. Introduce `a b ha hb`. Rewrite using `[mR_mul, mR_mG ha, mR_nG hb, lower_left_block_mul]`. Simplify using `[mLc, nU]`.

Establish `hbig : Set.EqOn S (fun g => (C / κ) * F0 (pOf sg m) (qOf sg m) e g) {g : GR n | IsUnit (Matrix.toBlocks₂₁ (mR g)).det}`. Introduce `g hg`. Take `⟨a, b, b', ha, hb, hb', rfl⟩` from `big_eq g hg`. Establish `hy` using `hpar a b ha hb`. Establish `hassoc : mG a * nG b * jG n * nG b' = (mG a * nG b) * (jG n * nG b')`.

Simplify using `only [mul_assoc]`. Simplify using `only`. Rewrite using `[hassoc, hlaw _ _ hy, weight_factor_mul_parabolic _ _ _ _ _ hy, hcell b' hb', hF b' hb']`. Clear the denominators using the available nonvanishing facts. Establish `hall : S = fun g => (C / κ) * F0 (pOf sg m) (qOf sg m) e g` using `Continuous.ext_on dense_big hS (continuous_const.mul (continuous_weight_factor_unitary _ _ _)) hbig`.

Establish `h1'` using `congrFun hall 1`. Rewrite `h1'` using `[h1, weight_factor_one, mul_one]`. Introduce `g`. Rewrite using `[hall, ← h1']`. Simplify using the standard rewrite rules.
-/
theorem vac_unique (sg : ℤˣ) (e : ℤ) (S : GR n → ℂ) (C : ℂ) (hS : Continuous S) (h1 : S 1 = 1)
    (hlaw : ∀ y g : GR n, (mR y).toBlocks₂₁ = 0 → S (y * g) = F0 (pOf sg m) (qOf sg m) e y * S g)
    (hcell : ∀ b : Matrix (Fin n) (Fin n) ℂ, bᴴ = b →
      S (jG n * nG b) = C * secN (fun _ : Fin m => true) (2 * Real.pi) (2 * Real.pi * ((sg : ℤ) : ℝ)) (1 : PX m n) b) :
    ∀ g, S g = F0 (pOf sg m) (qOf sg m) e g := by
  obtain ⟨κ, hκ, hF⟩ := gauss_cell (m := m) (n := n) sg e
  have hpar : ∀ (a b : Matrix (Fin n) (Fin n) ℂ), IsUnit a.det → bᴴ = b →
      (mR (mG a * nG b)).toBlocks₂₁ = 0 := by
    intro a b ha hb
    rw [mR_mul, mR_mG ha, mR_nG hb, lower_left_block_mul]
    simp [mLc, nU]
  have hbig : Set.EqOn S (fun g => (C / κ) * F0 (pOf sg m) (qOf sg m) e g)
      {g : GR n | IsUnit (Matrix.toBlocks₂₁ (mR g)).det} := by
    intro g hg
    obtain ⟨a, b, b', ha, hb, hb', rfl⟩ := big_eq g hg
    have hy := hpar a b ha hb
    have hassoc : mG a * nG b * jG n * nG b' = (mG a * nG b) * (jG n * nG b') := by
      simp only [mul_assoc]
    simp only
    rw [hassoc, hlaw _ _ hy, weight_factor_mul_parabolic _ _ _ _ _ hy, hcell b' hb', hF b' hb']
    field_simp
  have hall : S = fun g => (C / κ) * F0 (pOf sg m) (qOf sg m) e g :=
    Continuous.ext_on dense_big hS (continuous_const.mul (continuous_weight_factor_unitary _ _ _)) hbig
  have h1' := congrFun hall 1
  rw [h1, weight_factor_one, mul_one] at h1'
  intro g
  rw [hall, ← h1']
  simp

end PositivityTheory.SiegelWeilFormula.KLI

end
