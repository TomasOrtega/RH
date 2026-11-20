import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLieBase
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HodgePeriodGram
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeChartBoundsOfSchurLemW
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PerValNeZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsExponentialChartAtPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsExponentialOfSemiAbelianFibreLinearChange
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CombMatAddMul
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RiemannRelationsPeriodMatrixHermitian
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DetNeZeroOfRealIndependentIsotropicHermitian
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology
open GlobalTheory.ShFam.Hor GlobalTheory.CxPts
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.ShFam.Hor.LogCh
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PeriodFrame

/- English proof (translation)
Unfold `hermForm`. Rewrite using `[sum_dotProduct]`. Simplify using `only [smul_dotProduct, smul_eq_mul]`.
-/
theorem frame_hermForm_sum_left {g n : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (c : Fin n → ℂ)
    (E : Fin n → Fin g → ℂ) (w : Fin g → ℂ) :
    hermForm Hm (∑ i, c i • E i) w = ∑ i, c i * hermForm Hm (E i) w := by
  unfold hermForm
  rw [sum_dotProduct]
  simp only [smul_dotProduct, smul_eq_mul]

/- English proof (translation)
Establish `hs : star (∑ i, c i • E i) = ∑ i, star (c i) • star (E i)`. Rewrite using `[star_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Use extensionality with `k`. Simplify using `[mul_comm]`.

Simplify using `only [hermForm, hs, Matrix.mulVec_sum, Matrix.mulVec_smul, dotProduct_sum, dotProduct_smul, smul_eq_mul]`.
-/
theorem frame_hermForm_sum_right {g n : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (c : Fin n → ℂ)
    (E : Fin n → Fin g → ℂ) (z : Fin g → ℂ) :
    hermForm Hm z (∑ i, c i • E i) = ∑ i, star (c i) * hermForm Hm z (E i) := by
  have hs : star (∑ i, c i • E i) = ∑ i, star (c i) • star (E i) := by
    rw [star_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    ext k
    simp [mul_comm]
  simp only [hermForm, hs, Matrix.mulVec_sum, Matrix.mulVec_smul, dotProduct_sum, dotProduct_smul, smul_eq_mul]

/- English proof (translation)
Use function extensionality and compare the values at `k`. Simplify using `[combMat, Finset.sum_apply]`.
-/
theorem frame_col {g r : ℕ} (l : Fin r → Fin g → ℂ) (ε : Matrix (Fin g) (Fin r) ℚ) (i : Fin g) :
    (fun k => combMat l ε k i) = ∑ m, (ε i m : ℂ) • l m := by
  funext k
  simp [combMat, Finset.sum_apply]

/- English proof (translation)
Rewrite using `[frame_col, frame_col, frame_hermForm_sum_left]`. Simplify using `only [frame_hermForm_sum_right, Finset.mul_sum, Complex.im_sum]`. Simplify using `only [Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply]`. Use `push_cast`. Simplify using `only [Finset.sum_mul]`.

Use `conv_rhs => rw [Finset.sum_comm]`. Use `Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun n _ => ?_` and prove the remaining obligations. Simplify using `[Complex.mul_im, hM]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem frame_im_hermForm {g r : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (M : Matrix (Fin r) (Fin r) ℤ)
    (l : Fin r → Fin g → ℂ) (hM : ∀ i j, (hermForm Hm (l i) (l j)).im = M i j)
    (A B : Matrix (Fin g) (Fin r) ℚ) (i k : Fin g) :
    (hermForm Hm (fun x => combMat l A x i) (fun x => combMat l B x k)).im
      = (((A * M.map (Int.cast : ℤ → ℚ) * Bᵀ) i k : ℚ) : ℝ) := by
  rw [frame_col, frame_col, frame_hermForm_sum_left]
  simp only [frame_hermForm_sum_right, Finset.mul_sum, Complex.im_sum]
  simp only [Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply]
  push_cast
  simp only [Finset.sum_mul]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun n _ => ?_
  simp [Complex.mul_im, hM]
  ring

/- English proof (translation)
Introduce `g r Hm M l ε φ D hD hH hpos _hl hM hεε hφφ hφε`. Use `set P := combMat l ε with hP`. Use `set Q := combMat l φ with hQ`. Use `set E : Fin g → Fin g → ℂ := fun i k => P k i with hE`. Use `set F : Fin g → Fin g → ℂ := fun j k => Q k j with hF`.

Establish `hEE : ∀ i j, (hermForm Hm (E i) (E j)).im = 0`. Introduce `i j`. Establish `h` using `frame_im_hermForm Hm M l hM ε ε i j`. Rewrite `h` using `[hεε]`. Simplify using `using h`.

Establish `hFF : ∀ i j, (hermForm Hm (F i) (F j)).im = 0`. Introduce `i j`. Establish `h` using `frame_im_hermForm Hm M l hM φ φ i j`. Rewrite `h` using `[hφφ]`. Simplify using `using h`.

Establish `hFE : ∀ i j, (hermForm Hm (F i) (E j)).im = if i = j then 1 else 0`. Introduce `i j`. Establish `h` using `frame_im_hermForm Hm M l hM φ ε i j`. Rewrite `h` using `[hφε]`. Express the relevant statement in the definitionally equal form `(hermForm Hm (F i) (E j)).im = _ at h`.

Rewrite using `[h]`. Apply the tactic sequence `by_cases hij : i = j <;> simp [hij, Matrix.one_apply]`. Establish `hind : LinearIndependent ℝ E`. Rewrite using `[Fintype.linearIndependent_iff]`. Introduce `a ha j`.

Establish `h1 : hermForm Hm (F j) (∑ i, ((a i : ℝ) : ℂ) • E i) = 0`. Establish `hs : (∑ i, ((a i : ℝ) : ℂ) • E i) = ∑ i, a i • E i`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Use extensionality with `k`. Simplify using the standard rewrite rules.

Rewrite using `[hs, ha]`. Simplify using `[hermForm]`. Rewrite `h1` using `[frame_hermForm_sum_right]`. Establish `h2` using `congrArg Complex.im h1`. Simplify `h2` using `[Complex.im_sum, Complex.mul_im, hFE]`.

Establish `hdet : P.det ≠ 0`. Establish `h` using `GlobalTheory.det_ne_zero_of_real_indep_isotropic g Hm E hpos hind hEE`. Conclude with `h`. Establish `hU : IsUnit P.det` using `isUnit_iff_ne_zero.mpr hdet`. Use `set τ := P⁻¹ * Q with hτ`.

Establish `hPτ : P * τ = Q`. Rewrite using `[hτ, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hU, Matrix.one_mul]`. Establish `hFτ : ∀ j, F j = ∑ i, τ i j • E i`. Introduce `j`. Use function extensionality and compare the values at `k`.

Establish `h` using `congrFun (congrFun hPτ k) j`. Simplify using `only [Matrix.mul_apply] at h`. Simplify using `only [hF, hE, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, ← h]`. Conclude with `Finset.sum_congr rfl fun i _ => mul_comm _ _`. Take `⟨hposτ, hsymτ⟩` from `GlobalTheory.riemann_relations_period_matrix g g Hm E F τ hH hpos hFτ hEE hFE`.

Establish `hτs : ∀ i j, τ i j = τ j i` using `fun i j => by`. Establish `h` using `hsymτ i j`. Rewrite `h` using `[hFF]`. Simplify `h` using `[sub_eq_zero]`. Use `set Y : Matrix (Fin g) (Fin g) ℝ := τ.map Complex.im with hY`.

Use `set a : Matrix (Fin g) (Fin g) ℝ := Matrix.of fun i k => (hermForm Hm (E i) (E k)).re with ha`. Establish `hAr : ∀ i k, hermForm Hm (E i) (E k) = (a i k : ℂ)` using `fun i k => Complex.ext (by simp [a]) (by simp [a, hEE])`. Establish `hYA : Y * a = 1`. Use extensionality with `j k`. Establish `h` using `hFE j k`.

Rewrite `h` using `[hFτ j, frame_hermForm_sum_left]`. Simplify using `only [hAr, Complex.im_sum, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, add_zero, zero_add] at h`. Rewrite using `[Matrix.mul_apply, Matrix.one_apply, ← h]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Simplify using `only [hY, Matrix.map_apply]`.

Rewrite using `[hτs j i]`. Establish `hTim : ((D : ℂ) • τ).map Complex.im = (D : ℝ) • Y`. Use extensionality with `i j`. Simplify using `[hY]`. Establish `hTre : (((D : ℂ) • τ).map Complex.im).map Complex.ofReal = (D : ℂ) • Y.map Complex.ofReal`.

Rewrite using `[hTim]`. Use extensionality with `i j`. Simplify using the standard rewrite rules. Establish `hYAc : Y.map Complex.ofReal * a.map Complex.ofReal = 1`. Use extensionality with `i k`.

Establish `h` using `congrFun (congrFun hYA i) k`. Simplify using `only [Matrix.mul_apply, Matrix.map_apply, Matrix.one_apply] at h ⊢`. Apply the tactic sequence `split_ifs at h ⊢ <;> exact_mod_cast h`. Establish `hDne : (D : ℂ) ≠ 0` using `by exact_mod_cast hD.ne'`. Establish `hinv : ((((D : ℂ) • τ).map Complex.im).map Complex.ofReal)⁻¹ = (D : ℂ)⁻¹ • a.map Complex.ofReal`.

Apply `Matrix.inv_eq_right_inv` to reduce the goal to its premises. Rewrite using `[hTre, Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ hDne, one_smul, hYAc]`. Use `⟨hU, ?_, ?_, ?_⟩` and prove the remaining obligations. Use `show ((D : ℂ) • τ)ᵀ = (D : ℂ) • τ`. Use extensionality with `i j`.

Simplify using `only [Matrix.transpose_apply, Matrix.smul_apply]`. Rewrite using `[hτs j i]`. Rewrite using `[Matrix.posDef_iff_dotProduct_mulVec, hTim]`. Use `⟨?_, fun x hx => ?_⟩` and prove the remaining obligations. Use extensionality with `i j`.

Simplify using `only [Matrix.conjTranspose_apply, Matrix.smul_apply, star_trivial, hY, Matrix.map_apply]`. Rewrite using `[hτs j i]`. Establish `e : star x ⬝ᵥ (((D : ℝ) • Y) *ᵥ x) = (D : ℝ) * (∑ i, ∑ j, (x i : ℂ) * τ i j * (x j : ℂ)).im`. Simplify using `only [star_trivial, dotProduct, Matrix.mulVec, Matrix.smul_apply, smul_eq_mul, Complex.im_sum, Finset.mul_sum, hY, Matrix.map_apply]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Simplify using `[Complex.mul_im]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `mul_pos (by exact_mod_cast hD) (hposτ x hx)`. Rewrite using `[hinv, smul_smul, Complex.ofReal_natCast, mul_inv_cancel₀ hDne, one_smul]`.

Use extensionality with `i j`. Rewrite using `[Matrix.map_apply, ← hAr i j]`. Simplify using `only [hermForm, dotProduct, Matrix.mulVec, Matrix.mul_apply, Matrix.transpose_apply, Matrix.conjTranspose_apply, Pi.star_apply, Matrix.map_apply, hE, Finset.mul_sum, Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun x _ => ?_` and prove the remaining obligations.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem riemann_relations_frame : ∀ (g r : ℕ) (Hm : Matrix (Fin g) (Fin g) ℂ) (M : Matrix (Fin r) (Fin r) ℤ) (l : Fin r → Fin g → ℂ) (ε φ : Matrix (Fin g) (Fin r) ℚ) (D : ℕ), 0 < D → Hm.IsHermitian → (∀ u : Fin g → ℂ, u ≠ 0 → 0 < (hermForm Hm u u).re) → LinearIndependent ℝ l → (∀ i j, (hermForm Hm (l i) (l j)).im = M i j) → ε * M.map (Int.cast : ℤ → ℚ) * εᵀ = 0 → φ * M.map (Int.cast : ℤ → ℚ) * φᵀ = 0 → φ * M.map (Int.cast : ℤ → ℚ) * εᵀ = 1 → IsUnit (GlobalTheory.PeriodFrame.combMat l ε).det ∧ ((D : ℂ) • ((GlobalTheory.PeriodFrame.combMat l ε)⁻¹ * GlobalTheory.PeriodFrame.combMat l φ)).IsSymm ∧ (((D : ℂ) • ((GlobalTheory.PeriodFrame.combMat l ε)⁻¹ * GlobalTheory.PeriodFrame.combMat l φ)).map Complex.im).PosDef ∧ (GlobalTheory.PeriodFrame.combMat l ε)ᵀ * Hm * (GlobalTheory.PeriodFrame.combMat l ε)ᵀᴴ = ((D : ℝ) : ℂ) • ((((D : ℂ) • ((GlobalTheory.PeriodFrame.combMat l ε)⁻¹ * GlobalTheory.PeriodFrame.combMat l φ)).map Complex.im).map Complex.ofReal)⁻¹ := by
  intro g r Hm M l ε φ D hD hH hpos _hl hM hεε hφφ hφε
  set P := combMat l ε with hP
  set Q := combMat l φ with hQ
  set E : Fin g → Fin g → ℂ := fun i k => P k i with hE
  set F : Fin g → Fin g → ℂ := fun j k => Q k j with hF
  have hEE : ∀ i j, (hermForm Hm (E i) (E j)).im = 0 := by
    intro i j
    have h := frame_im_hermForm Hm M l hM ε ε i j
    rw [hεε] at h
    simpa using h
  have hFF : ∀ i j, (hermForm Hm (F i) (F j)).im = 0 := by
    intro i j
    have h := frame_im_hermForm Hm M l hM φ φ i j
    rw [hφφ] at h
    simpa using h
  have hFE : ∀ i j, (hermForm Hm (F i) (E j)).im = if i = j then 1 else 0 := by
    intro i j
    have h := frame_im_hermForm Hm M l hM φ ε i j
    rw [hφε] at h
    change (hermForm Hm (F i) (E j)).im = _ at h
    rw [h]
    by_cases hij : i = j <;> simp [hij, Matrix.one_apply]
  have hind : LinearIndependent ℝ E := by
    rw [Fintype.linearIndependent_iff]
    intro a ha j
    have h1 : hermForm Hm (F j) (∑ i, ((a i : ℝ) : ℂ) • E i) = 0 := by
      have hs : (∑ i, ((a i : ℝ) : ℂ) • E i) = ∑ i, a i • E i := by
        refine Finset.sum_congr rfl fun i _ => ?_
        ext k
        simp
      rw [hs, ha]
      simp [hermForm]
    rw [frame_hermForm_sum_right] at h1
    have h2 := congrArg Complex.im h1
    simpa [Complex.im_sum, Complex.mul_im, hFE] using h2
  have hdet : P.det ≠ 0 := by
    have h := GlobalTheory.det_ne_zero_of_real_indep_isotropic g Hm E hpos hind hEE
    exact h
  have hU : IsUnit P.det := isUnit_iff_ne_zero.mpr hdet
  set τ := P⁻¹ * Q with hτ
  have hPτ : P * τ = Q := by
    rw [hτ, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hU, Matrix.one_mul]
  have hFτ : ∀ j, F j = ∑ i, τ i j • E i := by
    intro j
    funext k
    have h := congrFun (congrFun hPτ k) j
    simp only [Matrix.mul_apply] at h
    simp only [hF, hE, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, ← h]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  obtain ⟨hposτ, hsymτ⟩ := GlobalTheory.riemann_relations_period_matrix g g Hm E F τ hH hpos hFτ hEE hFE
  have hτs : ∀ i j, τ i j = τ j i := fun i j => by
    have h := hsymτ i j
    rw [hFF] at h
    simpa [sub_eq_zero] using h
  set Y : Matrix (Fin g) (Fin g) ℝ := τ.map Complex.im with hY
  set a : Matrix (Fin g) (Fin g) ℝ := Matrix.of fun i k => (hermForm Hm (E i) (E k)).re with ha
  have hAr : ∀ i k, hermForm Hm (E i) (E k) = (a i k : ℂ) := fun i k =>
    Complex.ext (by simp [a]) (by simp [a, hEE])
  have hYA : Y * a = 1 := by
    ext j k
    have h := hFE j k
    rw [hFτ j, frame_hermForm_sum_left] at h
    simp only [hAr, Complex.im_sum, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, add_zero, zero_add] at h
    rw [Matrix.mul_apply, Matrix.one_apply, ← h]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [hY, Matrix.map_apply]
    rw [hτs j i]
  have hTim : ((D : ℂ) • τ).map Complex.im = (D : ℝ) • Y := by
    ext i j
    simp [hY]
  have hTre : (((D : ℂ) • τ).map Complex.im).map Complex.ofReal = (D : ℂ) • Y.map Complex.ofReal := by
    rw [hTim]
    ext i j
    simp
  have hYAc : Y.map Complex.ofReal * a.map Complex.ofReal = 1 := by
    ext i k
    have h := congrFun (congrFun hYA i) k
    simp only [Matrix.mul_apply, Matrix.map_apply, Matrix.one_apply] at h ⊢
    split_ifs at h ⊢ <;> exact_mod_cast h
  have hDne : (D : ℂ) ≠ 0 := by exact_mod_cast hD.ne'
  have hinv : ((((D : ℂ) • τ).map Complex.im).map Complex.ofReal)⁻¹ = (D : ℂ)⁻¹ • a.map Complex.ofReal := by
    apply Matrix.inv_eq_right_inv
    rw [hTre, Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ hDne, one_smul, hYAc]
  refine ⟨hU, ?_, ?_, ?_⟩
  · show ((D : ℂ) • τ)ᵀ = (D : ℂ) • τ
    ext i j
    simp only [Matrix.transpose_apply, Matrix.smul_apply]
    rw [hτs j i]
  · rw [Matrix.posDef_iff_dotProduct_mulVec, hTim]
    refine ⟨?_, fun x hx => ?_⟩
    · ext i j
      simp only [Matrix.conjTranspose_apply, Matrix.smul_apply, star_trivial, hY, Matrix.map_apply]
      rw [hτs j i]
    · have e : star x ⬝ᵥ (((D : ℝ) • Y) *ᵥ x) = (D : ℝ) * (∑ i, ∑ j, (x i : ℂ) * τ i j * (x j : ℂ)).im := by
        simp only [star_trivial, dotProduct, Matrix.mulVec, Matrix.smul_apply, smul_eq_mul, Complex.im_sum,
          Finset.mul_sum, hY, Matrix.map_apply]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        simp [Complex.mul_im]
        ring
      rw [e]
      exact mul_pos (by exact_mod_cast hD) (hposτ x hx)
  · rw [hinv, smul_smul, Complex.ofReal_natCast, mul_inv_cancel₀ hDne, one_smul]
    ext i j
    rw [Matrix.map_apply, ← hAr i j]
    simp only [hermForm, dotProduct, Matrix.mulVec, Matrix.mul_apply, Matrix.transpose_apply,
      Matrix.conjTranspose_apply, Pi.star_apply, Matrix.map_apply, hE, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun x _ => ?_
    ring

end GlobalTheory.PeriodFrame
