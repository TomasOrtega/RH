import Mathlib
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.Statements
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.StatementsCusp
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.TransposeEqOfPosSemidef
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

noncomputable section

namespace PeriodGramPosDef

/- English proof (translation)
Simplify using `only [hermPair, dotProduct, mulVec, Matrix.map_apply, Complex.re_sum, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Establish `hkl : A l k = A k l` using `by rw [← transpose_apply A k l, hA]`. Rewrite using `[hkl]`.

Simplify using `only [Pi.star_apply, Complex.star_def, Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_im]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hermPair_symm {ι : Type*} [Fintype ι] {A : Matrix ι ι ℝ} (hA : Aᵀ = A) (v w : ι → ℂ) :
    hermPair A v w = hermPair A w v := by
  simp only [hermPair, dotProduct, mulVec, Matrix.map_apply, Complex.re_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  have hkl : A l k = A k l := by rw [← transpose_apply A k l, hA]
  rw [hkl]
  simp only [Pi.star_apply, Complex.star_def, Complex.mul_re, Complex.conj_re, Complex.conj_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.mul_im]
  ring

/- English proof (translation)
Simplify using `only [hermPair]`. Rewrite using `[mulVec_sum, dotProduct_sum, Complex.re_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[mulVec_smul, dotProduct_smul, smul_eq_mul, Complex.re_ofReal_mul]`.
-/
theorem hermPair_sum_right {ι κ : Type*} [Fintype ι] [Fintype κ] (A : Matrix ι ι ℝ)
    (v : ι → ℂ) (w : κ → ι → ℂ) (x : κ → ℝ) :
    hermPair A v (∑ j, (x j : ℂ) • w j) = ∑ j, x j * hermPair A v (w j) := by
  simp only [hermPair]
  rw [mulVec_sum, dotProduct_sum, Complex.re_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mulVec_smul, dotProduct_smul, smul_eq_mul, Complex.re_ofReal_mul]

/- English proof (translation)
Simplify using `only [hermPair]`. Rewrite using `[star_sum, sum_dotProduct, Complex.re_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[star_smul, Complex.star_def, Complex.conj_ofReal, smul_dotProduct, smul_eq_mul, Complex.re_ofReal_mul]`.
-/
theorem hermPair_sum_left {ι κ : Type*} [Fintype ι] [Fintype κ] (A : Matrix ι ι ℝ)
    (v : κ → ι → ℂ) (w : ι → ℂ) (x : κ → ℝ) :
    hermPair A (∑ i, (x i : ℂ) • v i) w = ∑ i, x i * hermPair A (v i) w := by
  simp only [hermPair]
  rw [star_sum, sum_dotProduct, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [star_smul, Complex.star_def, Complex.conj_ofReal, smul_dotProduct, smul_eq_mul,
    Complex.re_ofReal_mul]

/- English proof (translation)
Rewrite using `[hermValue, hermPair_sum_left]`. Simplify using `only [hermPair_sum_right, MCSchur.qf, dotProduct, mulVec, Matrix.of_apply]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.mul_sum, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem qf_gram {ι κ : Type*} [Fintype ι] [Fintype κ] (A : Matrix ι ι ℝ) (b : κ → ι → ℂ)
    (x : κ → ℝ) :
    MCSchur.qf (Matrix.of fun i j => hermPair A (b i) (b j)) x =
      hermValue A (∑ i, (x i : ℂ) • b i) := by
  rw [hermValue, hermPair_sum_left]
  simp only [hermPair_sum_right, MCSchur.qf, dotProduct, mulVec, Matrix.of_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/- English proof (translation)
Rewrite using `[Fin.sum_univ_add]`. Simplify using `only [periodBasis, Fin.append_left, Fin.append_right, ← mulVec_smul, ← mulVec_sum]`. Use `congr 1`. Use function extensionality and compare the values at `l`. Simplify using `[Finset.sum_apply, Pi.single_apply]`.

Use `congr 1`. Use function extensionality and compare the values at `l`. Simplify using `[Finset.sum_apply, Pi.single_apply]`.
-/
theorem sum_periodBasis {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) (x : Fin (g + g) → ℝ) :
    ∑ i, (x i : ℂ) • periodBasis τ i =
      (fun k => (x (Fin.castAdd g k) : ℂ)) + τ *ᵥ fun k => (x (Fin.natAdd g k) : ℂ) := by
  rw [Fin.sum_univ_add]
  simp only [periodBasis, Fin.append_left, Fin.append_right, ← mulVec_smul, ← mulVec_sum]
  congr 1
  · funext l
    simp [Finset.sum_apply, Pi.single_apply]
  · congr 1
    funext l
    simp [Finset.sum_apply, Pi.single_apply]

end PeriodGramPosDef

open PeriodGramPosDef in

/- English proof (translation)
Introduce `g τ hY`. Establish `hu : IsUnit (τ.map Complex.im).det` using `(Matrix.isUnit_iff_isUnit_det _).mp hY.isUnit`. Establish `hform : ∀ x : Fin (g + g) → ℝ, MCSchur.qf (periodGram τ) x = MCSchur.qf (τ.map Complex.im)⁻¹ ((fun k => x (Fin.castAdd g k)) + τ.map Complex.re *ᵥ fun k => x (Fin.natAdd g k)) + MCSchur.qf (τ.map Complex.im) (fun k => x (Fin.natAdd g k))`. Introduce `x`. Rewrite using `[periodGram, qf_gram, sum_periodBasis]`.

Conclude with `hPH g τ hu _ _`. Use `⟨?_, hform⟩` and prove the remaining obligations. Establish `hYi` using `hY.inv`. Establish `hsym : ((τ.map Complex.im)⁻¹)ᵀ = (τ.map Complex.im)⁻¹` using `MCCusp.transpose_eq_of_posSemidef hYi.posSemidef`. Use `PosDef.of_dotProduct_mulVec_pos ?_ fun x hx => ?_` and prove the remaining obligations.

Rewrite using `[IsHermitian, conjTranspose_eq_transpose_of_trivial]`. Use extensionality with `i j`. Simplify using `only [transpose_apply, periodGram, Matrix.of_apply]`. Conclude with `hermPair_symm hsym _ _`. Establish `e : star x ⬝ᵥ (periodGram τ *ᵥ x) = MCSchur.qf (periodGram τ) x`.

Simplify using `[MCSchur.qf]`. Rewrite using `[e, hform]`. Establish `h1` using `MCCusp.qf_nonneg hYi.posSemidef ((fun k => x (Fin.castAdd g k)) + τ.map Complex.re *ᵥ fun k => x (Fin.natAdd g k))`. Distinguish the cases in `hβ : (fun k => x (Fin.natAdd g k)) = 0`. Establish `hα : (fun k => x (Fin.castAdd g k)) ≠ 0`.

Introduce `hα`. Apply `hx` to reduce the goal to its premises. Use function extensionality and compare the values at `i`. Use `Fin.addCases (fun k => ?_) (fun k => ?_) i` and prove the remaining obligations. Conclude with `congrFun hα k`.

Conclude with `congrFun hβ k`. Establish `h2 : 0 < MCSchur.qf (τ.map Complex.im)⁻¹ (fun k => x (Fin.castAdd g k))`. Use `hYi.dotProduct_mulVec_pos hα` as an intermediate fact. Simplify `this` using `[MCSchur.qf]`. Rewrite using `[hβ, mulVec_zero, add_zero]`.

Rewrite `h1` using `[hβ, mulVec_zero, add_zero]`. Establish `h3 : MCSchur.qf (τ.map Complex.im) 0 = 0` using `by simp [MCSchur.qf]`. Rewrite using `[h3]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h2 : 0 < MCSchur.qf (τ.map Complex.im) (fun k => x (Fin.natAdd g k))`.

Use `hY.dotProduct_mulVec_pos hβ` as an intermediate fact. Simplify `this` using `[MCSchur.qf]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem PeriodGramPosDef.proof (hPH : PeriodHermValue.Statement) : PeriodGramPosDef.Statement := by
  intro g τ hY
  have hu : IsUnit (τ.map Complex.im).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp hY.isUnit
  have hform : ∀ x : Fin (g + g) → ℝ,
      MCSchur.qf (periodGram τ) x =
        MCSchur.qf (τ.map Complex.im)⁻¹
            ((fun k => x (Fin.castAdd g k)) + τ.map Complex.re *ᵥ fun k => x (Fin.natAdd g k)) +
          MCSchur.qf (τ.map Complex.im) (fun k => x (Fin.natAdd g k)) := by
    intro x
    rw [periodGram, qf_gram, sum_periodBasis]
    exact hPH g τ hu _ _
  refine ⟨?_, hform⟩
  have hYi := hY.inv
  have hsym : ((τ.map Complex.im)⁻¹)ᵀ = (τ.map Complex.im)⁻¹ :=
    MCCusp.transpose_eq_of_posSemidef hYi.posSemidef
  refine PosDef.of_dotProduct_mulVec_pos ?_ fun x hx => ?_
  · rw [IsHermitian, conjTranspose_eq_transpose_of_trivial]
    ext i j
    simp only [transpose_apply, periodGram, Matrix.of_apply]
    exact hermPair_symm hsym _ _
  · have e : star x ⬝ᵥ (periodGram τ *ᵥ x) = MCSchur.qf (periodGram τ) x := by
      simp [MCSchur.qf]
    rw [e, hform]
    have h1 := MCCusp.qf_nonneg hYi.posSemidef
      ((fun k => x (Fin.castAdd g k)) + τ.map Complex.re *ᵥ fun k => x (Fin.natAdd g k))
    by_cases hβ : (fun k => x (Fin.natAdd g k)) = 0
    · have hα : (fun k => x (Fin.castAdd g k)) ≠ 0 := by
        intro hα
        apply hx
        funext i
        refine Fin.addCases (fun k => ?_) (fun k => ?_) i
        · exact congrFun hα k
        · exact congrFun hβ k
      have h2 : 0 < MCSchur.qf (τ.map Complex.im)⁻¹ (fun k => x (Fin.castAdd g k)) := by
        have := hYi.dotProduct_mulVec_pos hα
        simpa [MCSchur.qf] using this
      rw [hβ, mulVec_zero, add_zero]
      rw [hβ, mulVec_zero, add_zero] at h1
      have h3 : MCSchur.qf (τ.map Complex.im) 0 = 0 := by simp [MCSchur.qf]
      rw [h3]
      linarith
    · have h2 : 0 < MCSchur.qf (τ.map Complex.im) (fun k => x (Fin.natAdd g k)) := by
        have := hY.dotProduct_mulVec_pos hβ
        simpa [MCSchur.qf] using this
      linarith

end

end GroundTheory.Heights₂.Heights
