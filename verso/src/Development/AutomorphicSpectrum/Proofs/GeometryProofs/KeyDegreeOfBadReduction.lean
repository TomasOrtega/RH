import Mathlib
import Development.AutomorphicSpectrum.Statements.GeometryStatements.KeyBadSt
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsThetaMeanSquareNorm
import Development.AutomorphicSpectrum.Statements.GeometryStatements.ZhangDimensionPushDownGrassmannianHeightBounds
import GroundTheory.HeightsAndTheta.Heights.KernelsLattice
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.StatementsBundles
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExactKeyFormulaProofStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PolarizedDataFieldExtensionStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ThetaFunctionArchimedeanFrameStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ThetaMultiplierQuadraticCharacterStatement
import Development.AutomorphicSpectrum.Proofs.AdelicProofs.GramMatrixPosDefConjugate
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LeWchartOne
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.NonvanishingSectionFieldExtStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.KeyInputFromPpDataStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.KeyOverLieBasisDegreeStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.KeyDegreePpDataStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeMetricFrameInnerStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FundamentalDomainRiemannFormStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.NormalizedDegreeGramDetStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Sl

namespace KeyDeg

/- English proof (translation)
Use extensionality with `i j`. Use `show ((B.metric.form σ).inner ((1 : ComplexAt σ) ⊗ₜ[𝓞 L] e i) ((1 : ComplexAt σ) ⊗ₜ[𝓞 L] e j) : ℂ) = _`. Rewrite using `[h i j]`. Simplify using `only [Matrix.transpose_apply, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply, Matrix.conjTranspose_apply, dotProduct, Matrix.mulVec, Pi.star_apply, Finset.mul_sum, Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`.

Use `Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => by ring))` and prove the remaining obligations.
-/
private theorem gramMat_eq_pi_smul_transpose {L : Type} [Field L] [NumberField L] (B : HermitianBundle.{0} L)
    (σ : L →+* ℂ) {g : ℕ} (e : Fin g → B.carrier) (W Hm : Matrix (Fin g) (Fin g) ℂ)
    (h : ∀ i j, ((B.metric.form σ).inner ((1 : ComplexAt σ) ⊗ₜ[𝓞 L] e i)
      ((1 : ComplexAt σ) ⊗ₜ[𝓞 L] e j) : ℂ) = Real.pi * (W j ⬝ᵥ Hm.mulVec (star (W i)))) :
    GlobalTheory.CompanionTheory.Ar.Lines.gramMat B σ e = ((Real.pi : ℂ) • (W * Hm * W.conjTranspose)).transpose := by
  ext i j
  show ((B.metric.form σ).inner ((1 : ComplexAt σ) ⊗ₜ[𝓞 L] e i)
    ((1 : ComplexAt σ) ⊗ₜ[𝓞 L] e j) : ℂ) = _
  rw [h i j]
  simp only [Matrix.transpose_apply, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply,
    Matrix.conjTranspose_apply, dotProduct, Matrix.mulVec, Pi.star_apply, Finset.mul_sum,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => by ring))

open Matrix in

/- English proof (translation)
Establish `hG : B.gramDet σ e = (GlobalTheory.CompanionTheory.Ar.Lines.gramMat B σ e).det` using `rfl`. Rewrite using `[hG, gramMat_eq_pi_smul_transpose B σ e W Hm h, Matrix.det_transpose, Matrix.det_smul, Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose, Fintype.card_fin]`. Rewrite using `[norm_mul, norm_mul, norm_mul, norm_pow, norm_star, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem gramDet_norm {L : Type} [Field L] [NumberField L] (B : HermitianBundle.{0} L) (σ : L →+* ℂ) {g : ℕ}
    (e : Fin g → B.carrier) (W Hm : Matrix (Fin g) (Fin g) ℂ)
    (h : ∀ i j, ((B.metric.form σ).inner ((1 : ComplexAt σ) ⊗ₜ[𝓞 L] e i) ((1 : ComplexAt σ) ⊗ₜ[𝓞 L] e j) : ℂ) =
      Real.pi * (W j ⬝ᵥ Hm.mulVec (star (W i)))) :
    ‖B.gramDet σ e‖ = Real.pi ^ g * ‖W.det‖ ^ 2 * ‖Hm.det‖ := by
  have hG : B.gramDet σ e = (GlobalTheory.CompanionTheory.Ar.Lines.gramMat B σ e).det := rfl
  rw [hG, gramMat_eq_pi_smul_transpose B σ e W Hm h, Matrix.det_transpose, Matrix.det_smul, Matrix.det_mul,
    Matrix.det_mul, Matrix.det_conjTranspose, Fintype.card_fin]
  rw [norm_mul, norm_mul, norm_mul, norm_pow, norm_star, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos Real.pi_pos]
  ring

/- English proof (translation)
Unfold `mean`. Apply `div_nonneg ?_ (Nat.cast_nonneg _)` to reduce the goal to its premises. Establish `hne : ∀ σ : L →+* ℂ, ‖σ k‖ ≠ 0` using `fun σ => norm_ne_zero_iff.mpr ((map_ne_zero σ).mpr hk)`. Use `show 0 ≤ ∑ σ : L →+* ℂ, Real.log ‖σ k‖`. Rewrite using `[← Real.log_prod (fun σ _ => hne σ)]`.

Apply `Real.log_nonneg` to reduce the goal to its premises. Rewrite using `[← norm_prod]`. Establish `hprod : (∏ σ : L →+* ℂ, σ k) = algebraMap ℚ ℂ (Algebra.norm ℚ k)`. Rewrite using `[Algebra.norm_eq_prod_embeddings ℚ ℂ k]`. Conclude with `Fintype.prod_equiv (RingHom.equivRatAlgHom L ℂ) _ _ (fun σ => rfl)`.

Rewrite using `[hprod]`. Take `⟨n, hn⟩ : ∃ n : ℤ, (n : ℚ) = Algebra.norm ℚ k` from `⟨Algebra.norm ℤ (⟨k, hint⟩ : 𝓞 L), Algebra.coe_norm_int _⟩`. Establish `hn0 : n ≠ 0`. Introduce and unpack `rfl`. Apply `hk` to reduce the goal to its premises.

Rewrite using `[← Algebra.norm_eq_zero_iff (R := ℚ), ← hn]`. Simplify using the standard rewrite rules. Rewrite using `[← hn]`. Simplify using `only [eq_ratCast, Rat.cast_intCast, Complex.norm_intCast]`. Conclude with `Int.one_le_abs hn0` after adjusting the coercions.
-/
theorem mean_log_nonneg {L : Type} [Field L] [NumberField L] (k : L) (hk : k ≠ 0) (hint : IsIntegral ℤ k) :
    0 ≤ mean L (fun σ => Real.log ‖σ k‖) := by
  unfold mean
  apply div_nonneg ?_ (Nat.cast_nonneg _)
  have hne : ∀ σ : L →+* ℂ, ‖σ k‖ ≠ 0 := fun σ => norm_ne_zero_iff.mpr ((map_ne_zero σ).mpr hk)
  show 0 ≤ ∑ σ : L →+* ℂ, Real.log ‖σ k‖
  rw [← Real.log_prod (fun σ _ => hne σ)]
  apply Real.log_nonneg
  rw [← norm_prod]
  have hprod : (∏ σ : L →+* ℂ, σ k) = algebraMap ℚ ℂ (Algebra.norm ℚ k) := by
    rw [Algebra.norm_eq_prod_embeddings ℚ ℂ k]
    exact Fintype.prod_equiv (RingHom.equivRatAlgHom L ℂ) _ _ (fun σ => rfl)
  rw [hprod]
  obtain ⟨n, hn⟩ : ∃ n : ℤ, (n : ℚ) = Algebra.norm ℚ k :=
    ⟨Algebra.norm ℤ (⟨k, hint⟩ : 𝓞 L), Algebra.coe_norm_int _⟩
  have hn0 : n ≠ 0 := by
    rintro rfl
    apply hk
    rw [← Algebra.norm_eq_zero_iff (R := ℚ), ← hn]
    simp
  rw [← hn]
  simp only [eq_ratCast, Rat.cast_intCast, Complex.norm_intCast]
  exact_mod_cast Int.one_le_abs hn0

/- English proof (translation)
Establish `hpos : (0:ℝ) < 2 * Real.pi` using `by positivity`. Rewrite using `[Real.log_le_iff_le_exp hpos]`. Establish `h1 : (2:ℝ) ≤ Real.exp 1`. Use `Real.add_one_le_exp (1:ℝ)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `h4 : Real.exp 4 = Real.exp 1 ^ 4`. Rewrite using `[← Real.exp_nat_mul]`. Evaluate the numerical expressions. Establish `h16 : (2:ℝ) ^ 4 ≤ Real.exp 1 ^ 4` using `pow_le_pow_left₀ (by norm_num) h1 4`. Establish `hp` using `Real.pi_le_four`.

Rewrite using `[h4]`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem log_two_pi_le : Real.log (2 * Real.pi) ≤ 4 := by
  have hpos : (0:ℝ) < 2 * Real.pi := by positivity
  rw [Real.log_le_iff_le_exp hpos]
  have h1 : (2:ℝ) ≤ Real.exp 1 := by
    have := Real.add_one_le_exp (1:ℝ)
    linarith
  have h4 : Real.exp 4 = Real.exp 1 ^ 4 := by
    rw [← Real.exp_nat_mul]
    norm_num
  have h16 : (2:ℝ) ^ 4 ≤ Real.exp 1 ^ 4 := pow_le_pow_left₀ (by norm_num) h1 4
  have hp := Real.pi_le_four
  rw [h4]
  nlinarith

end KeyDeg

namespace KeyDeg

/- English proof (translation)
Use `open Matrix ComplexOrder in`. Establish `hMeq` using `gramMat_eq_pi_smul_transpose B σ e W Hm h`. Establish `hGn` using `gramDet_norm B σ e W Hm h`. Establish `hdetM : (GlobalTheory.CompanionTheory.Ar.Lines.gramMat B σ e).det ≠ 0`. Introduce `h0`.

Establish `h1 : B.gramDet σ e = (GlobalTheory.CompanionTheory.Ar.Lines.gramMat B σ e).det` using `rfl`. Rewrite `hG` using `[h1, h0, norm_zero]`. Conclude with `lt_irrefl _ hG`. Establish `hWdet : W.det ≠ 0`. Introduce `h0`.

Rewrite `hG` using `[hGn, h0, norm_zero]`. Simplify using `at hG`. Establish `hWu : IsUnit W` using `(Matrix.isUnit_iff_isUnit_det W).mpr (isUnit_iff_ne_zero.mpr hWdet)`. Establish `hWHu : IsUnit Wᴴ` using `(Matrix.isUnit_iff_isUnit_det _).mpr (by rw [Matrix.det_conjTranspose]; exact isUnit_iff_ne_zero.mpr (star_ne_zero.mpr hWdet))`. Establish `hMpd : (GlobalTheory.CompanionTheory.Ar.Lines.gramMat B σ e).PosDef`.

Establish `hsd : (GlobalTheory.CompanionTheory.Ar.Lines.gramMat B σ e).PosSemidef`. Rewrite using `[GlobalTheory.CompanionTheory.Ar.Lines.gramMat_eq_gram]`. Conclude with `Matrix.posSemidef_gram ℂ _`. Conclude with `hsd.posDef_iff_isUnit.mpr ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdetM))`. Establish `hMh` using `hMpd.isHermitian`.

Establish `hT : W * Hm * Wᴴ = ((Real.pi : ℂ)⁻¹) • (GlobalTheory.CompanionTheory.Ar.Lines.gramMat B σ e)ᵀ`. Rewrite using `[hMeq, Matrix.transpose_transpose, smul_smul, inv_mul_cancel₀ (by exact_mod_cast Real.pi_ne_zero), one_smul]`. Establish `hXh : (W * Hm * Wᴴ).IsHermitian`. Use `Matrix.IsHermitian.ext (fun i j => ?_)` and prove the remaining obligations. Rewrite using `[hT]`.

Simplify using `only [Matrix.smul_apply, Matrix.transpose_apply, smul_eq_mul, star_mul', hMh.apply j i]`. Use `congr 1`. Simplify using `[Complex.conj_ofReal]`. Establish `hHerm : Hm.IsHermitian`. Establish `h1 : W * Hmᴴ * Wᴴ = W * Hm * Wᴴ` using `by conv_rhs => rw [← hXh.eq]`.

Rewrite using `[Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]`. Conclude with `hWu.mul_left_cancel (hWHu.mul_right_cancel h1)`. Use `⟨hHerm, fun z hz => ?_⟩` and prove the remaining obligations. Use `set y := z ᵥ* W⁻¹ with hy`. Establish `hyz : y ᵥ* W = z`.

Rewrite using `[hy, Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul W (isUnit_iff_ne_zero.mpr hWdet), Matrix.vecMul_one]`. Establish `hy0 : y ≠ 0`. Introduce `h0`. Apply `hz` to reduce the goal to its premises. Rewrite using `[← hyz, h0, Matrix.zero_vecMul]`.

Establish `key : z ⬝ᵥ Hm *ᵥ star z = ((Real.pi : ℂ)⁻¹) * (star y ⬝ᵥ (GlobalTheory.CompanionTheory.Ar.Lines.gramMat B σ e) *ᵥ y)`. Rewrite using `[← hyz, Matrix.star_vecMul, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hT, Matrix.smul_mulVec, dotProduct_smul, Matrix.mulVec_transpose, dotProduct_comm, ← Matrix.dotProduct_mulVec, smul_eq_mul]`. Establish `hpos : 0 < star y ⬝ᵥ (GlobalTheory.CompanionTheory.Ar.Lines.gramMat B σ e) *ᵥ y` using `hMpd.dotProduct_mulVec_pos hy0`. Rewrite using `[key]`. Establish `hre` using `(Complex.pos_iff.mp hpos).1`.

Rewrite using `[show ((Real.pi : ℂ)⁻¹) = ((Real.pi⁻¹ : ℝ) : ℂ) by push_cast; rfl, Complex.re_ofReal_mul]`. Conclude with `mul_pos (inv_pos.mpr Real.pi_pos) hre`.
-/
private theorem isHermitian_and_posDef_of_gramDet_pos {L : Type} [Field L] [NumberField L] (B : HermitianBundle.{0} L)
    (σ : L →+* ℂ) {g : ℕ} (e : Fin g → B.carrier) (W Hm : Matrix (Fin g) (Fin g) ℂ)
    (h : ∀ i j, ((B.metric.form σ).inner ((1 : ComplexAt σ) ⊗ₜ[𝓞 L] e i)
      ((1 : ComplexAt σ) ⊗ₜ[𝓞 L] e j) : ℂ) = Real.pi * (W j ⬝ᵥ Hm.mulVec (star (W i))))
    (hG : 0 < ‖B.gramDet σ e‖) :
    Hm.IsHermitian ∧ ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ Hm.mulVec (star z)).re := by
  open Matrix ComplexOrder in
  classical
  have hMeq := gramMat_eq_pi_smul_transpose B σ e W Hm h
  have hGn := gramDet_norm B σ e W Hm h
  have hdetM : (GlobalTheory.CompanionTheory.Ar.Lines.gramMat B σ e).det ≠ 0 := by
    intro h0
    have h1 : B.gramDet σ e = (GlobalTheory.CompanionTheory.Ar.Lines.gramMat B σ e).det := rfl
    rw [h1, h0, norm_zero] at hG
    exact lt_irrefl _ hG
  have hWdet : W.det ≠ 0 := by
    intro h0
    rw [hGn, h0, norm_zero] at hG
    simp at hG
  have hWu : IsUnit W := (Matrix.isUnit_iff_isUnit_det W).mpr (isUnit_iff_ne_zero.mpr hWdet)
  have hWHu : IsUnit Wᴴ := (Matrix.isUnit_iff_isUnit_det _).mpr
    (by rw [Matrix.det_conjTranspose]; exact isUnit_iff_ne_zero.mpr (star_ne_zero.mpr hWdet))
  have hMpd : (GlobalTheory.CompanionTheory.Ar.Lines.gramMat B σ e).PosDef := by
    have hsd : (GlobalTheory.CompanionTheory.Ar.Lines.gramMat B σ e).PosSemidef := by
      rw [GlobalTheory.CompanionTheory.Ar.Lines.gramMat_eq_gram]
      exact Matrix.posSemidef_gram ℂ _
    exact hsd.posDef_iff_isUnit.mpr
      ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdetM))
  have hMh := hMpd.isHermitian
  have hT : W * Hm * Wᴴ = ((Real.pi : ℂ)⁻¹) • (GlobalTheory.CompanionTheory.Ar.Lines.gramMat B σ e)ᵀ := by
    rw [hMeq, Matrix.transpose_transpose, smul_smul,
      inv_mul_cancel₀ (by exact_mod_cast Real.pi_ne_zero), one_smul]
  have hXh : (W * Hm * Wᴴ).IsHermitian := by
    refine Matrix.IsHermitian.ext (fun i j => ?_)
    rw [hT]
    simp only [Matrix.smul_apply, Matrix.transpose_apply, smul_eq_mul, star_mul', hMh.apply j i]
    congr 1
    simp [Complex.conj_ofReal]
  have hHerm : Hm.IsHermitian := by
    have h1 : W * Hmᴴ * Wᴴ = W * Hm * Wᴴ := by
      conv_rhs => rw [← hXh.eq]
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
        Matrix.mul_assoc]
    exact hWu.mul_left_cancel (hWHu.mul_right_cancel h1)
  refine ⟨hHerm, fun z hz => ?_⟩
  set y := z ᵥ* W⁻¹ with hy
  have hyz : y ᵥ* W = z := by
    rw [hy, Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul W (isUnit_iff_ne_zero.mpr hWdet),
      Matrix.vecMul_one]
  have hy0 : y ≠ 0 := by
    intro h0
    apply hz
    rw [← hyz, h0, Matrix.zero_vecMul]
  have key : z ⬝ᵥ Hm *ᵥ star z =
      ((Real.pi : ℂ)⁻¹) * (star y ⬝ᵥ (GlobalTheory.CompanionTheory.Ar.Lines.gramMat B σ e) *ᵥ y) := by
    rw [← hyz, Matrix.star_vecMul, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
      Matrix.mulVec_mulVec, hT, Matrix.smul_mulVec, dotProduct_smul, Matrix.mulVec_transpose,
      dotProduct_comm, ← Matrix.dotProduct_mulVec, smul_eq_mul]
  have hpos : 0 < star y ⬝ᵥ (GlobalTheory.CompanionTheory.Ar.Lines.gramMat B σ e) *ᵥ y := hMpd.dotProduct_mulVec_pos hy0
  rw [key]
  have hre := (Complex.pos_iff.mp hpos).1
  rw [show ((Real.pi : ℂ)⁻¹) = ((Real.pi⁻¹ : ℝ) : ℂ) by push_cast; rfl, Complex.re_ofReal_mul]
  exact mul_pos (inv_pos.mpr Real.pi_pos) hre

/- English proof (translation)
Establish `hσk : 0 < ‖σ k‖` using `norm_pos_iff.mpr ((map_ne_zero σ).mpr hk)`. Establish `hent : ∀ i j, ((D.B.metric.form σ).inner ((1 : ComplexAt σ) ⊗ₜ[𝓞 L] e i) ((1 : ComplexAt σ) ⊗ₜ[𝓞 L] e j) : ℂ) = Real.pi * (W j ⬝ᵥ a.Hm.mulVec (star (W i)))` using `fun i j => GlobalTheory.T.hodge_metric_frame_inner E H L D σ a (e i) (e j) (W i) (W j) (hW i) (hW j)`. Establish `hGn` using `gramDet_norm D.B σ e W a.Hm hent`. Take `⟨hHerm, hpos⟩` from `isHermitian_and_posDef_of_gramDet_pos D.B σ e W a.Hm hent hG`. Establish `hWn : 0 < ‖W.det‖`.

Break down `(norm_nonneg W.det).lt_or_eq with h0 | h0` into its components or cases. Conclude with `h0`. Rewrite `hG` using `[hGn, ← h0]`. Simplify using `at hG`. Establish `h14` using `GlobalTheory.T.theta_multiplier_quadratic_character E H L D σ a`.

Establish `hint1 : ∀ l ∈ a.u.Λ, ∀ l' ∈ a.u.Λ, ∃ k : ℤ, (l ⬝ᵥ a.Hm.mulVec (star l')).im = k` using `fun l hl l' hl' => h14.1 ⟨l, hl⟩ ⟨l', hl'⟩`. Establish `hint2 : ∀ w : Fin D.g → ℂ, (∀ l ∈ a.u.Λ, ∃ k : ℤ, (w ⬝ᵥ a.Hm.mulVec (star l)).im = k) → w ∈ a.u.Λ` using `fun w hw => h14.2.1 w (fun l => hw l l.2)`. Establish `hX : 0 < (2 * Real.pi) ^ (2 * D.g) * ‖D.B.gramDet σ e‖ ^ 2 / ‖σ k‖` using `by positivity`. Establish `hc8 : Real.exp (Real.log ((2 * Real.pi) ^ (2 * D.g) * ‖D.B.gramDet σ e‖ ^ 2 / ‖σ k‖) / 8) ^ 8 = (2 * Real.pi) ^ (2 * D.g) * ‖D.B.gramDet σ e‖ ^ 2 / ‖σ k‖`. Establish `h8 : ∀ x : ℝ, (8 : ℝ) * (x / 8) = x` using `fun x => by ring`.

Rewrite using `[← Real.exp_nat_mul]`. Use `push_cast`. Rewrite using `[h8, Real.exp_log hX]`. Unfold `GlobalTheory.CompanionTheory.Ar.Sl.ArchFrame.IsThetaMeanSquareNorm`. Use `⟨Real.exp_pos _, fun Fd hFd => ?_⟩` and prove the remaining obligations.

Establish `hV` using `GlobalTheory.T.fundamental_domain_riemann_form D.g a.u.Λ a.Hm a.u.discrete a.u.full hHerm hpos hint1 hint2 Fd hFd`. Establish `hA'` using `hA Fd hFd`. Establish `hq : (volume Fd).toReal / (Real.pi ^ D.g * ‖W.det‖ ^ 2) = 1 / ‖D.B.gramDet σ e‖`. Rewrite using `[hGn, div_eq_div_iff (mul_pos (pow_pos Real.pi_pos _) (pow_pos hWn 2)).ne' (by rw [← hGn]; exact hG.ne')]`. Take the linear combination `(Real.pi ^ D.g * ‖W.det‖ ^ 2) * hV`.

Rewrite `hA'` using `[hq]`. Establish `hI0 : 0 ≤ (∫ w in Fd, a.nrm 1 θ w ^ 2) / (volume Fd).toReal` using `div_nonneg (MeasureTheory.integral_nonneg (fun w => by positivity)) ENNReal.toReal_nonneg`. Establish `hG2 : ‖D.B.gramDet σ e‖ ^ 2 * (1 / ‖D.B.gramDet σ e‖) ^ 2 = 1`. Rewrite using `[← mul_pow, mul_one_div_cancel hG.ne', one_pow]`. Establish `hI4 : ((∫ w in Fd, a.nrm 1 θ w ^ 2) / (volume Fd).toReal) ^ 4 = (2 * Real.pi) ^ (2 * D.g) * ‖D.B.gramDet σ e‖ ^ 2 / ‖σ k‖`.

Rewrite using `[eq_div_iff hσk.ne', ← hA']`. Take the linear combination `(-(‖σ k‖ * ((∫ w in Fd, a.nrm 1 θ w ^ 2) / (volume Fd).toReal) ^ 4)) * hG2`. Establish `hc : 0 ≤ Real.exp (Real.log ((2 * Real.pi) ^ (2 * D.g) * ‖D.B.gramDet σ e‖ ^ 2 / ‖σ k‖) / 8) ^ 2` using `by positivity`. Use `(pow_left_inj₀ hc hI0 (by norm_num : (4 : ℕ) ≠ 0)).mp ?_` and prove the remaining obligations. Rewrite using `[← pow_mul, show 2 * 4 = 8 from rfl, hc8, hI4]`.
-/
theorem is_L2_of_gram_det_pos {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {L : Type} [Field L] [NumberField L]
    (D : PPData H L) (k : L) (hk : k ≠ 0) (e : Fin D.g → D.B.carrier) (σ : L →+* ℂ)
    (hG : 0 < ‖D.B.gramDet σ e‖) (a : D.Frame σ) (θ : (Fin D.g → ℂ) → ℂ)
    (W : Matrix (Fin D.g) (Fin D.g) ℂ) (hW : ∀ i, D.IsVec a (e i) (W i))
    (hA : ∀ Fd : Set (Fin D.g → ℂ), IsAddFundamentalDomain a.u.Λ Fd volume →
      ‖σ k‖ * ((∫ w in Fd, a.nrm 1 θ w ^ 2) / (volume Fd).toReal) ^ 4 *
        ((volume Fd).toReal / (Real.pi ^ D.g * ‖W.det‖ ^ 2)) ^ 2 = (2 * Real.pi) ^ (2 * D.g)) :
    a.IsThetaMeanSquareNorm θ (Real.exp (Real.log ((2 * Real.pi) ^ (2 * D.g) * ‖D.B.gramDet σ e‖ ^ 2 / ‖σ k‖) / 8)) := by
  have hσk : 0 < ‖σ k‖ := norm_pos_iff.mpr ((map_ne_zero σ).mpr hk)
  have hent : ∀ i j, ((D.B.metric.form σ).inner ((1 : ComplexAt σ) ⊗ₜ[𝓞 L] e i)
      ((1 : ComplexAt σ) ⊗ₜ[𝓞 L] e j) : ℂ) = Real.pi * (W j ⬝ᵥ a.Hm.mulVec (star (W i))) :=
    fun i j => GlobalTheory.T.hodge_metric_frame_inner E H L D σ a (e i) (e j) (W i) (W j) (hW i) (hW j)
  have hGn := gramDet_norm D.B σ e W a.Hm hent
  obtain ⟨hHerm, hpos⟩ := isHermitian_and_posDef_of_gramDet_pos D.B σ e W a.Hm hent hG
  have hWn : 0 < ‖W.det‖ := by
    rcases (norm_nonneg W.det).lt_or_eq with h0 | h0
    · exact h0
    · rw [hGn, ← h0] at hG
      simp at hG
  have h14 := GlobalTheory.T.theta_multiplier_quadratic_character E H L D σ a
  have hint1 : ∀ l ∈ a.u.Λ, ∀ l' ∈ a.u.Λ, ∃ k : ℤ, (l ⬝ᵥ a.Hm.mulVec (star l')).im = k :=
    fun l hl l' hl' => h14.1 ⟨l, hl⟩ ⟨l', hl'⟩
  have hint2 : ∀ w : Fin D.g → ℂ, (∀ l ∈ a.u.Λ, ∃ k : ℤ, (w ⬝ᵥ a.Hm.mulVec (star l)).im = k) →
      w ∈ a.u.Λ :=
    fun w hw => h14.2.1 w (fun l => hw l l.2)
  have hX : 0 < (2 * Real.pi) ^ (2 * D.g) * ‖D.B.gramDet σ e‖ ^ 2 / ‖σ k‖ := by positivity
  have hc8 : Real.exp (Real.log ((2 * Real.pi) ^ (2 * D.g) * ‖D.B.gramDet σ e‖ ^ 2 / ‖σ k‖) / 8) ^ 8
      = (2 * Real.pi) ^ (2 * D.g) * ‖D.B.gramDet σ e‖ ^ 2 / ‖σ k‖ := by
    have h8 : ∀ x : ℝ, (8 : ℝ) * (x / 8) = x := fun x => by ring
    rw [← Real.exp_nat_mul]
    push_cast
    rw [h8, Real.exp_log hX]
  unfold GlobalTheory.CompanionTheory.Ar.Sl.ArchFrame.IsThetaMeanSquareNorm
  refine ⟨Real.exp_pos _, fun Fd hFd => ?_⟩
  have hV := GlobalTheory.T.fundamental_domain_riemann_form D.g a.u.Λ a.Hm a.u.discrete a.u.full hHerm hpos hint1 hint2 Fd hFd
  have hA' := hA Fd hFd
  have hq : (volume Fd).toReal / (Real.pi ^ D.g * ‖W.det‖ ^ 2) = 1 / ‖D.B.gramDet σ e‖ := by
    rw [hGn, div_eq_div_iff (mul_pos (pow_pos Real.pi_pos _) (pow_pos hWn 2)).ne'
      (by rw [← hGn]; exact hG.ne')]
    linear_combination (Real.pi ^ D.g * ‖W.det‖ ^ 2) * hV
  rw [hq] at hA'
  have hI0 : 0 ≤ (∫ w in Fd, a.nrm 1 θ w ^ 2) / (volume Fd).toReal :=
    div_nonneg (MeasureTheory.integral_nonneg (fun w => by positivity)) ENNReal.toReal_nonneg
  have hG2 : ‖D.B.gramDet σ e‖ ^ 2 * (1 / ‖D.B.gramDet σ e‖) ^ 2 = 1 := by
    rw [← mul_pow, mul_one_div_cancel hG.ne', one_pow]
  have hI4 : ((∫ w in Fd, a.nrm 1 θ w ^ 2) / (volume Fd).toReal) ^ 4
      = (2 * Real.pi) ^ (2 * D.g) * ‖D.B.gramDet σ e‖ ^ 2 / ‖σ k‖ := by
    rw [eq_div_iff hσk.ne', ← hA']
    linear_combination (-(‖σ k‖ * ((∫ w in Fd, a.nrm 1 θ w ^ 2) / (volume Fd).toReal) ^ 4)) * hG2
  have hc : 0 ≤ Real.exp (Real.log ((2 * Real.pi) ^ (2 * D.g) * ‖D.B.gramDet σ e‖ ^ 2 / ‖σ k‖) / 8) ^ 2 :=
    by positivity
  refine (pow_left_inj₀ hc hI0 (by norm_num : (4 : ℕ) ≠ 0)).mp ?_
  rw [← pow_mul, show 2 * 4 = 8 from rfl, hc8, hI4]

end KeyDeg

open scoped ComplexOrder in

/- English proof (translation)
Introduce `hb`. Establish `hKF` using `GlobalTheory.T.exactKeyFormula_proof`. Unfold `ReciprocityTheory.ChartRestriction.G.Geo.Tor.KeyFormula at hKF`. Take `⟨κ, h1, h2, h3, h4, h5⟩` from `hKF`. Establish `hHom : GlobalTheory.KeyCl.Homog (fun _ => 1) κ`.

Unfold `GlobalTheory.KeyCl.Homog`. Simplify using `using h1`. Establish `hArch : GlobalTheory.KeyCl.ArchNorm (fun _ => 1) κ`. Unfold `GlobalTheory.KeyCl.ArchNorm`. Simplify using `using h5`.

Unfold `GlobalTheory.CompanionTheory.Ar.Sl.KeyDegSt`. Use `⟨1, zero_le_one, ?_⟩` and prove the remaining obligations. Introduce `E _ _ _ H L _ _ D hg`. Take `⟨L', i1, i2, i3, D', x3, s, e, hNV, hLI, hsp⟩` from `GlobalTheory.T.nonvanishing_section_field_ext E H L D hg`. Establish `h15` using `(GlobalTheory.T.polarized_data_field_extension E H L D L').2 D' x3`.

Establish `hgg : D'.g = D.g` using `h15.1`. Establish `hpp : D'.hp = D.hp` using `h15.2.1`. Establish `hg' : 1 ≤ D'.g` using `hgg ▸ hg`. Take `⟨x, th, hgx, v, hSS, hNV', hKO, hLB, hv⟩` from `GlobalTheory.T.key_input_from_pp_data E H L' D' hg' s e hNV hLI hsp`. Establish `hint : IsIntegral ℤ ((κ L' x : L'ˣ) : L')` using `GlobalTheory.T.key_over_lie_basis_degree hb κ hHom h2 h3 h4 hArch E H L' D'.t th x v hKO hLB hNV'`.

Establish `hk : ((κ L' x : L'ˣ) : L') ≠ 0` using `Units.ne_zero _`. Establish `hGpos : ∀ σ : L' →+* ℂ, 0 < ‖D'.B.gramDet σ e‖`. Introduce `σ`. Establish `hpd` using `(GlobalTheory.CompanionTheory.Ar.Lines.gramMat_posDef_and_conj L' D'.B D'.g e hLI).1 σ`. Establish `h1' : D'.B.gramDet σ e = (GlobalTheory.CompanionTheory.Ar.Lines.gramMat D'.B σ e).det` using `rfl`.

Rewrite using `[h1']`. Conclude with `norm_pos_iff.mpr hpd.det_pos.ne'`. Use `⟨L', i1, i2, i3, D', x3, s, ?_⟩` and prove the remaining obligations. Unfold `GlobalTheory.CompanionTheory.Ar.Sl.PPData.HasTheta`. Use `⟨fun σ => Real.exp (Real.log ((2 * Real.pi) ^ (2 * D'.g) * ‖D'.B.gramDet σ e‖ ^ 2 / ‖σ ((κ L' x : L'ˣ) : L')‖) / 8), ?_, ?_⟩` and prove the remaining obligations.

Introduce `σ a θ hθ`. Establish `h13` using `((GlobalTheory.T.theta_function_archimedean_frame E H L' D' σ).2 a).2.2`. Use `choose W hW using fun i => (h13 (e i)).1.exists`. Conclude with `KeyDeg.is_L2_of_gram_det_pos D' _ hk e σ (hGpos σ) a θ (Matrix.of W) hW (fun Fd hFd => GlobalTheory.T.key_degree_pp_data κ h2 hArch E H L' D' x th s hgx v e hSS hKO hLB hv σ a θ (Matrix.of W) Fd hθ hW hFd)`. Establish `hf : ∀ σ : L' →+* ℂ, Real.log (Real.exp (Real.log ((2 * Real.pi) ^ (2 * D'.g) * ‖D'.B.gramDet σ e‖ ^ 2 / ‖σ ((κ L' x : L'ˣ) : L')‖) / 8)) = 2 * (D'.g : ℝ) * Real.log (2 * Real.pi) / 8 + 1 / 4 * Real.log ‖D'.B.gramDet σ e‖ - 1 / 8 * Real.log ‖σ ((κ L' x : L'ˣ) : L')‖`.

Introduce `σ`. Establish `hσk : ‖σ ((κ L' x : L'ˣ) : L')‖ ≠ 0` using `(norm_pos_iff.mpr ((map_ne_zero σ).mpr hk)).ne'`. Establish `hG0 : ‖D'.B.gramDet σ e‖ ≠ 0` using `(hGpos σ).ne'`. Rewrite using `[Real.log_exp, Real.log_div (mul_ne_zero (by positivity) (pow_ne_zero 2 hG0)) hσk, Real.log_mul (by positivity) (pow_ne_zero 2 hG0), Real.log_pow, Real.log_pow]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Establish `hmk` using `KeyDeg.mean_log_nonneg ((κ L' x : L'ˣ) : L') hk hint`. Establish `hmG` using `GlobalTheory.T.normalized_degree_gram_det L' D'.B D'.g e hLI hsp`. Establish `hhp : -D'.B.normDegree ⊤ ≤ D'.hp`. Unfold `GlobalTheory.CompanionTheory.Ar.Sl.PPData.hp`.

Conclude with `le_max_left _ _`. Rewrite `hhp` using `[hpp]`. Establish `hl` using `KeyDeg.log_two_pi_le`. Establish `hn : (0 : ℝ) < Module.finrank ℚ L'` using `Nat.cast_pos.mpr Module.finrank_pos`. Unfold `GlobalTheory.CompanionTheory.Ar.Sl.mean at hmk hmG ⊢`.

Simplify using `only [hf]`. Rewrite using `[Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, NumberField.Embeddings.card]`. Establish `hS1 : (∑ σ : L' →+* ℂ, Real.log ‖D'.B.gramDet σ e‖) = -2 * D'.B.normDegree ⊤ * (Module.finrank ℚ L' : ℝ)`. Establish `h1'' : (∑ σ : L' →+* ℂ, Real.log ‖D'.B.gramDet σ e‖) / (Module.finrank ℚ L' : ℝ) = -2 * D'.B.normDegree ⊤` using `by linarith`. Rewrite `h1''` using `[div_eq_iff hn.ne']`.

Conclude with `h1''`. Establish `hS2 : 0 ≤ ∑ σ : L' →+* ℂ, Real.log ‖σ ((κ L' x : L'ˣ) : L')‖`. Establish `h2''` using `mul_nonneg hmk hn.le`. Rewrite `h2''` using `[div_mul_cancel₀ _ hn.ne']`. Then use the resulting hypothesis. Establish `hA : 2 * (D'.g : ℝ) * Real.log (2 * Real.pi) / 8 ≤ D.g`.

Establish `hgg' : (D'.g : ℝ) = D.g` using `by exact_mod_cast hgg`. Rewrite using `[hgg']`. Establish `hg0 : (0 : ℝ) ≤ D.g` using `Nat.cast_nonneg _`. Use the polynomial consequences of the given equalities and inequalities. Rewrite using `[div_le_iff₀ hn]`.

Use polynomial arithmetic with `[mul_le_mul_of_nonneg_left hA hn.le, mul_le_mul_of_nonneg_left hhp hn.le, hS1, hS2]`.
-/
theorem keyDeg_of_keyBad : KeyBadSt → KeyDegSt := by
  intro hb
  have hKF := GlobalTheory.T.exactKeyFormula_proof
  unfold ReciprocityTheory.ChartRestriction.G.Geo.Tor.KeyFormula at hKF
  obtain ⟨κ, h1, h2, h3, h4, h5⟩ := hKF
  have hHom : GlobalTheory.KeyCl.Homog (fun _ => 1) κ := by
    unfold GlobalTheory.KeyCl.Homog
    simpa using h1
  have hArch : GlobalTheory.KeyCl.ArchNorm (fun _ => 1) κ := by
    unfold GlobalTheory.KeyCl.ArchNorm
    simpa using h5
  unfold GlobalTheory.CompanionTheory.Ar.Sl.KeyDegSt
  refine ⟨1, zero_le_one, ?_⟩
  intro E _ _ _ H L _ _ D hg
  obtain ⟨L', i1, i2, i3, D', x3, s, e, hNV, hLI, hsp⟩ := GlobalTheory.T.nonvanishing_section_field_ext E H L D hg
  have h15 := (GlobalTheory.T.polarized_data_field_extension E H L D L').2 D' x3
  have hgg : D'.g = D.g := h15.1
  have hpp : D'.hp = D.hp := h15.2.1
  have hg' : 1 ≤ D'.g := hgg ▸ hg
  obtain ⟨x, th, hgx, v, hSS, hNV', hKO, hLB, hv⟩ := GlobalTheory.T.key_input_from_pp_data E H L' D' hg' s e hNV hLI hsp
  have hint : IsIntegral ℤ ((κ L' x : L'ˣ) : L') :=
    GlobalTheory.T.key_over_lie_basis_degree hb κ hHom h2 h3 h4 hArch E H L' D'.t th x v hKO hLB hNV'
  have hk : ((κ L' x : L'ˣ) : L') ≠ 0 := Units.ne_zero _
  have hGpos : ∀ σ : L' →+* ℂ, 0 < ‖D'.B.gramDet σ e‖ := by
    intro σ
    have hpd := (GlobalTheory.CompanionTheory.Ar.Lines.gramMat_posDef_and_conj L' D'.B D'.g e hLI).1 σ
    have h1' : D'.B.gramDet σ e = (GlobalTheory.CompanionTheory.Ar.Lines.gramMat D'.B σ e).det := rfl
    rw [h1']
    exact norm_pos_iff.mpr hpd.det_pos.ne'
  refine ⟨L', i1, i2, i3, D', x3, s, ?_⟩
  unfold GlobalTheory.CompanionTheory.Ar.Sl.PPData.HasTheta
  refine ⟨fun σ => Real.exp (Real.log ((2 * Real.pi) ^ (2 * D'.g) * ‖D'.B.gramDet σ e‖ ^ 2 /
    ‖σ ((κ L' x : L'ˣ) : L')‖) / 8), ?_, ?_⟩
  · intro σ a θ hθ
    have h13 := ((GlobalTheory.T.theta_function_archimedean_frame E H L' D' σ).2 a).2.2
    choose W hW using fun i => (h13 (e i)).1.exists
    exact KeyDeg.is_L2_of_gram_det_pos D' _ hk e σ (hGpos σ) a θ (Matrix.of W) hW
      (fun Fd hFd => GlobalTheory.T.key_degree_pp_data κ h2 hArch E H L' D' x th s hgx v e hSS hKO hLB hv σ a θ
        (Matrix.of W) Fd hθ hW hFd)
  · have hf : ∀ σ : L' →+* ℂ, Real.log (Real.exp (Real.log ((2 * Real.pi) ^ (2 * D'.g) *
          ‖D'.B.gramDet σ e‖ ^ 2 / ‖σ ((κ L' x : L'ˣ) : L')‖) / 8)) =
        2 * (D'.g : ℝ) * Real.log (2 * Real.pi) / 8 + 1 / 4 * Real.log ‖D'.B.gramDet σ e‖ -
          1 / 8 * Real.log ‖σ ((κ L' x : L'ˣ) : L')‖ := by
      intro σ
      have hσk : ‖σ ((κ L' x : L'ˣ) : L')‖ ≠ 0 := (norm_pos_iff.mpr ((map_ne_zero σ).mpr hk)).ne'
      have hG0 : ‖D'.B.gramDet σ e‖ ≠ 0 := (hGpos σ).ne'
      rw [Real.log_exp, Real.log_div (mul_ne_zero (by positivity) (pow_ne_zero 2 hG0)) hσk,
        Real.log_mul (by positivity) (pow_ne_zero 2 hG0), Real.log_pow, Real.log_pow]
      push_cast
      ring
    have hmk := KeyDeg.mean_log_nonneg ((κ L' x : L'ˣ) : L') hk hint
    have hmG := GlobalTheory.T.normalized_degree_gram_det L' D'.B D'.g e hLI hsp
    have hhp : -D'.B.normDegree ⊤ ≤ D'.hp := by
      unfold GlobalTheory.CompanionTheory.Ar.Sl.PPData.hp
      exact le_max_left _ _
    rw [hpp] at hhp
    have hl := KeyDeg.log_two_pi_le
    have hn : (0 : ℝ) < Module.finrank ℚ L' := Nat.cast_pos.mpr Module.finrank_pos
    unfold GlobalTheory.CompanionTheory.Ar.Sl.mean at hmk hmG ⊢
    simp only [hf]
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul, NumberField.Embeddings.card]
    have hS1 : (∑ σ : L' →+* ℂ, Real.log ‖D'.B.gramDet σ e‖) =
        -2 * D'.B.normDegree ⊤ * (Module.finrank ℚ L' : ℝ) := by
      have h1'' : (∑ σ : L' →+* ℂ, Real.log ‖D'.B.gramDet σ e‖) / (Module.finrank ℚ L' : ℝ) =
          -2 * D'.B.normDegree ⊤ := by linarith
      rw [div_eq_iff hn.ne'] at h1''
      exact h1''
    have hS2 : 0 ≤ ∑ σ : L' →+* ℂ, Real.log ‖σ ((κ L' x : L'ˣ) : L')‖ := by
      have h2'' := mul_nonneg hmk hn.le
      rwa [div_mul_cancel₀ _ hn.ne'] at h2''
    have hA : 2 * (D'.g : ℝ) * Real.log (2 * Real.pi) / 8 ≤ D.g := by
      have hgg' : (D'.g : ℝ) = D.g := by exact_mod_cast hgg
      rw [hgg']
      have hg0 : (0 : ℝ) ≤ D.g := Nat.cast_nonneg _
      nlinarith
    rw [div_le_iff₀ hn]
    nlinarith [mul_le_mul_of_nonneg_left hA hn.le, mul_le_mul_of_nonneg_left hhp hn.le, hS1, hS2]

end GlobalTheory.CompanionTheory.Ar.Sl
