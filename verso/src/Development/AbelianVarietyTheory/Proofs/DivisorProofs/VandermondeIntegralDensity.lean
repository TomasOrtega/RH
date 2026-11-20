import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecondChernDensity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JacobianDensityHermitianMetrics
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JacobiDensityWeightedThetaIntegralZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentTriangularFactorUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeadingMinorsUnipotentMul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetTriangularConjugateEqDiagonalRatio
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MinorsNonzeroAeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IwasawaDecompositionDifferentiableStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IwasawaJacobianDeterminantStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantBilinearTraceFormulaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaDiagonalEntryConjugateStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JacobianDensityOfTriangularStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VandermondeDensitySymmetricStatement

open Filter Topology MeasureTheory Matrix
open GlobalTheory GlobalTheory.HermFrame GlobalTheory.ArInt GlobalTheory.VdmRec GlobalTheory.ArchLim
open GlobalTheory.MixDens (emb jacDens theta)
open GlobalTheory.FlagFibre (Low uni)
open ReciprocityTheory.L2DbarEstimates (V cHess bas)
open scoped ContDiff ComplexOrder Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagMoment

variable {m : ℕ}

/- English proof (translation)
Introduce `h` and use `by have := FlagFibre.inv_diag_mul b (fun a c h => hb h) hu i rw [h, mul_zero] at this exact zero_ne_one this`.
-/
theorem diag_ne_zero {b : Matrix (Fin m) (Fin m) ℂ} (hb : b.BlockTriangular id) (hu : IsUnit b.det) (i : Fin m) :
    b i i ≠ 0 := fun h => by
  have := FlagFibre.inv_diag_mul b (fun a c h => hb h) hu i
  rw [h, mul_zero] at this
  exact zero_ne_one this

/- English proof (translation)
Rewrite using `[det_of_isUpperTriangular (M := b.submatrix (Fin.castLE l.is_le) (Fin.castLE l.is_le)) fun a c h => hb (show (Fin.castLE l.is_le c) < Fin.castLE l.is_le a from h)]`. Conclude with `Finset.prod_ne_zero_iff.2 fun i _ => diag_ne_zero hb hu _`.
-/
theorem minor_ne_zero {b : Matrix (Fin m) (Fin m) ℂ} (hb : b.BlockTriangular id) (hu : IsUnit b.det)
    (l : Fin (m + 1)) : (b.submatrix (Fin.castLE l.is_le) (Fin.castLE l.is_le)).det ≠ 0 := by
  rw [det_of_isUpperTriangular (M := b.submatrix (Fin.castLE l.is_le) (Fin.castLE l.is_le))
    fun a c h => hb (show (Fin.castLE l.is_le c) < Fin.castLE l.is_le a from h)]
  exact Finset.prod_ne_zero_iff.2 fun i _ => diag_ne_zero hb hu _

/- English proof (translation)
The claim follows from `(isUnit_iff_isUnit_det _).2 (by rw [FlagFibre.det_uni]; exact isUnit_one)`.
-/
theorem isUnit_uni (x : Low m → ℂ) : IsUnit (uni x) :=
  (isUnit_iff_isUnit_det _).2 (by rw [FlagFibre.det_uni]; exact isUnit_one)

/- English proof (translation)
Take `⟨T, hT, h1⟩` from `MixDens.NormalCoord.exists_upper_chg_eq_one (posDef_chg (isUnit_uni x) (posDef_chg ((isUnit_iff_isUnit_det _).2 hg) hG))`. Establish `hT' : (b * T).BlockTriangular id` using `hb.mul fun a c h => hT a c h`. Establish `h2 : chg (b * T) (chg (uni y) G) = 1`. Rewrite using `[chg_chg, ← Matrix.mul_assoc, ← h, ← h1, chg_chg, chg_chg, Matrix.mul_assoc]`. Rewrite using `[← GlobalTheory.T.jacobian_density_unipotent_product _ (posDef_chg ((isUnit_iff_isUnit_det _).2 hg) hG) x T hT h1, ← GlobalTheory.T.jacobian_density_unipotent_product _ hG y (b * T) (fun a c h => hT' h) h2, ← Finset.prod_mul_distrib]`.

Use `Finset.prod_congr rfl fun s _ => ?_` and prove the remaining obligations. Rewrite using `[← mul_pow, ← norm_mul, FlagFibre.diag_mul_of_upper b T (fun a c h => hb h) hT, FlagFibre.diag_mul_of_upper b T (fun a c h => hb h) hT]`. Use `diag_ne_zero hb hu s.1.1` as an intermediate fact. Use `diag_ne_zero hb hu s.1.2` as an intermediate fact. Use `congr 2`.

Distinguish the cases in `h0 : T s.1.1 s.1.1 = 0`. Simplify using `[h0]`. Clear the denominators using the available nonvanishing facts.
-/
theorem jacDens_chg {G g b : Matrix (Fin m) (Fin m) ℂ} (hG : G.PosDef) (hg : IsUnit g.det) {x y : Low m → ℂ}
    (hb : b.BlockTriangular id) (hu : IsUnit b.det) (h : g * uni x = uni y * b) :
    jacDens (chg g G) x = (∏ s : Low m, ‖b s.1.1 s.1.1 / b s.1.2 s.1.2‖ ^ 2) * jacDens G y := by
  obtain ⟨T, hT, h1⟩ := MixDens.NormalCoord.exists_upper_chg_eq_one
    (posDef_chg (isUnit_uni x) (posDef_chg ((isUnit_iff_isUnit_det _).2 hg) hG))
  have hT' : (b * T).BlockTriangular id := hb.mul fun a c h => hT a c h
  have h2 : chg (b * T) (chg (uni y) G) = 1 := by
    rw [chg_chg, ← Matrix.mul_assoc, ← h, ← h1, chg_chg, chg_chg, Matrix.mul_assoc]
  rw [← GlobalTheory.T.jacobian_density_unipotent_product _ (posDef_chg ((isUnit_iff_isUnit_det _).2 hg) hG) x T hT h1,
    ← GlobalTheory.T.jacobian_density_unipotent_product _ hG y (b * T) (fun a c h => hT' h) h2, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun s _ => ?_
  rw [← mul_pow, ← norm_mul, FlagFibre.diag_mul_of_upper b T (fun a c h => hb h) hT,
    FlagFibre.diag_mul_of_upper b T (fun a c h => hb h) hT]
  have := diag_ne_zero hb hu s.1.1
  have := diag_ne_zero hb hu s.1.2
  congr 2
  by_cases h0 : T s.1.1 s.1.1 = 0
  · simp [h0]
  · field_simp

/- English proof (translation)
Take `⟨φ, B, h⟩` from `GlobalTheory.T.iwasawa_decomposition_differentiable m g`. Take `⟨φ', B', h'⟩` from `GlobalTheory.T.iwasawa_decomposition_differentiable m g⁻¹`. Use `set s : Set (Low m → ℂ) := {x | ∀ l : Fin (m + 1), ((g * uni x).submatrix (Fin.castLE l.is_le) (Fin.castLE l.is_le)).det ≠ 0}`. Establish `hs : IsOpen s`. Simplify using `only [s, Set.ofPred_forall]`.

Conclude with `isOpen_iInter_of_finite fun l => isOpen_ne_fun ((continuous_const.matrix_mul FlagFibre.continuous_uni).matrix_submatrix _ _).matrix_det continuous_const`. Establish `hinv (b : Matrix (Fin m) (Fin m) ℂ) (hb : b.BlockTriangular id) (hu : IsUnit b.det) : b⁻¹.BlockTriangular id` using `fun a c h => FlagFibre.inv_upper b (fun a c h => hb h) hu a c h`. Establish `hinj : Set.InjOn φ s` using `fun x hx y hy e => by`. Take `⟨a1, a2, a3, -⟩` from `h x hx`. Take `⟨b1, b2, b3, -⟩` from `h y hy`.

Use `FlagCell.uniR_unique_of_mul_eq ℂ m x y (B x)⁻¹ (B y)⁻¹ (hinv _ a1 a2) (hinv _ b1 b2) (isUnit_nonsing_inv_det _ a2) ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `uni x * _ = uni y * _`. Rewrite using `[← nonsing_inv_mul_cancel_left g (uni x * _) hg, ← nonsing_inv_mul_cancel_left g (uni y * _) hg, ← Matrix.mul_assoc g, ← Matrix.mul_assoc g, a3, b3, mul_nonsing_inv_cancel_right _ _ a2, mul_nonsing_inv_cancel_right _ _ b2, e]`. Establish `hsurj : ∀ᵐ y, y ∈ φ '' s` using `by filter_upwards [T.minors_nonzero_ae m g⁻¹ (isUnit_nonsing_inv_det _ hg)] with y hy`. Take `⟨a1, a2, a3, -⟩` from `h' y hy`.

Establish `e : g * uni (φ' y) = uni y * (B' y)⁻¹`. Rewrite using `[← mul_nonsing_inv_cancel_left g (uni y * _) hg, ← Matrix.mul_assoc g⁻¹, a3, mul_nonsing_inv_cancel_right _ _ a2]`. Establish `hx : φ' y ∈ s` using `fun l => by`. Rewrite using `[e]`. Conclude with `(FlagCell.det_leading_uniR_mul ℂ m y _ (hinv _ a1 a2) l).trans_ne (minor_ne_zero (hinv _ a1 a2) (isUnit_nonsing_inv_det _ a2) l)`.

Take `⟨b1, b2, b3, -⟩` from `h _ hx`. Conclude with `⟨_, hx, FlagCell.uniR_unique_of_mul_eq ℂ m _ _ _ _ b1 (hinv _ a1 a2) b2 (b3.symm.trans e)⟩`. Establish `key` using `integral_image_eq_integral_abs_det_fderiv_smul volume hs.measurableSet (f' := fun x => (fderiv ℂ φ x).restrictScalars ℝ) (fun x hx => ((h x hx).2.2.2.1.hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt) hinj fun y => jacDens G y • Φ (uni y)`. Rewrite `key` using `[Measure.restrict_eq_self_of_ae_mem hsurj]`. Rewrite using `[key, ← Measure.restrict_eq_self_of_ae_mem (s := s) (GlobalTheory.T.minors_nonzero_ae m g hg)]`.

Rewrite using `[Measure.restrict_restrict hs.measurableSet, Set.inter_self]`. Use `setIntegral_congr_fun hs.measurableSet fun x hx => ?_` and prove the remaining obligations. Take `⟨a1, a2, a3, a4, a5⟩` from `h x hx`. Use `beta_reduce`. Rewrite using `[T.iwasawa_jacobian_determinant m g φ B x (by filter_upwards [hs.mem_nhds hx] with y hy using ⟨(h y hy).1, (h y hy).2.2.1⟩) a2 a4 a5, jacDens_chg hG hg a1 a2 a3, a3, hΦ _ _ a1 a2, smul_smul]`.
-/
theorem integral_chg {G g : Matrix (Fin m) (Fin m) ℂ} (hG : G.PosDef) (hg : IsUnit g.det)
    (Φ : Matrix (Fin m) (Fin m) ℂ → ℂ)
    (hΦ : ∀ (y : Low m → ℂ) (b : Matrix (Fin m) (Fin m) ℂ), b.BlockTriangular id → IsUnit b.det →
      Φ (uni y * b) = Φ (uni y)) :
    ∫ x, jacDens (chg g G) x • Φ (g * uni x) = ∫ y, jacDens G y • Φ (uni y) := by
  obtain ⟨φ, B, h⟩ := GlobalTheory.T.iwasawa_decomposition_differentiable m g
  obtain ⟨φ', B', h'⟩ := GlobalTheory.T.iwasawa_decomposition_differentiable m g⁻¹
  set s : Set (Low m → ℂ) := {x | ∀ l : Fin (m + 1),
    ((g * uni x).submatrix (Fin.castLE l.is_le) (Fin.castLE l.is_le)).det ≠ 0}
  have hs : IsOpen s := by
    simp only [s, Set.ofPred_forall]
    exact isOpen_iInter_of_finite fun l => isOpen_ne_fun
      ((continuous_const.matrix_mul FlagFibre.continuous_uni).matrix_submatrix _ _).matrix_det continuous_const
  have hinv (b : Matrix (Fin m) (Fin m) ℂ) (hb : b.BlockTriangular id) (hu : IsUnit b.det) :
      b⁻¹.BlockTriangular id := fun a c h => FlagFibre.inv_upper b (fun a c h => hb h) hu a c h
  have hinj : Set.InjOn φ s := fun x hx y hy e => by
    obtain ⟨a1, a2, a3, -⟩ := h x hx
    obtain ⟨b1, b2, b3, -⟩ := h y hy
    refine FlagCell.uniR_unique_of_mul_eq ℂ m x y (B x)⁻¹ (B y)⁻¹ (hinv _ a1 a2) (hinv _ b1 b2)
      (isUnit_nonsing_inv_det _ a2) ?_
    change uni x * _ = uni y * _
    rw [← nonsing_inv_mul_cancel_left g (uni x * _) hg, ← nonsing_inv_mul_cancel_left g (uni y * _) hg,
      ← Matrix.mul_assoc g, ← Matrix.mul_assoc g, a3, b3, mul_nonsing_inv_cancel_right _ _ a2,
      mul_nonsing_inv_cancel_right _ _ b2, e]
  have hsurj : ∀ᵐ y, y ∈ φ '' s := by
    filter_upwards [T.minors_nonzero_ae m g⁻¹ (isUnit_nonsing_inv_det _ hg)] with y hy
    obtain ⟨a1, a2, a3, -⟩ := h' y hy
    have e : g * uni (φ' y) = uni y * (B' y)⁻¹ := by
      rw [← mul_nonsing_inv_cancel_left g (uni y * _) hg, ← Matrix.mul_assoc g⁻¹, a3,
        mul_nonsing_inv_cancel_right _ _ a2]
    have hx : φ' y ∈ s := fun l => by
      rw [e]
      exact (FlagCell.det_leading_uniR_mul ℂ m y _ (hinv _ a1 a2) l).trans_ne
        (minor_ne_zero (hinv _ a1 a2) (isUnit_nonsing_inv_det _ a2) l)
    obtain ⟨b1, b2, b3, -⟩ := h _ hx
    exact ⟨_, hx, FlagCell.uniR_unique_of_mul_eq ℂ m _ _ _ _ b1 (hinv _ a1 a2) b2 (b3.symm.trans e)⟩
  have key := integral_image_eq_integral_abs_det_fderiv_smul volume hs.measurableSet
    (f' := fun x => (fderiv ℂ φ x).restrictScalars ℝ)
    (fun x hx => ((h x hx).2.2.2.1.hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt) hinj
    fun y => jacDens G y • Φ (uni y)
  rw [Measure.restrict_eq_self_of_ae_mem hsurj] at key
  rw [key, ← Measure.restrict_eq_self_of_ae_mem (s := s) (GlobalTheory.T.minors_nonzero_ae m g hg)]
  rw [Measure.restrict_restrict hs.measurableSet, Set.inter_self]
  refine setIntegral_congr_fun hs.measurableSet fun x hx => ?_
  obtain ⟨a1, a2, a3, a4, a5⟩ := h x hx
  beta_reduce
  rw [T.iwasawa_jacobian_determinant m g φ B x (by
    filter_upwards [hs.mem_nhds hx] with y hy using ⟨(h y hy).1, (h y hy).2.2.1⟩) a2 a4 a5,
    jacDens_chg hG hg a1 a2 a3, a3, hΦ _ _ a1 a2, smul_smul]

def diagEntry (G F : Matrix (Fin m) (Fin m) ℂ) (x : Low m → ℂ) (i : Fin m) : ℂ :=
  theta G (-(Fᵀ * G)) x i + Complex.I * theta G (-(((-Complex.I) • F)ᵀ * G)) x i

/- English proof (translation)
Rewrite using `[diagEntry, GlobalTheory.T.theta_diagonal_entry_conjugate G F x T hT h1, GlobalTheory.T.theta_diagonal_entry_conjugate G _ x T hT h1, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply]`. Apply the tactic sequence `apply Complex.ext <;> simp`.
-/
theorem diagEntry_eq {G T : Matrix (Fin m) (Fin m) ℂ} {x : Low m → ℂ} (hT : ∀ a c : Fin m, c < a → T a c = 0)
    (h1 : chg T (chg (uni x) G) = 1) (F : Matrix (Fin m) (Fin m) ℂ) (i : Fin m) :
    diagEntry G F x i = ((uni x * T)⁻¹ * F * (uni x * T)) i i := by
  rw [diagEntry, GlobalTheory.T.theta_diagonal_entry_conjugate G F x T hT h1, GlobalTheory.T.theta_diagonal_entry_conjugate G _ x T hT h1, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.smul_apply]
  apply Complex.ext <;> simp

/- English proof (translation)
The claim follows from `(Complex.measurable_ofReal.comp ((MixDens.Canon.measurable_logMinorDer _ _ _).sub (MixDens.Canon.measurable_logMinorDer _ _ _))).add ((Complex.measurable_ofReal.comp ((MixDens.Canon.measurable_logMinorDer _ _ _).sub (MixDens.Canon.measurable_logMinorDer _ _ _))).const_mul _)`.
-/
theorem measurable_diagEntry (G F : Matrix (Fin m) (Fin m) ℂ) (i : Fin m) : Measurable fun x => diagEntry G F x i :=
  (Complex.measurable_ofReal.comp ((MixDens.Canon.measurable_logMinorDer _ _ _).sub
    (MixDens.Canon.measurable_logMinorDer _ _ _))).add ((Complex.measurable_ofReal.comp
      ((MixDens.Canon.measurable_logMinorDer _ _ _).sub (MixDens.Canon.measurable_logMinorDer _ _ _))).const_mul _)

/- English proof (translation)
Use `congrArg transpose h` as an intermediate fact. Rewrite `this` using `[chg, Matrix.mul_one, transpose_mul, transpose_transpose, transpose_transpose, transpose_one]`. Then use the resulting hypothesis.
-/
theorem unitary_of_chg {u : Matrix (Fin m) (Fin m) ℂ} (h : chg u 1 = 1) : uᴴ * u = 1 := by
  have := congrArg transpose h
  rwa [chg, Matrix.mul_one, transpose_mul, transpose_transpose, transpose_transpose, transpose_one] at this

/- English proof (translation)
Establish `h` using `congrArg Matrix.det h`. Rewrite `h` using `[det_chg, det_one]`. Establish `: R.det ≠ 0` using `fun h0 => by rw [h0] at h; simp at h`. Conclude with `this.isUnit`.
-/
theorem isUnit_of_chg {R G : Matrix (Fin m) (Fin m) ℂ} (h : chg R G = 1) : IsUnit R.det := by
  have h := congrArg Matrix.det h
  rw [det_chg, det_one] at h
  have : R.det ≠ 0 := fun h0 => by rw [h0] at h; simp at h
  exact this.isUnit

/- English proof (translation)
Take `⟨T, hT, h1⟩` from `MixDens.NormalCoord.exists_upper_chg_eq_one (posDef_chg (isUnit_uni x) hG)`. Establish `hu` using `isUnit_of_chg hR`. Establish `h2 : (R⁻¹ * (uni x * T))ᴴ * (R⁻¹ * (uni x * T)) = 1` using `unitary_of_chg (by`. Rewrite using `[← hR, chg_chg, mul_nonsing_inv_cancel_left _ _ hu, hR, ← chg_chg, h1])`. Use `⟨_, h2, fun F i => ?_⟩` and prove the remaining obligations.

Rewrite using `[diagEntry_eq hT h1, ← inv_eq_left_inv h2, Matrix.mul_inv_rev R⁻¹, nonsing_inv_nonsing_inv _ hu]`. Simplify using `only [Matrix.mul_assoc, mul_nonsing_inv_cancel_left _ _ hu]`.
-/
theorem exists_unitary {G R : Matrix (Fin m) (Fin m) ℂ} (hG : G.PosDef) (hR : chg R G = 1) (x : Low m → ℂ) :
    ∃ u : Matrix (Fin m) (Fin m) ℂ, uᴴ * u = 1 ∧ ∀ F i, diagEntry G F x i = (uᴴ * (R⁻¹ * F * R) * u) i i := by
  obtain ⟨T, hT, h1⟩ := MixDens.NormalCoord.exists_upper_chg_eq_one (posDef_chg (isUnit_uni x) hG)
  have hu := isUnit_of_chg hR
  have h2 : (R⁻¹ * (uni x * T))ᴴ * (R⁻¹ * (uni x * T)) = 1 := unitary_of_chg (by
    rw [← hR, chg_chg, mul_nonsing_inv_cancel_left _ _ hu, hR, ← chg_chg, h1])
  refine ⟨_, h2, fun F i => ?_⟩
  rw [diagEntry_eq hT h1, ← inv_eq_left_inv h2, Matrix.mul_inv_rev R⁻¹, nonsing_inv_nonsing_inv _ hu]
  simp only [Matrix.mul_assoc, mul_nonsing_inv_cancel_left _ _ hu]

/- English proof (translation)
Take `⟨T, hT, h1⟩` from `MixDens.NormalCoord.exists_upper_chg_eq_one (posDef_chg (isUnit_uni x) hG)`. Simplify using `only [diagEntry_eq hT h1]`. Rewrite `h1` using `[chg_chg]`. Express the relevant statement in the definitionally equal form `((uni x * T)⁻¹ * F * (uni x * T)).trace = _`. Rewrite using `[trace_mul_cycle, mul_nonsing_inv _ (isUnit_of_chg h1), Matrix.one_mul]`.
-/
theorem sum_diagEntry {G : Matrix (Fin m) (Fin m) ℂ} (hG : G.PosDef) (F : Matrix (Fin m) (Fin m) ℂ) (x : Low m → ℂ) :
    ∑ i, diagEntry G F x i = F.trace := by
  obtain ⟨T, hT, h1⟩ := MixDens.NormalCoord.exists_upper_chg_eq_one (posDef_chg (isUnit_uni x) hG)
  simp only [diagEntry_eq hT h1]
  rw [chg_chg] at h1
  change ((uni x * T)⁻¹ * F * (uni x * T)).trace = _
  rw [trace_mul_cycle, mul_nonsing_inv _ (isUnit_of_chg h1), Matrix.one_mul]

/- English proof (translation)
Take `⟨R, -, hR⟩` from `MixDens.NormalCoord.exists_upper_chg_eq_one hG`. Use `⟨∑ b, ∑ a, ‖(R⁻¹ * F * R) a b‖, fun x i => ?_⟩` and prove the remaining obligations. Take `⟨u, hu, h⟩` from `exists_unitary hG hR x`. Establish `hb (a c) : ‖u a c‖ ≤ 1` using `entry_norm_bound_of_unitary (mem_unitaryGroup_iff'.2 hu) a c`. Rewrite using `[h, mul_apply]`.

Use `norm_sum_le_of_le _ fun b _ => ?_` and prove the remaining obligations. Rewrite using `[norm_mul]`. Use `(mul_le_of_le_one_right (norm_nonneg _) (hb _ _)).trans ?_` and prove the remaining obligations. Rewrite using `[mul_apply]`. Use `norm_sum_le_of_le _ fun a _ => ?_` and prove the remaining obligations.

Rewrite using `[norm_mul, conjTranspose_apply, norm_star]`. Conclude with `mul_le_of_le_one_left (norm_nonneg _) (hb _ _)`.
-/
theorem exists_bound {G : Matrix (Fin m) (Fin m) ℂ} (hG : G.PosDef) (F : Matrix (Fin m) (Fin m) ℂ) :
    ∃ C : ℝ, ∀ x i, ‖diagEntry G F x i‖ ≤ C := by
  obtain ⟨R, -, hR⟩ := MixDens.NormalCoord.exists_upper_chg_eq_one hG
  refine ⟨∑ b, ∑ a, ‖(R⁻¹ * F * R) a b‖, fun x i => ?_⟩
  obtain ⟨u, hu, h⟩ := exists_unitary hG hR x
  have hb (a c) : ‖u a c‖ ≤ 1 := entry_norm_bound_of_unitary (mem_unitaryGroup_iff'.2 hu) a c
  rw [h, mul_apply]
  refine norm_sum_le_of_le _ fun b _ => ?_
  rw [norm_mul]
  refine (mul_le_of_le_one_right (norm_nonneg _) (hb _ _)).trans ?_
  rw [mul_apply]
  refine norm_sum_le_of_le _ fun a _ => ?_
  rw [norm_mul, conjTranspose_apply, norm_star]
  exact mul_le_of_le_one_left (norm_nonneg _) (hb _ _)

def sq (G F F' : Matrix (Fin m) (Fin m) ℂ) (x : Low m → ℂ) : ℂ := ∑ i, diagEntry G F x i * diagEntry G F' x i

/- English proof (translation)
Take `⟨C, hC⟩` from `exists_bound hG F`. Take `⟨C', hC'⟩` from `exists_bound hG F'`. Simplify using `only [Complex.real_smul]`. Apply the tactic sequence `refine (MixDens.Canon.integrable_jacDens hG).ofReal.mul_bdd (c := ∑ _i : Fin m, C * C') (Finset.measurable_sum _ fun i _ => (measurable_diagEntry G F i).mul (measurable_diagEntry G F' i)).aestronglyMeasurable (.of_forall fun x => ?_)`. Use `norm_sum_le_of_le _ fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[norm_mul]`. Conclude with `mul_le_mul (hC x i) (hC' x i) (norm_nonneg _) ((norm_nonneg _).trans (hC x i))`.
-/
theorem integrable_sq {G : Matrix (Fin m) (Fin m) ℂ} (hG : G.PosDef) (F F' : Matrix (Fin m) (Fin m) ℂ) :
    Integrable fun x => jacDens G x • sq G F F' x := by
  obtain ⟨C, hC⟩ := exists_bound hG F
  obtain ⟨C', hC'⟩ := exists_bound hG F'
  simp only [Complex.real_smul]
  refine (MixDens.Canon.integrable_jacDens hG).ofReal.mul_bdd (c := ∑ _i : Fin m, C * C')
    (Finset.measurable_sum _ fun i _ => (measurable_diagEntry G F i).mul
      (measurable_diagEntry G F' i)).aestronglyMeasurable (.of_forall fun x => ?_)
  refine norm_sum_le_of_le _ fun i _ => ?_
  rw [norm_mul]
  exact mul_le_mul (hC x i) (hC' x i) (norm_nonneg _) ((norm_nonneg _).trans (hC x i))

/- English proof (translation)
Establish `ex (M : Matrix (Fin m) (Fin m) ℂ) : ∃ T : Matrix (Fin m) (Fin m) ℂ, IsUnit M → (∀ a c : Fin m, c < a → T a c = 0) ∧ chg T (chg M G) = 1`. Distinguish the cases in `h : IsUnit M`. Take `⟨T, hT⟩` from `MixDens.NormalCoord.exists_upper_chg_eq_one (posDef_chg h hG)`. Conclude with `⟨T, fun _ => hT⟩`. Conclude with `⟨0, fun h' => (h h').elim⟩`.

Use `choose T hT using ex`. Set `Φ (M : Matrix (Fin m) (Fin m) ℂ) : ℂ` to `∑ i, ((M * T M)⁻¹ * F * (M * T M)) i i * ((M * T M)⁻¹ * F' * (M * T M)) i i`. Establish `h1 (y : Low m → ℂ) (b : Matrix (Fin m) (Fin m) ℂ) (hb : b.BlockTriangular id) (hu : IsUnit b.det) : Φ (uni y * b) = sq G F F' y`. Take `⟨a1, a2⟩` from `hT _ ((isUnit_uni y).mul ((isUnit_iff_isUnit_det _).2 hu))`. Establish `a3 : (b * T (uni y * b)).BlockTriangular id` using `hb.mul fun a c h => a1 a c h`.

Establish `a4 : chg (b * T (uni y * b)) (chg (uni y) G) = 1`. Rewrite using `[← a2, chg_chg, chg_chg, Matrix.mul_assoc]`. Simplify using `only [Φ, sq, diagEntry_eq (fun a c h => a3 h) a4, Matrix.mul_assoc]`. Establish `h2 (y : Low m → ℂ) : Φ (uni y) = sq G F F' y`. Rewrite using `[← h1 y 1 blockTriangular_one (by simp), Matrix.mul_one]`.

Establish `h3 (x : Low m → ℂ) : Φ (g * uni x) = sq (chg g G) (g⁻¹ * F * g) (g⁻¹ * F' * g) x`. Take `⟨a1, a2⟩` from `hT _ (((isUnit_iff_isUnit_det _).2 hg).mul (isUnit_uni x))`. Rewrite `a2` using `[← chg_chg]`. Simplify using `only [Φ, sq, diagEntry_eq a1 a2, Matrix.mul_assoc, Matrix.mul_inv_rev g]`. Simplify `integral_chg hG hg Φ fun y b hb hu => (h1 y b hb hu).trans (h2 y).symm` using `only [h2, h3]`.
-/
theorem integral_sq_chg {G g : Matrix (Fin m) (Fin m) ℂ} (hG : G.PosDef) (hg : IsUnit g.det)
    (F F' : Matrix (Fin m) (Fin m) ℂ) :
    ∫ x, jacDens (chg g G) x • sq (chg g G) (g⁻¹ * F * g) (g⁻¹ * F' * g) x = ∫ y, jacDens G y • sq G F F' y := by
  have ex (M : Matrix (Fin m) (Fin m) ℂ) : ∃ T : Matrix (Fin m) (Fin m) ℂ, IsUnit M →
      (∀ a c : Fin m, c < a → T a c = 0) ∧ chg T (chg M G) = 1 := by
    by_cases h : IsUnit M
    · obtain ⟨T, hT⟩ := MixDens.NormalCoord.exists_upper_chg_eq_one (posDef_chg h hG)
      exact ⟨T, fun _ => hT⟩
    · exact ⟨0, fun h' => (h h').elim⟩
  choose T hT using ex
  let Φ (M : Matrix (Fin m) (Fin m) ℂ) : ℂ :=
    ∑ i, ((M * T M)⁻¹ * F * (M * T M)) i i * ((M * T M)⁻¹ * F' * (M * T M)) i i
  have h1 (y : Low m → ℂ) (b : Matrix (Fin m) (Fin m) ℂ) (hb : b.BlockTriangular id) (hu : IsUnit b.det) :
      Φ (uni y * b) = sq G F F' y := by
    obtain ⟨a1, a2⟩ := hT _ ((isUnit_uni y).mul ((isUnit_iff_isUnit_det _).2 hu))
    have a3 : (b * T (uni y * b)).BlockTriangular id := hb.mul fun a c h => a1 a c h
    have a4 : chg (b * T (uni y * b)) (chg (uni y) G) = 1 := by
      rw [← a2, chg_chg, chg_chg, Matrix.mul_assoc]
    simp only [Φ, sq, diagEntry_eq (fun a c h => a3 h) a4, Matrix.mul_assoc]
  have h2 (y : Low m → ℂ) : Φ (uni y) = sq G F F' y := by
    rw [← h1 y 1 blockTriangular_one (by simp), Matrix.mul_one]
  have h3 (x : Low m → ℂ) : Φ (g * uni x) = sq (chg g G) (g⁻¹ * F * g) (g⁻¹ * F' * g) x := by
    obtain ⟨a1, a2⟩ := hT _ (((isUnit_iff_isUnit_det _).2 hg).mul (isUnit_uni x))
    rw [← chg_chg] at a2
    simp only [Φ, sq, diagEntry_eq a1 a2, Matrix.mul_assoc, Matrix.mul_inv_rev g]
  simpa only [h2, h3] using integral_chg hG hg Φ fun y b hb hu => (h1 y b hb hu).trans (h2 y).symm

/- English proof (translation)
Establish `h1 : (1 : Matrix (Fin m) (Fin m) ℂ).PosDef` using `PosDef.one`. Establish `c1 : chg (1 : Matrix (Fin m) (Fin m) ℂ) 1 = 1` using `by simp [chg]`. Use `choose u hu h using exists_unitary h1 c1`. Simplify using `only [inv_one, Matrix.one_mul, Matrix.mul_one] at h`. Set `B : Matrix (Fin m) (Fin m) ℂ →ₗ[ℂ] Matrix (Fin m) (Fin m) ℂ →ₗ[ℂ] ℂ` to `LinearMap.mk₂ ℂ (fun F F' => ∫ x, jacDens 1 x • sq 1 F F' x) (fun F₁ F₂ F' => by`.

Rewrite using `[← integral_add (integrable_sq h1 _ _) (integrable_sq h1 _ _)]`. Simplify using `only [sq, h, Matrix.mul_add, Matrix.add_mul, Matrix.add_apply, add_mul, Finset.sum_add_distrib, smul_add])`. Use the proof step `(fun c F F' => by`. Rewrite using `[← integral_smul]`. Simplify using `only [sq, h, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum, mul_smul_comm])`.

Use the proof step `(fun F F₁ F₂ => by`. Rewrite using `[← integral_add (integrable_sq h1 _ _) (integrable_sq h1 _ _)]`. Simplify using `only [sq, h, Matrix.mul_add, Matrix.add_mul, Matrix.add_apply, mul_add, Finset.sum_add_distrib, smul_add])`. Use the proof step `(fun c F F' => by`. Rewrite using `[← integral_smul]`.

Simplify using `only [sq, h, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul, mul_left_comm _ c, ← Finset.mul_sum, mul_smul_comm])`. Establish `key` using `GlobalTheory.T.invariant_bilinear_trace_formula m B ((1 / TrueCx.flagConst m : ℝ) : ℂ) (fun U hU F F' => by`. Establish `e : chg U 1 = 1`. Use `congrArg transpose hU` as an intermediate fact. Rewrite `this` using `[transpose_mul, transpose_one, ← Matrix.mul_one Uᵀ]`. Then use the resulting hypothesis.

Use `integral_sq_chg h1 (isUnit_of_chg e) F F'` as an intermediate fact. Rewrite using `[e, inv_eq_left_inv hU] at this)` and apply the resulting hypothesis. Use the proof step `(fun a b c d => by`. Establish `e (x) (a b i : Fin m) : ((u x)ᴴ * Matrix.single a b (1 : ℂ) * u x : Matrix (Fin m) (Fin m) ℂ) i i = star (u x a i) * u x b i`. Simplify using `[mul_apply, Matrix.single_apply, ite_and]`.

Use `integral_congr_ae (.of_forall fun x => ?_)` and prove the remaining obligations. Simplify using `only [sq, h, e]`. Use `congr 1`. Conclude with `Finset.sum_congr rfl fun i _ => by ring)`. Use the proof step `(fun F => by`.

Express the relevant statement in the definitionally equal form `∫ x, jacDens 1 x • sq 1 1 F x = _`. Establish `e (x) : sq 1 1 F x = F.trace`. Apply the tactic sequence `rw [← sum_diagEntry h1 F x]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[h x 1, Matrix.mul_one, hu, one_apply_eq, one_mul]`.

Simplify using `only [e]`. Rewrite using `[integral_smul_const, MixDens.Canon.integral_jacDens_eq h1, Complex.real_smul])`. Take `⟨R, -, hR⟩` from `MixDens.NormalCoord.exists_upper_chg_eq_one hG`. Establish `hRu` using `isUnit_of_chg hR`. Establish `t (X : Matrix (Fin m) (Fin m) ℂ) : (R⁻¹ * X * R).trace = X.trace`.

Rewrite using `[trace_mul_cycle, mul_nonsing_inv _ hRu, Matrix.one_mul]`. Rewrite using `[← integral_sq_chg hG hRu, hR]`. Use `(key _ _).trans ?_` and prove the remaining obligations. Rewrite using `[t, t, ← t (F * F')]`. Simplify using `only [Matrix.mul_assoc, mul_nonsing_inv_cancel_left _ _ hRu]`.
-/
theorem integral_sq {G : Matrix (Fin m) (Fin m) ℂ} (hG : G.PosDef) (F F' : Matrix (Fin m) (Fin m) ℂ) :
    ∫ x, jacDens G x • sq G F F' x =
      ((1 / TrueCx.flagConst m : ℝ) : ℂ) / (m + 1) * (F.trace * F'.trace + (F * F').trace) := by
  have h1 : (1 : Matrix (Fin m) (Fin m) ℂ).PosDef := PosDef.one
  have c1 : chg (1 : Matrix (Fin m) (Fin m) ℂ) 1 = 1 := by simp [chg]
  choose u hu h using exists_unitary h1 c1
  simp only [inv_one, Matrix.one_mul, Matrix.mul_one] at h
  let B : Matrix (Fin m) (Fin m) ℂ →ₗ[ℂ] Matrix (Fin m) (Fin m) ℂ →ₗ[ℂ] ℂ :=
    LinearMap.mk₂ ℂ (fun F F' => ∫ x, jacDens 1 x • sq 1 F F' x)
      (fun F₁ F₂ F' => by
        rw [← integral_add (integrable_sq h1 _ _) (integrable_sq h1 _ _)]
        simp only [sq, h, Matrix.mul_add, Matrix.add_mul, Matrix.add_apply, add_mul, Finset.sum_add_distrib, smul_add])
      (fun c F F' => by
        rw [← integral_smul]
        simp only [sq, h, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul, mul_assoc,
          ← Finset.mul_sum, mul_smul_comm])
      (fun F F₁ F₂ => by
        rw [← integral_add (integrable_sq h1 _ _) (integrable_sq h1 _ _)]
        simp only [sq, h, Matrix.mul_add, Matrix.add_mul, Matrix.add_apply, mul_add, Finset.sum_add_distrib, smul_add])
      (fun c F F' => by
        rw [← integral_smul]
        simp only [sq, h, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul, mul_left_comm _ c,
          ← Finset.mul_sum, mul_smul_comm])
  have key := GlobalTheory.T.invariant_bilinear_trace_formula m B ((1 / TrueCx.flagConst m : ℝ) : ℂ) (fun U hU F F' => by
      have e : chg U 1 = 1 := by
        have := congrArg transpose hU
        rwa [transpose_mul, transpose_one, ← Matrix.mul_one Uᵀ] at this
      have := integral_sq_chg h1 (isUnit_of_chg e) F F'
      rwa [e, inv_eq_left_inv hU] at this)
    (fun a b c d => by
      have e (x) (a b i : Fin m) : ((u x)ᴴ * Matrix.single a b (1 : ℂ) * u x : Matrix (Fin m) (Fin m) ℂ) i i = star (u x a i) * u x b i := by
        simp [mul_apply, Matrix.single_apply, ite_and]
      refine integral_congr_ae (.of_forall fun x => ?_)
      simp only [sq, h, e]
      congr 1
      exact Finset.sum_congr rfl fun i _ => by ring)
    (fun F => by
      change ∫ x, jacDens 1 x • sq 1 1 F x = _
      have e (x) : sq 1 1 F x = F.trace := by
        rw [← sum_diagEntry h1 F x]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [h x 1, Matrix.mul_one, hu, one_apply_eq, one_mul]
      simp only [e]
      rw [integral_smul_const, MixDens.Canon.integral_jacDens_eq h1, Complex.real_smul])
  obtain ⟨R, -, hR⟩ := MixDens.NormalCoord.exists_upper_chg_eq_one hG
  have hRu := isUnit_of_chg hR
  have t (X : Matrix (Fin m) (Fin m) ℂ) : (R⁻¹ * X * R).trace = X.trace := by
    rw [trace_mul_cycle, mul_nonsing_inv _ hRu, Matrix.one_mul]
  rw [← integral_sq_chg hG hRu, hR]
  refine (key _ _).trans ?_
  rw [t, t, ← t (F * F')]
  simp only [Matrix.mul_assoc, mul_nonsing_inv_cancel_left _ _ hRu]

/- English proof (translation)
Set `F (j l : Fin (e + 2))` to `curv G u (bas _ j) (bas _ l)`. Set `f (s t : Equiv.Perm (Fin (e + 2))) : ℂ` to `((Equiv.Perm.sign s * Equiv.Perm.sign t : ℤˣ) : ℤ) * ((F (s 0) (t 0) * F (s 1) (t 1)).trace * ∏ p : Fin e, A (s p.succ.succ) (t p.succ.succ))`. Set `g (s t : Equiv.Perm (Fin (e + 2))) : ℂ` to `((Equiv.Perm.sign s * Equiv.Perm.sign t : ℤˣ) : ℤ) * ((F (s 0) (t 1) * F (s 1) (t 0)).trace * ∏ p : Fin e, A (s p.succ.succ) (t p.succ.succ))`. Establish `hw (a b c d : Fin (e + 2)) : chTwo G u (bas _ a) (bas _ b) (bas _ c) (bas _ d) = kappa ^ 2 * ((F a b * F c d).trace - (F a d * F c b).trace)`. Establish `t1 (X Y : Matrix (Fin r) (Fin r) ℂ) : ∑ i, ∑ j, X i j * Y j i = (X * Y).trace`.

Simplify using `only [trace, diag_apply, mul_apply]`. Simplify using `only [chTwo, wedge, Finset.sum_add_distrib, Finset.sum_sub_distrib, t1]`. Rewrite using `[trace_mul_comm (curv G u (bas _ c) (bas _ d)), trace_mul_comm (curv G u (bas _ c) (bas _ b))]`. Expand and normalize the polynomial expressions, which then agree. Establish `hg (s) : ∑ t, g s t = -∑ t, f s t`.

Rewrite using `[← Finset.sum_neg_distrib, ← Equiv.sum_comp (Equiv.mulRight (Equiv.swap 0 1))]`. Use `Finset.sum_congr rfl fun t _ => ?_` and prove the remaining obligations. Establish `h2 (p : Fin e) : Equiv.swap (0 : Fin (e + 2)) 1 p.succ.succ = p.succ.succ` using `Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero _) (Fin.succ_succ_ne_one p)`. Simplify using `[f, g, h2]`. Establish `hf : ∑ σ : Equiv.Perm (Fin (e + 2)), ∑ t : Equiv.Perm (Fin (e + 2)), ((Equiv.Perm.sign σ : ℤ) : ℂ) * ((F (σ (t 0)) (t 0) * F (σ (t 1)) (t 1)).trace * ∏ p : Fin e, A (σ (t p.succ.succ)) (t p.succ.succ)) = ∑ s, ∑ t, f s t`.

Rewrite using `[Finset.sum_comm, Finset.sum_comm (f := f)]`. Use `Finset.sum_congr rfl fun t _ => ?_` and prove the remaining obligations. Rewrite using `[← Equiv.sum_comp (Equiv.mulRight t) (f · t)]`. Use `Finset.sum_congr rfl fun s _ => ?_` and prove the remaining obligations. Apply the tactic sequence `rcases Int.units_eq_one_or (Equiv.Perm.sign t) with h | h <;> simp [f, mul_assoc, h]`.

Establish `hk : kappa ^ 2 = ((-(1 / (4 * Real.pi ^ 2)) : ℝ) : ℂ)`. Rewrite using `[kappa, div_pow, Complex.I_sq]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `: ∑ s : Equiv.Perm (Fin (e + 2)), ∑ t : Equiv.Perm (Fin (e + 2)), ((Equiv.Perm.sign s * Equiv.Perm.sign t : ℤˣ) : ℤ) * (chTwo G u (bas _ (s 0)) (bas _ (t 0)) (bas _ (s 1)) (bas _ (t 1)) * ∏ i : Fin e, A (s i.succ.succ) (t i.succ.succ)) = ((-(1 / (2 * Real.pi ^ 2)) : ℝ) : ℂ) * ∑ s …`.

Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun s _ => ?_` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[secondChernDensity, this, hf, Complex.re_ofReal_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem dens22_chTwo {r e : ℕ} (G : V (e + 2) → Matrix (Fin r) (Fin r) ℂ) (u : V (e + 2))
    (A : Matrix (Fin (e + 2)) (Fin (e + 2)) ℂ) :
    secondChernDensity e (chTwo G u) A = (∑ σ : Equiv.Perm (Fin (e + 2)), ∑ t : Equiv.Perm (Fin (e + 2)),
      ((Equiv.Perm.sign σ : ℤ) : ℂ) * ((curv G u (bas _ (σ (t 0))) (bas _ (t 0)) *
        curv G u (bas _ (σ (t 1))) (bas _ (t 1))).trace * ∏ p : Fin e, A (σ (t p.succ.succ)) (t p.succ.succ))).re /
      (2 * Real.pi ^ 2 * Real.pi ^ e) := by
  let F (j l : Fin (e + 2)) := curv G u (bas _ j) (bas _ l)
  let f (s t : Equiv.Perm (Fin (e + 2))) : ℂ := ((Equiv.Perm.sign s * Equiv.Perm.sign t : ℤˣ) : ℤ) *
    ((F (s 0) (t 0) * F (s 1) (t 1)).trace * ∏ p : Fin e, A (s p.succ.succ) (t p.succ.succ))
  let g (s t : Equiv.Perm (Fin (e + 2))) : ℂ := ((Equiv.Perm.sign s * Equiv.Perm.sign t : ℤˣ) : ℤ) *
    ((F (s 0) (t 1) * F (s 1) (t 0)).trace * ∏ p : Fin e, A (s p.succ.succ) (t p.succ.succ))
  have hw (a b c d : Fin (e + 2)) : chTwo G u (bas _ a) (bas _ b) (bas _ c) (bas _ d) =
      kappa ^ 2 * ((F a b * F c d).trace - (F a d * F c b).trace) := by
    have t1 (X Y : Matrix (Fin r) (Fin r) ℂ) : ∑ i, ∑ j, X i j * Y j i = (X * Y).trace := by
      simp only [trace, diag_apply, mul_apply]
    simp only [chTwo, wedge, Finset.sum_add_distrib, Finset.sum_sub_distrib, t1]
    rw [trace_mul_comm (curv G u (bas _ c) (bas _ d)), trace_mul_comm (curv G u (bas _ c) (bas _ b))]
    ring
  have hg (s) : ∑ t, g s t = -∑ t, f s t := by
    rw [← Finset.sum_neg_distrib, ← Equiv.sum_comp (Equiv.mulRight (Equiv.swap 0 1))]
    refine Finset.sum_congr rfl fun t _ => ?_
    have h2 (p : Fin e) : Equiv.swap (0 : Fin (e + 2)) 1 p.succ.succ = p.succ.succ :=
      Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero _) (Fin.succ_succ_ne_one p)
    simp [f, g, h2]
  have hf : ∑ σ : Equiv.Perm (Fin (e + 2)), ∑ t : Equiv.Perm (Fin (e + 2)),
      ((Equiv.Perm.sign σ : ℤ) : ℂ) * ((F (σ (t 0)) (t 0) * F (σ (t 1)) (t 1)).trace *
        ∏ p : Fin e, A (σ (t p.succ.succ)) (t p.succ.succ)) = ∑ s, ∑ t, f s t := by
    rw [Finset.sum_comm, Finset.sum_comm (f := f)]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [← Equiv.sum_comp (Equiv.mulRight t) (f · t)]
    refine Finset.sum_congr rfl fun s _ => ?_
    rcases Int.units_eq_one_or (Equiv.Perm.sign t) with h | h <;> simp [f, mul_assoc, h]
  have hk : kappa ^ 2 = ((-(1 / (4 * Real.pi ^ 2)) : ℝ) : ℂ) := by
    rw [kappa, div_pow, Complex.I_sq]; push_cast; ring
  have : ∑ s : Equiv.Perm (Fin (e + 2)), ∑ t : Equiv.Perm (Fin (e + 2)),
    ((Equiv.Perm.sign s * Equiv.Perm.sign t : ℤˣ) : ℤ) *
      (chTwo G u (bas _ (s 0)) (bas _ (t 0)) (bas _ (s 1)) (bas _ (t 1)) *
        ∏ i : Fin e, A (s i.succ.succ) (t i.succ.succ)) =
      ((-(1 / (2 * Real.pi ^ 2)) : ℝ) : ℂ) * ∑ s, ∑ t, f s t := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    calc _ = ∑ t, kappa ^ 2 * (f s t - g s t) := Finset.sum_congr rfl fun t _ => by rw [hw]; simp only [f, g]; ring
      _ = _ := by rw [← Finset.mul_sum, Finset.sum_sub_distrib, hg, hk]; push_cast; ring
  rw [secondChernDensity, this, hf, Complex.re_ofReal_mul]
  ring

/- English proof (translation)
Establish `e : ∑ o, a o • H o = chg J ((fromBlocks (∑ o, a o • M o) 0 0 (diagonal fun s : Low r => a (some s.1.1) - a (some s.1.2))).submatrix ε ε)`. Rewrite using `[Fintype.sum_option]`. Establish `c1 (z : ℂ) (X : Matrix (Fin D) (Fin D) ℂ) : z • chg J X = chg J (z • X)` using `by simp [chg]`. Establish `c2 (X Y : Matrix (Fin D) (Fin D) ℂ) : chg J X + chg J Y = chg J (X + Y)`. Simplify using `[chg, Matrix.mul_add, Matrix.add_mul]`.

Establish `c3 (X : Fin r → Matrix (Fin D) (Fin D) ℂ) : ∑ i, chg J (X i) = chg J (∑ i, X i)`. Simplify using `[chg, Matrix.mul_sum, Matrix.sum_mul]`. Simplify using `only [h₀, h₁, c1, c3, c2]`. Use `congr 1`. Use extensionality with `j l`.

Simplify using `only [Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply, submatrix_apply, Fintype.sum_option]`. Apply the tactic sequence `rcases ε j with x | x <;> rcases ε l with y | y`. Simplify using `[Matrix.sum_apply]`. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.

Apply the tactic sequence `by_cases h : x = y <;> simp [diagonal_apply, h, mul_sub]`. Rewrite using `[e, det_chg, det_submatrix_equiv_self, det_fromBlocks_zero₂₁, det_diagonal, det_apply' (∑ o, a o • M o), Finset.sum_mul]`. Simplify using `only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, mul_assoc]`.
-/
theorem det_sum_chg {n D r : ℕ} (ε : Fin D ≃ Fin n ⊕ Low r) (J : Matrix (Fin D) (Fin D) ℂ)
    (M : Option (Fin r) → Matrix (Fin n) (Fin n) ℂ) (a : Option (Fin r) → ℂ)
    (H : Option (Fin r) → Matrix (Fin D) (Fin D) ℂ)
    (h₀ : H none = chg J ((fromBlocks (M none) 0 0 (0 : Matrix (Low r) (Low r) ℂ)).submatrix ε ε))
    (h₁ : ∀ i, H (some i) = chg J ((fromBlocks (M (some i)) 0 0 (diagonal fun s : Low r =>
      ((if i = s.1.1 then 1 else 0) - if i = s.1.2 then 1 else 0 : ℂ))).submatrix ε ε)) :
    (∑ o, a o • H o).det = ((‖J.det‖ ^ 2 : ℝ) : ℂ) * ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℂ) *
      ((∏ k, ∑ o, a o * M o (σ k) k) * ∏ s : Low r, (a (some s.1.1) - a (some s.1.2))) := by
  have e : ∑ o, a o • H o = chg J ((fromBlocks (∑ o, a o • M o) 0 0
      (diagonal fun s : Low r => a (some s.1.1) - a (some s.1.2))).submatrix ε ε) := by
    rw [Fintype.sum_option]
    have c1 (z : ℂ) (X : Matrix (Fin D) (Fin D) ℂ) : z • chg J X = chg J (z • X) := by simp [chg]
    have c2 (X Y : Matrix (Fin D) (Fin D) ℂ) : chg J X + chg J Y = chg J (X + Y) := by
      simp [chg, Matrix.mul_add, Matrix.add_mul]
    have c3 (X : Fin r → Matrix (Fin D) (Fin D) ℂ) : ∑ i, chg J (X i) = chg J (∑ i, X i) := by
      simp [chg, Matrix.mul_sum, Matrix.sum_mul]
    simp only [h₀, h₁, c1, c3, c2]
    congr 1
    ext j l
    simp only [Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply, submatrix_apply, Fintype.sum_option]
    rcases ε j with x | x <;> rcases ε l with y | y
    · simp [Matrix.sum_apply]
    · simp
    · simp
    · by_cases h : x = y <;> simp [diagonal_apply, h, mul_sub]
  rw [e, det_chg, det_submatrix_equiv_self, det_fromBlocks_zero₂₁, det_diagonal, det_apply' (∑ o, a o • M o),
    Finset.sum_mul]
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, mul_assoc]

/- English proof (translation)
Introduce `r e`. Take `⟨κ, hκ⟩` from `GlobalTheory.T.vandermonde_density_symmetric r e`. Use `⟨κ * (1 / TrueCx.flagConst r) / Real.pi ^ (e + 2 + Fintype.card (Low r)) * (2 * Real.pi ^ 2 * Real.pi ^ e), fun D ε G ψ u hG hP hψ I _ c m h => ?_⟩` and prove the remaining obligations. Establish `hD : D = e + 2 + Fintype.card (Low r)` using `by simpa using Fintype.card_congr ε`. Establish `hp` using `hP.self_of_nhds`.

Use `set A := cHess (e + 2) (fun v => (ψ v : ℂ)) u`. Set `F (j l : Fin (e + 2))` to `curv G u (bas _ j) (bas _ l)`. Set `w (σ t : Equiv.Perm (Fin (e + 2))) : ℂ` to `((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ p : Fin e, A (σ (t p.succ.succ)) (t p.succ.succ)`. Set `q (σ t : Equiv.Perm (Fin (e + 2))) (x : Low r → ℂ) : ℂ` to `w σ t * (((r : ℂ) + 1) * (jacDens (G u) x • sq (G u) (F (σ (t 0)) (t 0)) (F (σ (t 1)) (t 1)) x) - jacDens (G u) x • ((F (σ (t 0)) (t 0)).trace * (F (σ (t 1)) (t 1)).trace))`. Establish `hq (σ t) : Integrable (q σ t)` using `(((integrable_sq hp _ _).const_mul _).sub ((MixDens.Canon.integrable_jacDens hp).smul_const _)).const_mul _`.

Establish `iq (σ t) : ∫ x, q σ t x = ((1 / TrueCx.flagConst r : ℝ) : ℂ) * (((Equiv.Perm.sign σ : ℤ) : ℂ) * ((F (σ (t 0)) (t 0) * F (σ (t 1)) (t 1)).trace * ∏ p : Fin e, A (σ (t p.succ.succ)) (t p.succ.succ)))`. Establish `: (r : ℂ) + 1 ≠ 0` using `Nat.cast_add_one_ne_zero r`. Rewrite using `[integral_const_mul, integral_sub ((integrable_sq hp _ _).const_mul _) ((MixDens.Canon.integrable_jacDens hp).smul_const _), integral_const_mul, integral_sq hp, integral_smul_const, MixDens.Canon.integral_jacDens_eq hp, Complex.real_smul]`. Simplify using `only [w]`. Clear the denominators using the available nonvanishing facts.

Expand and normalize the polynomial expressions, which then agree. Establish `pw (x : Low r → ℂ) : ∑ j, c j * (D.factorial / Real.pi ^ D * (∑ o : Option (Fin r), (m j o : ℂ) • cHess D (fun v => ((o.elim (ψ (base ε v)) (fun i => rootWt ε G i v) : ℝ) : ℂ)) (pt ε u x)).det.re) = κ / Real.pi ^ D * (∑ σ, ∑ t, q σ t x).re`. Take `⟨T, hT, h1⟩` from `MixDens.NormalCoord.exists_upper_chg_eq_one (posDef_chg (isUnit_uni x) hp)`. Take `⟨J, hJ, hr, hb⟩` from `GlobalTheory.T.jacobian_density_of_triangular (e + 2) r D ε G ψ u hG hP hψ x T hT h1`. Simplify using `only [← diagEntry_eq hT h1] at hr`.

Apply the tactic sequence `let M (o : Option (Fin r)) : Matrix (Fin (e + 2)) (Fin (e + 2)) ℂ := o.elim A fun i => Matrix.of fun j l => diagEntry (G u) (F j l) x i`. Establish `hd (j : I)` using `det_sum_chg ε J M (fun o => (m j o : ℂ)) (fun o => cHess D (fun v => ((o.elim (ψ (base ε v)) (fun i => rootWt ε G i v) : ℝ) : ℂ)) (pt ε u x)) hb hr`. Establish `hk (σ : Equiv.Perm (Fin (e + 2)))` using `hκ D hD I c m h fun k o => M o (σ k) k`. Establish `e1 : ∑ j, (c j : ℂ) * (D.factorial * (∑ o : Option (Fin r), (m j o : ℂ) • cHess D (fun v => ((o.elim (ψ (base ε v)) (fun i => rootWt ε G i v) : ℝ) : ℂ)) (pt ε u x)).det) = κ * ∑ σ, ∑ t, q σ t x`. Combine the equalities or inequalities in the displayed calculation.

Simplify using `only [hd, hJ, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Conclude with `Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring`. Use `_ = _ := by`. Rewrite using `[Finset.mul_sum]`.

Use `Finset.sum_congr rfl fun σ _ => ?_` and prove the remaining obligations. Rewrite using `[hk σ, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun t _ => ?_` and prove the remaining obligations. Apply the tactic sequence `simp only [M, Option.elim, of_apply, sum_diagEntry hp, q, w, sq, Complex.real_smul]`. Expand and normalize the polynomial expressions, which then agree.

Establish `e2` using `congrArg Complex.re e1`. Rewrite `e2` using `[Complex.re_sum, Complex.re_ofReal_mul]`. Rewrite using `[div_mul_eq_mul_div, ← e2, Finset.sum_div]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[Complex.re_ofReal_mul, ← Complex.ofReal_natCast, Complex.re_ofReal_mul]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hs : Integrable fun x => ∑ σ, ∑ t, q σ t x` using `integrable_finsetSum _ fun σ _ => integrable_finsetSum _ fun t _ => hq σ t`. Simplify using `only [pw]`. Rewrite using `[integral_const_mul, show (∫ x, (∑ σ, ∑ t, q σ t x).re) = (∫ x, ∑ σ, ∑ t, q σ t x).re from integral_re hs, integral_finsetSum _ fun σ _ => integrable_finsetSum _ fun t _ => hq σ t]`. Simplify using `only [integral_finsetSum _ fun t _ => hq _ t, iq, ← Finset.mul_sum (a := ((1 / TrueCx.flagConst r : ℝ) : ℂ))]`.

Rewrite using `[Complex.re_ofReal_mul, dens22_chTwo, ← hD]`. Use `Real.pi_ne_zero` as an intermediate fact. Simplify using `only [F]`. Clear the denominators using the available nonvanishing facts.
-/
theorem fibre_integral : ∀ r e : ℕ, ∃ t : ℝ, ∀ (D : ℕ) (ε : Fin D ≃ Fin (e + 2) ⊕ Low r) (G : V (e + 2) → Matrix (Fin r) (Fin r) ℂ) (ψ : V (e + 2) → ℝ) (u : V (e + 2)), MContDiffAt ∞ G u → (∀ᶠ v in 𝓝 u, (G v).PosDef) → ContDiffAt ℝ 2 ψ u → ∀ (I : Type) [Fintype I] (c : I → ℝ) (m : I → Option (Fin r) → ℤ), ∑ j, c j • lin (fun o => (m j o : ℝ)) ^ D = vdmPol r e → ∫ x : Low r → ℂ, ∑ j, c j * (D.factorial / Real.pi ^ D * (∑ o : Option (Fin r), (m j o : ℂ) • cHess D (fun v => ((o.elim (ψ (base ε v)) (fun i => rootWt ε G i v) : ℝ) : ℂ)) (pt ε u x)).det.re) = t * secondChernDensity e (chTwo G u) (cHess (e + 2) (fun v => (ψ v : ℂ)) u) := by
  intro r e
  obtain ⟨κ, hκ⟩ := GlobalTheory.T.vandermonde_density_symmetric r e
  refine ⟨κ * (1 / TrueCx.flagConst r) / Real.pi ^ (e + 2 + Fintype.card (Low r)) * (2 * Real.pi ^ 2 * Real.pi ^ e),
    fun D ε G ψ u hG hP hψ I _ c m h => ?_⟩
  have hD : D = e + 2 + Fintype.card (Low r) := by simpa using Fintype.card_congr ε
  have hp := hP.self_of_nhds
  set A := cHess (e + 2) (fun v => (ψ v : ℂ)) u
  let F (j l : Fin (e + 2)) := curv G u (bas _ j) (bas _ l)
  let w (σ t : Equiv.Perm (Fin (e + 2))) : ℂ :=
    ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ p : Fin e, A (σ (t p.succ.succ)) (t p.succ.succ)
  let q (σ t : Equiv.Perm (Fin (e + 2))) (x : Low r → ℂ) : ℂ :=
    w σ t * (((r : ℂ) + 1) * (jacDens (G u) x • sq (G u) (F (σ (t 0)) (t 0)) (F (σ (t 1)) (t 1)) x) -
      jacDens (G u) x • ((F (σ (t 0)) (t 0)).trace * (F (σ (t 1)) (t 1)).trace))
  have hq (σ t) : Integrable (q σ t) :=
    (((integrable_sq hp _ _).const_mul _).sub ((MixDens.Canon.integrable_jacDens hp).smul_const _)).const_mul _
  have iq (σ t) : ∫ x, q σ t x = ((1 / TrueCx.flagConst r : ℝ) : ℂ) * (((Equiv.Perm.sign σ : ℤ) : ℂ) *
      ((F (σ (t 0)) (t 0) * F (σ (t 1)) (t 1)).trace * ∏ p : Fin e, A (σ (t p.succ.succ)) (t p.succ.succ))) := by
    have : (r : ℂ) + 1 ≠ 0 := Nat.cast_add_one_ne_zero r
    rw [integral_const_mul, integral_sub ((integrable_sq hp _ _).const_mul _)
      ((MixDens.Canon.integrable_jacDens hp).smul_const _), integral_const_mul, integral_sq hp, integral_smul_const,
      MixDens.Canon.integral_jacDens_eq hp, Complex.real_smul]
    simp only [w]
    field_simp
    ring
  have pw (x : Low r → ℂ) : ∑ j, c j * (D.factorial / Real.pi ^ D * (∑ o : Option (Fin r), (m j o : ℂ) •
      cHess D (fun v => ((o.elim (ψ (base ε v)) (fun i => rootWt ε G i v) : ℝ) : ℂ)) (pt ε u x)).det.re) =
      κ / Real.pi ^ D * (∑ σ, ∑ t, q σ t x).re := by
    obtain ⟨T, hT, h1⟩ := MixDens.NormalCoord.exists_upper_chg_eq_one (posDef_chg (isUnit_uni x) hp)
    obtain ⟨J, hJ, hr, hb⟩ := GlobalTheory.T.jacobian_density_of_triangular (e + 2) r D ε G ψ u hG hP hψ x T hT h1
    simp only [← diagEntry_eq hT h1] at hr
    let M (o : Option (Fin r)) : Matrix (Fin (e + 2)) (Fin (e + 2)) ℂ :=
      o.elim A fun i => Matrix.of fun j l => diagEntry (G u) (F j l) x i
    have hd (j : I) := det_sum_chg ε J M (fun o => (m j o : ℂ)) (fun o => cHess D
      (fun v => ((o.elim (ψ (base ε v)) (fun i => rootWt ε G i v) : ℝ) : ℂ)) (pt ε u x)) hb hr
    have hk (σ : Equiv.Perm (Fin (e + 2))) := hκ D hD I c m h fun k o => M o (σ k) k
    have e1 : ∑ j, (c j : ℂ) * (D.factorial * (∑ o : Option (Fin r), (m j o : ℂ) •
        cHess D (fun v => ((o.elim (ψ (base ε v)) (fun i => rootWt ε G i v) : ℝ) : ℂ)) (pt ε u x)).det) =
        κ * ∑ σ, ∑ t, q σ t x := by
      calc _ = ∑ σ : Equiv.Perm (Fin (e + 2)), (jacDens (G u) x : ℂ) * ((Equiv.Perm.sign σ : ℤ) : ℂ) *
            ∑ j, (c j : ℂ) * (D.factorial * ((∏ k, ∑ o, (m j o : ℂ) * M o (σ k) k) *
              ∏ s : Low r, ((m j (some s.1.1) : ℂ) - m j (some s.1.2)))) := by
            simp only [hd, hJ, Finset.mul_sum]
            rw [Finset.sum_comm]
            exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
        _ = _ := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun σ _ => ?_
            rw [hk σ, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
            refine Finset.sum_congr rfl fun t _ => ?_
            simp only [M, Option.elim, of_apply, sum_diagEntry hp, q, w, sq, Complex.real_smul]
            ring
    have e2 := congrArg Complex.re e1
    rw [Complex.re_sum, Complex.re_ofReal_mul] at e2
    rw [div_mul_eq_mul_div, ← e2, Finset.sum_div]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Complex.re_ofReal_mul, ← Complex.ofReal_natCast, Complex.re_ofReal_mul]
    ring
  have hs : Integrable fun x => ∑ σ, ∑ t, q σ t x :=
    integrable_finsetSum _ fun σ _ => integrable_finsetSum _ fun t _ => hq σ t
  simp only [pw]
  rw [integral_const_mul, show (∫ x, (∑ σ, ∑ t, q σ t x).re) = (∫ x, ∑ σ, ∑ t, q σ t x).re from integral_re hs,
    integral_finsetSum _ fun σ _ => integrable_finsetSum _ fun t _ => hq σ t]
  simp only [integral_finsetSum _ fun t _ => hq _ t, iq, ← Finset.mul_sum (a := ((1 / TrueCx.flagConst r : ℝ) : ℂ))]
  rw [Complex.re_ofReal_mul, dens22_chTwo, ← hD]
  have := Real.pi_ne_zero
  simp only [F]
  field_simp

end GlobalTheory.FlagMoment
