import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.LocallyConstantMajorants.SmoothMajorants.Bounds
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SecondIntegrandOfBound
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SecondFubini
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MatrixMulApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FderivDetEqTraceAdjugate

noncomputable section

open MeasureTheory Matrix Filter Topology LineDeriv
open Ad3.K Ad3.K.LC Ad3.K.LC.B

namespace GlobalTheory.CompanionTheory.LCDer

/- English proof (translation)
Simplify using `[dz, LineDeriv.lineDerivOpCLM_apply, SchwartzMap.lineDerivOp_apply_eq_fderiv]`.
-/
theorem dz_apply (Q : Sw) (r : Fin 2) (c : Fin 3) (p : E5) : dz r c Q p =
    (2 : ℂ)⁻¹ * (fderiv ℝ (⇑Q) p (eU 1 r c) - Complex.I * fderiv ℝ (⇑Q) p (eU Complex.I r c)) := by
  simp [dz, LineDeriv.lineDerivOpCLM_apply, SchwartzMap.lineDerivOp_apply_eq_fderiv]

/- English proof (translation)
Simplify using `[dzb, LineDeriv.lineDerivOpCLM_apply, SchwartzMap.lineDerivOp_apply_eq_fderiv]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem dzb_apply (Q : Sw) (r : Fin 2) (c : Fin 3) (p : E5) : dzb r c Q p =
    (2 : ℂ)⁻¹ * (fderiv ℝ (⇑Q) p (eU 1 r c) + Complex.I * fderiv ℝ (⇑Q) p (eU Complex.I r c)) := by
  simp [dzb, LineDeriv.lineDerivOpCLM_apply, SchwartzMap.lineDerivOp_apply_eq_fderiv]
  ring

/- English proof (translation)
Simplify using `only [PH, PHc, Fin.sum_univ_two]`. Apply the tactic sequence `split_ifs <;>`. Simplify using `[SchwartzMap.smulLeftCLM_apply_apply (crd_temperate _ _), crd]`.
-/
theorem PH_apply (Q : Sw) (i j : Fin 3) (p : E5) :
    PH i j Q p - (if i = j then Q p else 0) = ∑ r, p.1 r i * dz r j Q p := by
  simp only [PH, PHc, Fin.sum_univ_two]
  split_ifs <;>
  simp [SchwartzMap.smulLeftCLM_apply_apply (crd_temperate _ _), crd]

/- English proof (translation)
Simplify using `only [PA, PAc, Fin.sum_univ_two]`. Apply the tactic sequence `split_ifs <;>`. Simplify using `[SchwartzMap.smulLeftCLM_apply_apply (crdc_temperate _ _), crdc]`.
-/
theorem PA_apply (Q : Sw) (i j : Fin 3) (p : E5) :
    PA i j Q p - (if i = j then Q p else 0) = ∑ r, (starRingEnd ℂ) (p.1 r i) * dzb r j Q p := by
  simp only [PA, PAc, Fin.sum_univ_two]
  split_ifs <;>
  simp [SchwartzMap.smulLeftCLM_apply_apply (crdc_temperate _ _), crdc]

/- English proof (translation)
Use `Prod.ext ?_ ?_` and prove the remaining obligations. Use function extensionality and compare the values at `r' c'`. Simplify using `only [Fin.sum_univ_two, Fin.sum_univ_three]`. Apply the tactic sequence `fin_cases r' <;> fin_cases c' <;> simp [eU, Complex.re_add_im]`. Simplify using `[eU, Fin.sum_univ_two, Fin.sum_univ_three]`.
-/
theorem expand_first (v : M23) : ((v, 0) : E5) =
    ∑ r, ∑ c, ((v r c).re • eU 1 r c + (v r c).im • eU Complex.I r c) := by
  refine Prod.ext ?_ ?_
  · funext r' c'
    simp only [Fin.sum_univ_two, Fin.sum_univ_three]
    fin_cases r' <;> fin_cases c' <;> simp [eU, Complex.re_add_im]
  · simp [eU, Fin.sum_univ_two, Fin.sum_univ_three]

/- English proof (translation)
Establish `hv : v = a + b * Complex.I` using `by rw [ha, hb, Complex.re_add_im]`. Establish `hc : (starRingEnd ℂ) v = a - b * Complex.I`. Rewrite using `[ha, hb]`. Apply the tactic sequence `apply Complex.ext <;> simp`. Rewrite using `[hc, hv]`.

Take the linear combination `(b * d2) * Complex.I_sq`.
-/
theorem wirt_term (a b d1 d2 : ℂ) (v : ℂ) (ha : a = v.re) (hb : b = v.im) :
    a * d1 + b * d2 = v * ((2 : ℂ)⁻¹ * (d1 - Complex.I * d2)) +
      (starRingEnd ℂ) v * ((2 : ℂ)⁻¹ * (d1 + Complex.I * d2)) := by
  have hv : v = a + b * Complex.I := by rw [ha, hb, Complex.re_add_im]
  have hc : (starRingEnd ℂ) v = a - b * Complex.I := by
    rw [ha, hb]
    apply Complex.ext <;> simp
  rw [hc, hv]
  linear_combination (b * d2) * Complex.I_sq

/- English proof (translation)
Rewrite using `[expand_first v, map_sum]`. Use `Finset.sum_congr rfl fun r _ => ?_` and prove the remaining obligations. Rewrite using `[map_sum]`. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Rewrite using `[map_add, map_smul, map_smul, Complex.real_smul, Complex.real_smul]`.

Conclude with `wirt_term _ _ _ _ _ rfl rfl`.
-/
theorem fderiv_first (D : E5 →L[ℝ] ℂ) (v : M23) : D (v, 0) = ∑ r, ∑ c,
    (v r c * ((2 : ℂ)⁻¹ * (D (eU 1 r c) - Complex.I * D (eU Complex.I r c))) +
      (starRingEnd ℂ) (v r c) * ((2 : ℂ)⁻¹ * (D (eU 1 r c) + Complex.I * D (eU Complex.I r c)))) := by
  rw [expand_first v, map_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [map_add, map_smul, map_smul, Complex.real_smul, Complex.real_smul]
  exact wirt_term _ _ _ _ _ rfl rfl

/- English proof (translation)
Simplify using `only [Fin.sum_univ_two, Fin.sum_univ_three, map_add, map_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem reorder (Y : Fin 2 → Fin 3 → ℂ) (a : Fin 3 → Fin 3 → ℂ) (u w : Fin 2 → Fin 3 → ℂ) :
    ∑ r, ∑ c, ((∑ i, Y r i * a i c) * u r c + (starRingEnd ℂ) (∑ i, Y r i * a i c) * w r c) =
      ∑ i, ∑ j, (a i j * ∑ r, Y r i * u r j + (starRingEnd ℂ) (a i j) * ∑ r, (starRingEnd ℂ) (Y r i) * w r j) := by
  simp only [Fin.sum_univ_two, Fin.sum_univ_three, map_add, map_mul]
  ring

/- English proof (translation)
Use `set p := Rq M (Z, q) with hp`. Use `set A := (Matrix.of M)⁻¹ * Matrix.of m with hA`. Establish `hu : IsUnit (Matrix.of M).det` using `isUnit_iff_ne_zero.mpr hM`. Establish `e1 : Matrix.of Z * Matrix.of m = Matrix.of p.1 * A`. Simplify using `only [hA, hp, Rq_apply, Rm_apply, Equiv.apply_symm_apply, Matrix.mul_assoc]`.

Rewrite using `[← Matrix.mul_assoc (Matrix.of M), Matrix.mul_nonsing_inv _ hu, Matrix.one_mul]`. Establish `e2 : ∀ r c, mulB Z m r c = ∑ i, p.1 r i * A i c`. Introduce `r c`. Use `congrFun (congrFun e1 r) c` as an intermediate fact. Simplify `this` using `[Matrix.mul_apply, mulB_apply]`.

Rewrite using `[fderiv_first]`. Simplify using `only [ell_apply, ellc_apply, PH_apply, PA_apply, e2, ← hA, dz_apply, dzb_apply]`. Conclude with `reorder _ _ _ _`.
-/
theorem wirtinger (Q : Sw) {M : complexMatrix3} (hM : (Matrix.of M).det ≠ 0) (Z : M23) (q : Fin 2 → ℂ) (m : complexMatrix3) :
    fderiv ℝ (⇑Q) (Rq M (Z, q)) (mulB Z m, 0) = ∑ i, ∑ j,
      (ell M i j m * (PH i j Q (Rq M (Z, q)) - if i = j then Q (Rq M (Z, q)) else 0) +
        ellc M i j m * (PA i j Q (Rq M (Z, q)) - if i = j then Q (Rq M (Z, q)) else 0)) := by
  set p := Rq M (Z, q) with hp
  set A := (Matrix.of M)⁻¹ * Matrix.of m with hA
  have hu : IsUnit (Matrix.of M).det := isUnit_iff_ne_zero.mpr hM
  have e1 : Matrix.of Z * Matrix.of m = Matrix.of p.1 * A := by
    simp only [hA, hp, Rq_apply, Rm_apply, Equiv.apply_symm_apply, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (Matrix.of M), Matrix.mul_nonsing_inv _ hu, Matrix.one_mul]
  have e2 : ∀ r c, mulB Z m r c = ∑ i, p.1 r i * A i c := by
    intro r c
    have := congrFun (congrFun e1 r) c
    simpa [Matrix.mul_apply, mulB_apply] using this
  rw [fderiv_first]
  simp only [ell_apply, ellc_apply, PH_apply, PA_apply, e2, ← hA, dz_apply, dzb_apply]
  exact reorder _ _ _ _

/- English proof (translation)
Unfold `ph`. Use `fun_prop`.
-/
theorem ph_meas (n : ℤ) : Measurable (ph n) := by
  unfold ph
  fun_prop

/- English proof (translation)
Unfold `ph`. Rewrite using `[norm_zpow]`. Distinguish the cases in `hz : z = 0`. Substitute `hz` using the available equality. Simplify using `only [norm_zero, Complex.ofReal_zero, div_zero]`.

Rewrite using `[_root_.zero_zpow_eq]`. Apply the tactic sequence `split_ifs <;> norm_num`. Establish `: ‖z / (‖z‖ : ℂ)‖ = 1`. Rewrite using `[norm_div, Complex.norm_real, norm_norm, div_self (norm_ne_zero_iff.mpr hz)]`. Rewrite using `[this, _root_.one_zpow]`.
-/
theorem norm_ph_le (n : ℤ) (z : ℂ) : ‖ph n z‖ ≤ 1 := by
  unfold ph
  rw [norm_zpow]
  by_cases hz : z = 0
  · subst hz
    simp only [norm_zero, Complex.ofReal_zero, div_zero]
    rw [_root_.zero_zpow_eq]
    split_ifs <;> norm_num
  · have : ‖z / (‖z‖ : ℂ)‖ = 1 := by
      rw [norm_div, Complex.norm_real, norm_norm, div_self (norm_ne_zero_iff.mpr hz)]
    rw [this, _root_.one_zpow]

/- English proof (translation)
Establish `hdet : Continuous (fun p : M22 × ℂ => (Matrix.of p.1).det)` using `Continuous.matrix_det (by exact continuous_fst)`. Establish `h1 : Measurable (fun p : M22 × ℂ => ph (4 * (k : ℤ) - 4) p.2)` using `(ph_meas _).comp measurable_snd`. Establish `h2 : Measurable (fun p : M22 × ℂ => ph (-(2 * (k : ℤ) - 2)) (Matrix.of p.1).det)` using `(ph_meas _).comp hdet.measurable`. Establish `h3 : Measurable (fun p : M22 × ℂ => ((‖(Matrix.of p.1).det‖ ^ (-(2 : ℝ)) : ℝ) : ℂ))` using `Complex.measurable_ofReal.comp (hdet.norm.measurable.pow_const _)`. Conclude with `((h1.mul h2).mul h3).aestronglyMeasurable`.
-/
theorem wt_meas (k : ℕ) : AEStronglyMeasurable (wt k) (volume : Measure (M22 × ℂ)) := by
  have hdet : Continuous (fun p : M22 × ℂ => (Matrix.of p.1).det) :=
    Continuous.matrix_det (by exact continuous_fst)
  have h1 : Measurable (fun p : M22 × ℂ => ph (4 * (k : ℤ) - 4) p.2) := (ph_meas _).comp measurable_snd
  have h2 : Measurable (fun p : M22 × ℂ => ph (-(2 * (k : ℤ) - 2)) (Matrix.of p.1).det) :=
    (ph_meas _).comp hdet.measurable
  have h3 : Measurable (fun p : M22 × ℂ => ((‖(Matrix.of p.1).det‖ ^ (-(2 : ℝ)) : ℝ) : ℂ)) :=
    Complex.measurable_ofReal.comp (hdet.norm.measurable.pow_const _)
  exact ((h1.mul h2).mul h3).aestronglyMeasurable

/- English proof (translation)
Establish `e : ‖((‖(Matrix.of p.1).det‖ ^ (-(2 : ℝ)) : ℝ) : ℂ)‖ = (‖(Matrix.of p.1).det‖ ^ 2)⁻¹`. Rewrite using `[Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _), Real.rpow_neg (norm_nonneg _), Real.rpow_two]`. Rewrite using `[wt, norm_mul, norm_mul, e]`. Establish `h1` using `norm_ph_le (4 * (k : ℤ) - 4) p.2`. Establish `h2` using `norm_ph_le (-(2 * (k : ℤ) - 2)) (Matrix.of p.1).det`.

Establish `h3 : 0 ≤ (‖(Matrix.of p.1).det‖ ^ 2)⁻¹` using `by positivity`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem wt_norm (k : ℕ) (p : M22 × ℂ) : ‖wt k p‖ ≤ (‖(Matrix.of p.1).det‖ ^ 2)⁻¹ := by
  have e : ‖((‖(Matrix.of p.1).det‖ ^ (-(2 : ℝ)) : ℝ) : ℂ)‖ = (‖(Matrix.of p.1).det‖ ^ 2)⁻¹ := by
    rw [Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _),
      Real.rpow_neg (norm_nonneg _), Real.rpow_two]
  rw [wt, norm_mul, norm_mul, e]
  have h1 := norm_ph_le (4 * (k : ℤ) - 4) p.2
  have h2 := norm_ph_le (-(2 * (k : ℤ) - 2)) (Matrix.of p.1).det
  have h3 : 0 ≤ (‖(Matrix.of p.1).det‖ ^ 2)⁻¹ := by positivity
  calc _ ≤ 1 * 1 * (‖(Matrix.of p.1).det‖ ^ 2)⁻¹ := by gcongr
    _ = _ := by ring

/- English proof (translation)
The claim follows from `GlobalTheory.CompanionTheory.SecJC.ae_good`.
-/
theorem ae_good : ∀ᵐ p : M22 × ℂ, (Matrix.of p.1).det ≠ 0 ∧ p.2 ≠ 0 := GlobalTheory.CompanionTheory.SecJC.ae_good

/- English proof (translation)
Establish `e : (fun p : M22 × ℂ => J Q M p.1 p.2) = fun p : M22 × ℂ => inn Q (gl M hM) (Matrix.of p.1) p.2`. Use function extensionality and compare the values at `p`. Rewrite using `[inn_eq_J]`. Rewrite using `[e]`. Conclude with `(GlobalTheory.CompanionTheory.SecJC.measurable_inn Q (gl M hM)).aestronglyMeasurable`.
-/
theorem J_meas (Q : Sw) {M : complexMatrix3} (hM : (Matrix.of M).det ≠ 0) :
    AEStronglyMeasurable (fun p : M22 × ℂ => J Q M p.1 p.2) volume := by
  have e : (fun p : M22 × ℂ => J Q M p.1 p.2) = fun p : M22 × ℂ => inn Q (gl M hM) (Matrix.of p.1) p.2 := by
    funext p
    rw [inn_eq_J]
  rw [e]
  exact (GlobalTheory.CompanionTheory.SecJC.measurable_inn Q (gl M hM)).aestronglyMeasurable

/- English proof (translation)
The claim follows from `Prod.ext (Rm_minv hM _) rfl`.
-/
theorem Rq_minv {M : complexMatrix3} (hM : (Matrix.of M).det ≠ 0) (X : E5) : Rq (minv M) (Rq M X) = X :=
  Prod.ext (Rm_minv hM _) rfl

/- English proof (translation)
Establish `h0 : 0 ≤ b` using `by linarith`. Rewrite using `[Rq_apply, Prod.norm_def]`. Use `max_le ?_ ?_` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Conclude with `norm_fst_le X`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem norm_Rq_le {M : complexMatrix3} {b : ℝ} (hb1 : 1 ≤ b) (hb : ‖Rm M‖ ≤ b) (X : E5) : ‖Rq M X‖ ≤ b * ‖X‖ := by
  have h0 : 0 ≤ b := by linarith
  rw [Rq_apply, Prod.norm_def]
  refine max_le ?_ ?_
  · calc ‖Rm M X.1‖ ≤ ‖Rm M‖ * ‖X.1‖ := (Rm M).le_opNorm _
      _ ≤ b * ‖X‖ := by
        gcongr
        exact norm_fst_le X
  · calc ‖X.2‖ ≤ ‖X‖ := norm_snd_le X
      _ ≤ b * ‖X‖ := le_mul_of_one_le_left (norm_nonneg _) hb1

/- English proof (translation)
The claim follows from `ContinuousLinearMap.opNorm_le_bound _ (by linarith) (norm_Rq_le hb1 hb)`.
-/
theorem norm_Rq_op_le {M : complexMatrix3} {b : ℝ} (hb1 : 1 ≤ b) (hb : ‖Rm M‖ ≤ b) : ‖Rq M‖ ≤ b :=
  ContinuousLinearMap.opNorm_le_bound _ (by linarith) (norm_Rq_le hb1 hb)

def bI (M : complexMatrix3) : ℝ := max 1 (‖mulB‖ * (‖minv M‖ + 1))

def bF (M : complexMatrix3) : ℝ := max 1 (‖mulB‖ * (‖M‖ + 1))

/- English proof (translation)
The claim follows from `le_max_left _ _`.
-/
theorem one_le_bI (M : complexMatrix3) : 1 ≤ bI M := le_max_left _ _

/- English proof (translation)
The claim follows from `le_max_left _ _`.
-/
theorem one_le_bF (M : complexMatrix3) : 1 ≤ bF M := le_max_left _ _

/- English proof (translation)
Use `norm_Rq_le (one_le_bI M) ((nb_inv h).trans (le_max_right _ _)) (Rq M' X)` as an intermediate fact. Rewrite `this` using `[Rq_minv (nb_det h)]`. Then use the resulting hypothesis.
-/
theorem norm_le_Rq {M M' : complexMatrix3} (h : M' ∈ nb M) (X : E5) : ‖X‖ ≤ bI M * ‖Rq M' X‖ := by
  have := norm_Rq_le (one_le_bI M) ((nb_inv h).trans (le_max_right _ _)) (Rq M' X)
  rwa [Rq_minv (nb_det h)] at this

/- English proof (translation)
Establish `h1` using `norm_le_Rq h X`. Establish `h2` using `one_le_bI M`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem one_add_le_Rq {M M' : complexMatrix3} (h : M' ∈ nb M) (X : E5) : 1 + ‖X‖ ≤ bI M * (1 + ‖Rq M' X‖) := by
  have h1 := norm_le_Rq h X
  have h2 := one_le_bI M
  nlinarith

/- English proof (translation)
Take `⟨C, hC⟩` from `hI N`. Use `set K := 2 * N + 20 with hK`. Take `⟨S, hS⟩ : ∃ S : ℝ, ∀ n ≤ 2 * N, ∀ Y : E5, (1 + ‖Y‖) ^ K * ‖iteratedFDeriv ℝ n (⇑Q) Y‖ ≤ S` from `⟨_, fun n hn Y => SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (K, 2 * N)) le_rfl hn Q Y⟩`. Use `set B := bI M ^ K * S * bF M ^ (2 * N) with hB`. Use `⟨C * B, fun M' hM' h t hh ht => ?_⟩` and prove the remaining obligations.

Establish `hsm : ContDiff ℝ (⊤ : ℕ∞) (fun X : E5 => Q (Rq M' X))` using `(Q.smooth ⊤).comp (Rq M').contDiff`. Use `hC (fun X => Q (Rq M' X)) B hsm (fun n hn X => ?_) h t 1 1 hh ht one_ne_zero` and prove the remaining obligations. Establish `hS0 : 0 ≤ S` using `((by positivity : (0:ℝ) ≤ (1 + ‖Rq M' X‖) ^ K * ‖iteratedFDeriv ℝ n (⇑Q) (Rq M' X)‖)).trans (hS n hn _)`. Establish `e : iteratedFDeriv ℝ n (fun X : E5 => Q (Rq M' X)) X = (iteratedFDeriv ℝ n (⇑Q) (Rq M' X)).compContinuousLinearMap fun _ => Rq M'` using `(Rq M').iteratedFDeriv_comp_right (Q.smooth ⊤) X (by exact_mod_cast le_top)`. Establish `hb : ‖Rq M'‖ ≤ bF M` using `norm_Rq_op_le (one_le_bF M) ((nb_fwd hM').trans (le_max_right _ _))`.

Establish `h1 : ‖iteratedFDeriv ℝ n (fun X : E5 => Q (Rq M' X)) X‖ ≤ ‖iteratedFDeriv ℝ n (⇑Q) (Rq M' X)‖ * bF M ^ (2 * N)`. Rewrite using `[e]`. Use `(ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_` and prove the remaining obligations. Use `gcongr`. Simplify using `only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]`.

Combine the equalities or inequalities in the displayed calculation. Establish `h2` using `one_add_le_Rq hM' X`. Combine the equalities or inequalities in the displayed calculation. Conclude with `mul_le_mul (pow_le_pow_left₀ (by positivity) h2 K) h1 (norm_nonneg _) (pow_nonneg (mul_nonneg (by linarith [one_le_bI M]) (by positivity)) K)`. Use `_ = bI M ^ K * ((1 + ‖Rq M' X‖) ^ K * ‖iteratedFDeriv ℝ n (⇑Q) (Rq M' X)‖) * bF M ^ (2 * N) := by`.

Rewrite using `[mul_pow]`. Expand and normalize the polynomial expressions, which then agree. Use `_ ≤ bI M ^ K * S * bF M ^ (2 * N) := by`. Use `hS n hn (Rq M' X)` as an intermediate fact. Establish `h3 : 0 ≤ bI M` using `by linarith [one_le_bI M]`.

Establish `h4 : 0 ≤ bF M` using `by linarith [one_le_bF M]`. Use `gcongr`.
-/
theorem J_bound (hI : IbpBound) (N : ℕ) (Q : Sw) {M : complexMatrix3} (_hM : (Matrix.of M).det ≠ 0) :
    ∃ C : ℝ, ∀ M' ∈ nb M, ∀ (h : M22) (t : ℂ), (Matrix.of h).det ≠ 0 → t ≠ 0 →
      ‖J Q M' h t‖ ≤ C * jm N h t 1 1 := by
  obtain ⟨C, hC⟩ := hI N
  set K := 2 * N + 20 with hK
  obtain ⟨S, hS⟩ : ∃ S : ℝ, ∀ n ≤ 2 * N, ∀ Y : E5, (1 + ‖Y‖) ^ K * ‖iteratedFDeriv ℝ n (⇑Q) Y‖ ≤ S :=
    ⟨_, fun n hn Y => SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (K, 2 * N)) le_rfl hn Q Y⟩
  set B := bI M ^ K * S * bF M ^ (2 * N) with hB
  refine ⟨C * B, fun M' hM' h t hh ht => ?_⟩
  have hsm : ContDiff ℝ (⊤ : ℕ∞) (fun X : E5 => Q (Rq M' X)) :=
    (Q.smooth ⊤).comp (Rq M').contDiff
  refine hC (fun X => Q (Rq M' X)) B hsm (fun n hn X => ?_) h t 1 1 hh ht one_ne_zero
  have hS0 : 0 ≤ S := ((by positivity : (0:ℝ) ≤ (1 + ‖Rq M' X‖) ^ K * ‖iteratedFDeriv ℝ n (⇑Q) (Rq M' X)‖)).trans (hS n hn _)
  have e : iteratedFDeriv ℝ n (fun X : E5 => Q (Rq M' X)) X =
      (iteratedFDeriv ℝ n (⇑Q) (Rq M' X)).compContinuousLinearMap fun _ => Rq M' :=
    (Rq M').iteratedFDeriv_comp_right (Q.smooth ⊤) X (by exact_mod_cast le_top)
  have hb : ‖Rq M'‖ ≤ bF M := norm_Rq_op_le (one_le_bF M) ((nb_fwd hM').trans (le_max_right _ _))
  have h1 : ‖iteratedFDeriv ℝ n (fun X : E5 => Q (Rq M' X)) X‖ ≤
      ‖iteratedFDeriv ℝ n (⇑Q) (Rq M' X)‖ * bF M ^ (2 * N) := by
    rw [e]
    refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
    gcongr
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    calc ‖Rq M'‖ ^ n ≤ bF M ^ n := by gcongr
      _ ≤ bF M ^ (2 * N) := pow_le_pow_right₀ (one_le_bF M) hn
  have h2 := one_add_le_Rq hM' X
  calc (1 + ‖X‖) ^ K * ‖iteratedFDeriv ℝ n (fun X : E5 => Q (Rq M' X)) X‖
      ≤ (bI M * (1 + ‖Rq M' X‖)) ^ K * (‖iteratedFDeriv ℝ n (⇑Q) (Rq M' X)‖ * bF M ^ (2 * N)) := by
        exact mul_le_mul (pow_le_pow_left₀ (by positivity) h2 K) h1 (norm_nonneg _)
          (pow_nonneg (mul_nonneg (by linarith [one_le_bI M]) (by positivity)) K)
    _ = bI M ^ K * ((1 + ‖Rq M' X‖) ^ K * ‖iteratedFDeriv ℝ n (⇑Q) (Rq M' X)‖) * bF M ^ (2 * N) := by
        rw [mul_pow]; ring
    _ ≤ bI M ^ K * S * bF M ^ (2 * N) := by
        have := hS n hn (Rq M' X)
        have h3 : 0 ≤ bI M := by linarith [one_le_bI M]
        have h4 : 0 ≤ bF M := by linarith [one_le_bF M]
        gcongr

/- English proof (translation)
Establish `hd : ∀ a b, DifferentiableAt ℝ (fun M' : complexMatrix3 => Matrix.of M' a b) M`. Introduce `a b`. Conclude with `((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℂ) b).comp (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => Fin 3 → ℂ) a)).differentiableAt`. Take `⟨h1, h2⟩` from `GlobalTheory.MatDeriv.jacobi_fderiv_det (fun M' : complexMatrix3 => Matrix.of M') M hd`. Establish `e : fderiv ℝ (fun M' : complexMatrix3 => (Matrix.of M').det) M = (Matrix.of M).det • ∑ i, ell M i i`.

Use `ContinuousLinearMap.ext fun m => ?_` and prove the remaining obligations. Establish `hdm : GlobalTheory.MatDeriv.dMat (fun M' : complexMatrix3 => Matrix.of M') M m = Matrix.of m`. Use extensionality with `a b`. Establish `hL : HasFDerivAt (fun M' : complexMatrix3 => M' a b) ((ContinuousLinearMap.proj (R` using `ℝ) (φ := fun _ : Fin 3 => ℂ) b).comp (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => Fin 3 → ℂ) a)) M := ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℂ) b).comp (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => Fin 3 → ℂ) a)).hasFDerivAt`. Simplify using `only [GlobalTheory.MatDeriv.dMat, Matrix.of_apply]`.

Rewrite using `[hL.fderiv]`. Both sides reduce to the same expression. Establish `hadj : (Matrix.of M).adjugate = (Matrix.of M).det • (Matrix.of M)⁻¹`. Rewrite using `[Matrix.inv_def, smul_smul, Ring.inverse_eq_inv', mul_inv_cancel₀ hM, one_smul]`. Rewrite using `[h2 m, hdm, hadj, Matrix.smul_mul, Matrix.trace_smul]`.

Simplify using `[ell_apply, Matrix.trace, Matrix.diag]`. Rewrite using `[← e]`. Conclude with `h1.hasFDerivAt`.
-/
theorem hasFDerivAt_det' {M : complexMatrix3} (hM : (Matrix.of M).det ≠ 0) :
    HasFDerivAt (fun M' : complexMatrix3 => (Matrix.of M').det)
      ((Matrix.of M).det • ∑ i, ell M i i) M := by
  have hd : ∀ a b, DifferentiableAt ℝ (fun M' : complexMatrix3 => Matrix.of M' a b) M := by
    intro a b
    exact ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℂ) b).comp
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => Fin 3 → ℂ) a)).differentiableAt
  obtain ⟨h1, h2⟩ := GlobalTheory.MatDeriv.jacobi_fderiv_det (fun M' : complexMatrix3 => Matrix.of M') M hd
  have e : fderiv ℝ (fun M' : complexMatrix3 => (Matrix.of M').det) M = (Matrix.of M).det • ∑ i, ell M i i := by
    refine ContinuousLinearMap.ext fun m => ?_
    have hdm : GlobalTheory.MatDeriv.dMat (fun M' : complexMatrix3 => Matrix.of M') M m = Matrix.of m := by
      ext a b
      have hL : HasFDerivAt (fun M' : complexMatrix3 => M' a b)
          ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℂ) b).comp
            (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => Fin 3 → ℂ) a)) M :=
        ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℂ) b).comp
            (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => Fin 3 → ℂ) a)).hasFDerivAt
      simp only [GlobalTheory.MatDeriv.dMat, Matrix.of_apply]
      rw [hL.fderiv]
      rfl
    have hadj : (Matrix.of M).adjugate = (Matrix.of M).det • (Matrix.of M)⁻¹ := by
      rw [Matrix.inv_def, smul_smul, Ring.inverse_eq_inv', mul_inv_cancel₀ hM, one_smul]
    rw [h2 m, hdm, hadj, Matrix.smul_mul, Matrix.trace_smul]
    simp [ell_apply, Matrix.trace, Matrix.diag]
  rw [← e]
  exact h1.hasFDerivAt

/- English proof (translation)
Establish `hd` using `hasFDerivAt_det' hM`. Establish `hc : HasFDerivAt (fun M' : complexMatrix3 => (starRingEnd ℂ) (Matrix.of M').det) (Complex.conjCLE.toContinuousLinearMap.comp ((Matrix.of M).det • ∑ i, ell M i i)) M` using `(Complex.conjCLE.toContinuousLinearMap.hasFDerivAt).comp M hd`. Establish `hm` using `hc.mul hd`. Establish `e1 : (fun M' : complexMatrix3 => ((‖(Matrix.of M').det‖ ^ 2 : ℝ) : ℂ)) = fun M' : complexMatrix3 => (starRingEnd ℂ) (Matrix.of M').det * (Matrix.of M').det`. Use function extensionality and compare the values at `M'`.

Rewrite using `[Complex.conj_mul']`. Use `push_cast`. Both sides reduce to the same expression. Establish `e2 : ((‖(Matrix.of M).det‖ ^ 2 : ℝ) : ℂ) • ∑ i, (ell M i i + ellc M i i) = (starRingEnd ℂ) (Matrix.of M).det • (Matrix.of M).det • ∑ i, ell M i i + (Matrix.of M).det • (Complex.conjCLE.toContinuousLinearMap.comp ((Matrix.of M).det • ∑ i, ell M i i))`. Use `ContinuousLinearMap.ext fun m => ?_` and prove the remaining obligations.

Establish `hs : ∑ i, ellc M i i m = (starRingEnd ℂ) (∑ i, ell M i i m)`. Simplify using `only [ellc_apply, ell_apply, map_sum]`. Establish `hδ : ((‖(Matrix.of M).det‖ ^ 2 : ℝ) : ℂ) = (starRingEnd ℂ) (Matrix.of M).det * (Matrix.of M).det`. Rewrite using `[Complex.conj_mul']`. Use `push_cast`.

Both sides reduce to the same expression. Simplify using `only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.sum_apply, ContinuousLinearMap.comp_apply, smul_eq_mul, Finset.sum_add_distrib, hs, hδ]`. Simplify using `only [ContinuousLinearEquiv.coe_coe, Complex.conjCLE_apply, map_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e1, e2]`.

Conclude with `hm`.
-/
theorem hasFDerivAt_normSq_det {M : complexMatrix3} (hM : (Matrix.of M).det ≠ 0) :
    HasFDerivAt (fun M' : complexMatrix3 => ((‖(Matrix.of M').det‖ ^ 2 : ℝ) : ℂ))
      (((‖(Matrix.of M).det‖ ^ 2 : ℝ) : ℂ) • ∑ i, (ell M i i + ellc M i i)) M := by
  have hd := hasFDerivAt_det' hM
  have hc : HasFDerivAt (fun M' : complexMatrix3 => (starRingEnd ℂ) (Matrix.of M').det)
      (Complex.conjCLE.toContinuousLinearMap.comp ((Matrix.of M).det • ∑ i, ell M i i)) M :=
    (Complex.conjCLE.toContinuousLinearMap.hasFDerivAt).comp M hd
  have hm := hc.mul hd
  have e1 : (fun M' : complexMatrix3 => ((‖(Matrix.of M').det‖ ^ 2 : ℝ) : ℂ)) =
      fun M' : complexMatrix3 => (starRingEnd ℂ) (Matrix.of M').det * (Matrix.of M').det := by
    funext M'
    rw [Complex.conj_mul']
    push_cast
    rfl
  have e2 : ((‖(Matrix.of M).det‖ ^ 2 : ℝ) : ℂ) • ∑ i, (ell M i i + ellc M i i) =
      (starRingEnd ℂ) (Matrix.of M).det • (Matrix.of M).det • ∑ i, ell M i i +
        (Matrix.of M).det • (Complex.conjCLE.toContinuousLinearMap.comp ((Matrix.of M).det • ∑ i, ell M i i)) := by
    refine ContinuousLinearMap.ext fun m => ?_
    have hs : ∑ i, ellc M i i m = (starRingEnd ℂ) (∑ i, ell M i i m) := by
      simp only [ellc_apply, ell_apply, map_sum]
    have hδ : ((‖(Matrix.of M).det‖ ^ 2 : ℝ) : ℂ) = (starRingEnd ℂ) (Matrix.of M).det * (Matrix.of M).det := by
      rw [Complex.conj_mul']
      push_cast
      rfl
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.sum_apply,
      ContinuousLinearMap.comp_apply, smul_eq_mul, Finset.sum_add_distrib, hs, hδ]
    simp only [ContinuousLinearEquiv.coe_coe, Complex.conjCLE_apply, map_mul]
    ring
  rw [e1, e2]
  exact hm

def Zq (h : M22) (t : ℂ) (p : (Fin 2 → ℂ) × ℂ) : E5 :=
  (Matrix.of.symm (Matrix.of h * blk p.1), rowv t p.2 (Matrix.of h))

def Tq0 (h : M22) (t : ℂ) : E5 →ₗ[ℝ] ((Fin 2 → ℂ) × ℂ) where
  toFun X := ((Matrix.of h)⁻¹.mulVec (fun r => X.1 r 2), t⁻¹ * (Matrix.vecMul X.2 (Matrix.of h)) 1)
  map_add' X Y := by
    refine Prod.ext ?_ ?_
    · exact Matrix.mulVec_add (Matrix.of h)⁻¹ (fun r => X.1 r 2) (fun r => Y.1 r 2)
    · simp [Matrix.add_vecMul, mul_add]
  map_smul' a X := by
    refine Prod.ext ?_ ?_
    · have e : (fun r => (a • X).1 r 2) = (a : ℂ) • (fun r => X.1 r 2) := by
        funext r; simp
      simp only [e, Matrix.mulVec_smul]
      funext r
      simp only [Pi.smul_apply, Prod.smul_fst, RingHom.id_apply, smul_eq_mul, Complex.real_smul]
    · have e : (a • X).2 = (a : ℂ) • X.2 := by
        funext r; simp
      simp only [e, Matrix.smul_vecMul]
      simp [mul_left_comm]

def Tq (h : M22) (t : ℂ) : E5 →L[ℝ] ((Fin 2 → ℂ) × ℂ) := LinearMap.toContinuousLinearMap (Tq0 h t)

/- English proof (translation)
Establish `hu : IsUnit (Matrix.of h).det` using `isUnit_iff_ne_zero.mpr hh`. Use `Prod.ext ?_ ?_` and prove the remaining obligations. Establish `e : (fun r => (Zq h t p).1 r 2) = (Matrix.of h).mulVec p.1`. Use function extensionality and compare the values at `r`. Simplify using `[Zq, blk, Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]`.

Use `show (Matrix.of h)⁻¹.mulVec (fun r => (Zq h t p).1 r 2) = p.1`. Rewrite using `[e, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu, Matrix.one_mulVec]`. Use `show t⁻¹ * (Matrix.vecMul (Zq h t p).2 (Matrix.of h)) 1 = p.2`. Simplify using `only [Zq, rowv]`. Rewrite using `[Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hu, Matrix.vecMul_one]`.

Simplify using `[ht]`.
-/
theorem Tq_Zq {h : M22} {t : ℂ} (hh : (Matrix.of h).det ≠ 0) (ht : t ≠ 0) (p : (Fin 2 → ℂ) × ℂ) :
    Tq h t (Zq h t p) = p := by
  have hu : IsUnit (Matrix.of h).det := isUnit_iff_ne_zero.mpr hh
  refine Prod.ext ?_ ?_
  · have e : (fun r => (Zq h t p).1 r 2) = (Matrix.of h).mulVec p.1 := by
      funext r
      simp [Zq, blk, Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
    show (Matrix.of h)⁻¹.mulVec (fun r => (Zq h t p).1 r 2) = p.1
    rw [e, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu, Matrix.one_mulVec]
  · show t⁻¹ * (Matrix.vecMul (Zq h t p).2 (Matrix.of h)) 1 = p.2
    simp only [Zq, rowv]
    rw [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hu, Matrix.vecMul_one]
    simp [ht]

/- English proof (translation)
Establish `: -2 * (Real.pi : ℂ) * Complex.I * (2 * (x.re : ℂ)) = ((-2 * Real.pi * (2 * x.re) : ℝ) : ℂ) * Complex.I` using `by push_cast; ring`. Rewrite using `[psiC, this, Complex.norm_exp_ofReal_mul_I]`.
-/
theorem norm_psiC (x : ℂ) : ‖psiC x‖ = 1 := by
  have : -2 * (Real.pi : ℂ) * Complex.I * (2 * (x.re : ℂ)) = ((-2 * Real.pi * (2 * x.re) : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [psiC, this, Complex.norm_exp_ofReal_mul_I]

/- English proof (translation)
Use `Continuous.prodMk ?_ ?_` and prove the remaining obligations. Conclude with `continuous_const.matrix_mul (GlobalTheory.CompanionTheory.SecJC.continuous_blk.comp continuous_fst)`. Establish `: Continuous (fun p : (Fin 2 → ℂ) × ℂ => (![t, t * p.2] : Fin 2 → ℂ))`. Use `continuous_pi fun i => ?_` and prove the remaining obligations. Apply the tactic sequence `fin_cases i <;> simp <;> fun_prop`.

Conclude with `this.matrix_vecMul continuous_const`.
-/
theorem continuous_Zq (h : M22) (t : ℂ) : Continuous (Zq h t) := by
  refine Continuous.prodMk ?_ ?_
  · exact continuous_const.matrix_mul (GlobalTheory.CompanionTheory.SecJC.continuous_blk.comp continuous_fst)
  · have : Continuous (fun p : (Fin 2 → ℂ) × ℂ => (![t, t * p.2] : Fin 2 → ℂ)) := by
      refine continuous_pi fun i => ?_
      fin_cases i <;> simp <;> fun_prop
    exact this.matrix_vecMul continuous_const

def fX (Q : Sw) (h : M22) (t : ℂ) (M : complexMatrix3) (p : (Fin 2 → ℂ) × ℂ) : ℂ :=
  Q (Rq M (Zq h t p)) * psiC (-(1 * p.1 1)) * psiC (-(1 * p.2))

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem J_eq (Q : Sw) (M : complexMatrix3) (h : M22) (t : ℂ) : J Q M h t = ∫ p, fX Q h t M p := rfl

/- English proof (translation)
Unfold `fX`. Use `((Q.continuous.comp ((Rq M).continuous.comp (continuous_Zq h t))).mul ?_).mul ?_` and prove the remaining obligations. Conclude with `GlobalTheory.CompanionTheory.SecJC.continuous_psiC.comp (by fun_prop)`. Conclude with `GlobalTheory.CompanionTheory.SecJC.continuous_psiC.comp (by fun_prop)`.
-/
theorem continuous_fX (Q : Sw) (h : M22) (t : ℂ) (M : complexMatrix3) : Continuous (fX Q h t M) := by
  unfold fX
  refine ((Q.continuous.comp ((Rq M).continuous.comp (continuous_Zq h t))).mul ?_).mul ?_
  · exact GlobalTheory.CompanionTheory.SecJC.continuous_psiC.comp (by fun_prop)
  · exact GlobalTheory.CompanionTheory.SecJC.continuous_psiC.comp (by fun_prop)

def cA (h : M22) (t : ℂ) (M : complexMatrix3) : ℝ := max 1 (‖Tq h t‖ * bI M)

/- English proof (translation)
Establish `h1 : ‖p‖ ≤ ‖Tq h t‖ * ‖Zq h t p‖`. Combine the equalities or inequalities in the displayed calculation. Establish `h2` using `norm_le_Rq hM' (Zq h t p)`. Establish `h3 : ‖p‖ ≤ ‖Tq h t‖ * bI M * ‖Rq M' (Zq h t p)‖`. Combine the equalities or inequalities in the displayed calculation.

Establish `hY` using `norm_nonneg (Rq M' (Zq h t p))`. Establish `hm1` using `le_max_left 1 (‖Tq h t‖ * bI M)`. Establish `hm2` using `le_max_right 1 (‖Tq h t‖ * bI M)`. Simplify using `only [cA]`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem one_add_le_Zq {h : M22} {t : ℂ} (hh : (Matrix.of h).det ≠ 0) (ht : t ≠ 0) {M M' : complexMatrix3}
    (hM' : M' ∈ nb M) (p : (Fin 2 → ℂ) × ℂ) :
    1 + ‖p‖ ≤ cA h t M * (1 + ‖Rq M' (Zq h t p)‖) := by
  have h1 : ‖p‖ ≤ ‖Tq h t‖ * ‖Zq h t p‖ := by
    calc ‖p‖ = ‖Tq h t (Zq h t p)‖ := by rw [Tq_Zq hh ht]
      _ ≤ _ := (Tq h t).le_opNorm _
  have h2 := norm_le_Rq hM' (Zq h t p)
  have h3 : ‖p‖ ≤ ‖Tq h t‖ * bI M * ‖Rq M' (Zq h t p)‖ := by
    calc ‖p‖ ≤ ‖Tq h t‖ * ‖Zq h t p‖ := h1
      _ ≤ ‖Tq h t‖ * (bI M * ‖Rq M' (Zq h t p)‖) := by gcongr
      _ = _ := by ring
  have hY := norm_nonneg (Rq M' (Zq h t p))
  have hm1 := le_max_left 1 (‖Tq h t‖ * bI M)
  have hm2 := le_max_right 1 (‖Tq h t‖ * bI M)
  simp only [cA]
  nlinarith

/- English proof (translation)
Rewrite using `[Real.rpow_neg hu.le, show (7 : ℝ) = ((7 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]`. Rewrite using `[le_mul_inv_iff₀ (by positivity)]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem le_div_one_add_pow_succ_of_mul_le {a u v c S : ℝ} (ha : 0 ≤ a) (hu : 0 < u) (hc : 0 ≤ c) (huv : u ≤ c * v)
    (h : v ^ 7 * a ≤ S) : a ≤ c ^ 7 * S * u ^ (-(7 : ℝ)) := by
  rw [Real.rpow_neg hu.le, show (7 : ℝ) = ((7 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [le_mul_inv_iff₀ (by positivity)]
  calc a * u ^ 7 ≤ a * (c * v) ^ 7 := by gcongr
    _ = c ^ 7 * (v ^ 7 * a) := by ring
    _ ≤ c ^ 7 * S := by gcongr

/- English proof (translation)
The claim follows from `zero_le_one.trans (le_max_left _ _)`.
-/
theorem cA_nonneg (h : M22) (t : ℂ) (M : complexMatrix3) : 0 ≤ cA h t M :=
  zero_le_one.trans (le_max_left _ _)

/- English proof (translation)
Establish `e : ‖fX Q h t M' p‖ = ‖Q (Rq M' (Zq h t p))‖`. Rewrite using `[fX, norm_mul, norm_mul, norm_psiC, norm_psiC, mul_one, mul_one]`. Rewrite using `[e]`. Use `hS (Rq M' (Zq h t p))` as an intermediate fact. Rewrite `this` using `[norm_iteratedFDeriv_zero]`.

Conclude with `le_div_one_add_pow_succ_of_mul_le (norm_nonneg _) (by positivity) (cA_nonneg h t M) (one_add_le_Zq hh ht hM' p) this`.
-/
theorem fX_bound (Q : Sw) {h : M22} {t : ℂ} (hh : (Matrix.of h).det ≠ 0) (ht : t ≠ 0) {M M' : complexMatrix3}
    (hM' : M' ∈ nb M) {S : ℝ} (hS : ∀ Y : E5, (1 + ‖Y‖) ^ 7 * ‖iteratedFDeriv ℝ 0 (⇑Q) Y‖ ≤ S)
    (p : (Fin 2 → ℂ) × ℂ) : ‖fX Q h t M' p‖ ≤ cA h t M ^ 7 * S * (1 + ‖p‖) ^ (-(7 : ℝ)) := by
  have e : ‖fX Q h t M' p‖ = ‖Q (Rq M' (Zq h t p))‖ := by
    rw [fX, norm_mul, norm_mul, norm_psiC, norm_psiC, mul_one, mul_one]
  rw [e]
  have := hS (Rq M' (Zq h t p))
  rw [norm_iteratedFDeriv_zero] at this
  exact le_div_one_add_pow_succ_of_mul_le (norm_nonneg _) (by positivity) (cA_nonneg h t M) (one_add_le_Zq hh ht hM' p) this

/- English proof (translation)
Use `haveI : (volume : Measure (Fin 2 → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _`. Use `haveI : (volume : Measure ((Fin 2 → ℂ) × ℂ)).IsAddHaarMeasure := by`. Rewrite using `[Measure.volume_eq_prod]`. Use `infer_instance`. Use `(integrable_one_add_norm ?_).const_mul K` and prove the remaining obligations.

Establish `: Module.finrank ℝ ((Fin 2 → ℂ) × ℂ) = 6`. Simplify using `[Module.finrank_prod, Module.finrank_pi_fintype, Complex.finrank_real_complex]`. Rewrite using `[this]`. Evaluate the numerical expressions.
-/
theorem integrable_bound (K : ℝ) :
    Integrable (fun p : (Fin 2 → ℂ) × ℂ => K * (1 + ‖p‖) ^ (-(7 : ℝ))) := by
  haveI : (volume : Measure (Fin 2 → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  haveI : (volume : Measure ((Fin 2 → ℂ) × ℂ)).IsAddHaarMeasure := by
    rw [Measure.volume_eq_prod]
    infer_instance
  refine (integrable_one_add_norm ?_).const_mul K
  have : Module.finrank ℝ ((Fin 2 → ℂ) × ℂ) = 6 := by
    simp [Module.finrank_prod, Module.finrank_pi_fintype, Complex.finrank_real_complex]
  rw [this]
  norm_num

/- English proof (translation)
Take `⟨S, hS⟩ : ∃ S : ℝ, ∀ Y : E5, (1 + ‖Y‖) ^ 7 * ‖iteratedFDeriv ℝ 0 (⇑Q) Y‖ ≤ S` from `⟨_, fun Y => SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (7, 0)) le_rfl le_rfl Q Y⟩`. Conclude with `(integrable_bound _).mono' (continuous_fX Q h t M).aestronglyMeasurable (ae_of_all _ fun p => fX_bound Q hh ht (self_mem_nb hM) hS p)`.
-/
theorem integrable_fX (Q : Sw) {h : M22} {t : ℂ} (hh : (Matrix.of h).det ≠ 0) (ht : t ≠ 0) {M : complexMatrix3}
    (hM : (Matrix.of M).det ≠ 0) : Integrable (fX Q h t M) := by
  obtain ⟨S, hS⟩ : ∃ S : ℝ, ∀ Y : E5, (1 + ‖Y‖) ^ 7 * ‖iteratedFDeriv ℝ 0 (⇑Q) Y‖ ≤ S :=
    ⟨_, fun Y => SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (7, 0)) le_rfl le_rfl Q Y⟩
  exact (integrable_bound _).mono' (continuous_fX Q h t M).aestronglyMeasurable
    (ae_of_all _ fun p => fX_bound Q hh ht (self_mem_nb hM) hS p)

def Dq (Z : M23) : complexMatrix3 →L[ℝ] E5 := (ContinuousLinearMap.inl ℝ M23 (Fin 2 → ℂ)).comp (mulB Z)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem Dq_apply (Z : M23) (m : complexMatrix3) : Dq Z m = (mulB Z m, 0) := rfl

/- English proof (translation)
Use `ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun m => ?_` and prove the remaining obligations. Establish `e : ‖Dq Z m‖ = ‖mulB Z m‖`. Rewrite using `[Dq_apply, Prod.norm_def]`. Simplify using the standard rewrite rules. Rewrite using `[e]`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem norm_Dq_le (Z : M23) : ‖Dq Z‖ ≤ ‖mulB‖ * ‖Z‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun m => ?_
  have e : ‖Dq Z m‖ = ‖mulB Z m‖ := by
    rw [Dq_apply, Prod.norm_def]
    simp
  rw [e]
  calc ‖mulB Z m‖ ≤ ‖mulB Z‖ * ‖m‖ := (mulB Z).le_opNorm m
    _ ≤ ‖mulB‖ * ‖Z‖ * ‖m‖ := by gcongr; exact mulB.le_opNorm Z

def dX (Q : Sw) (h : M22) (t : ℂ) (M : complexMatrix3) (p : (Fin 2 → ℂ) × ℂ) : complexMatrix3 →L[ℝ] ℂ :=
  psiC (-(1 * p.2)) • psiC (-(1 * p.1 1)) •
    (fderiv ℝ (⇑Q) (Rq M (Zq h t p))).comp (Dq (Zq h t p).1)

/- English proof (translation)
Establish `h0 : HasFDerivAt (fun M' => Rq M' (Zq h t p)) (Dq (Zq h t p).1) M`. Establish `e : (fun M' => Rq M' (Zq h t p)) = fun M' => Dq (Zq h t p).1 M' + ((0 : M23), (Zq h t p).2)`. Use function extensionality and compare the values at `M'`. Use `Prod.ext ?_ ?_` and prove the remaining obligations. Simplify using `[Dq_apply, Rq_apply]`.

Both sides reduce to the same expression. Simplify using `[Dq_apply, Rq_apply]`. Rewrite using `[e]`. Conclude with `(Dq (Zq h t p).1).hasFDerivAt.add_const _`. Establish `h1 : HasFDerivAt (fun M' => Q (Rq M' (Zq h t p))) ((fderiv ℝ (⇑Q) (Rq M (Zq h t p))).comp (Dq (Zq h t p).1)) M` using `(Q.differentiableAt.hasFDerivAt).comp M h0`.

Conclude with `(h1.mul_const _).mul_const _`.
-/
theorem hasFDerivAt_fX (Q : Sw) (h : M22) (t : ℂ) (M : complexMatrix3) (p : (Fin 2 → ℂ) × ℂ) :
    HasFDerivAt (fun M' => fX Q h t M' p) (dX Q h t M p) M := by
  have h0 : HasFDerivAt (fun M' => Rq M' (Zq h t p)) (Dq (Zq h t p).1) M := by
    have e : (fun M' => Rq M' (Zq h t p)) = fun M' => Dq (Zq h t p).1 M' + ((0 : M23), (Zq h t p).2) := by
      funext M'
      refine Prod.ext ?_ ?_
      · simp [Dq_apply, Rq_apply]
        rfl
      · simp [Dq_apply, Rq_apply]
    rw [e]
    exact (Dq (Zq h t p).1).hasFDerivAt.add_const _
  have h1 : HasFDerivAt (fun M' => Q (Rq M' (Zq h t p)))
      ((fderiv ℝ (⇑Q) (Rq M (Zq h t p))).comp (Dq (Zq h t p).1)) M :=
    (Q.differentiableAt.hasFDerivAt).comp M h0
  exact (h1.mul_const _).mul_const _

/- English proof (translation)
Unfold `dX`. Use `(GlobalTheory.CompanionTheory.SecJC.continuous_psiC.comp (by fun_prop)).smul ((GlobalTheory.CompanionTheory.SecJC.continuous_psiC.comp (by fun_prop)).smul (Continuous.clm_comp ?_ ?_))` and prove the remaining obligations. Conclude with `((Q.smooth ⊤).continuous_fderiv (by simp)).comp ((Rq M).continuous.comp (continuous_Zq h t))`. Conclude with `Continuous.clm_comp continuous_const (mulB.continuous.comp (continuous_fst.comp (continuous_Zq h t)))`.
-/
theorem continuous_dX (Q : Sw) (h : M22) (t : ℂ) (M : complexMatrix3) : Continuous (dX Q h t M) := by
  unfold dX
  refine (GlobalTheory.CompanionTheory.SecJC.continuous_psiC.comp (by fun_prop)).smul
    ((GlobalTheory.CompanionTheory.SecJC.continuous_psiC.comp (by fun_prop)).smul (Continuous.clm_comp ?_ ?_))
  · exact ((Q.smooth ⊤).continuous_fderiv (by simp)).comp ((Rq M).continuous.comp (continuous_Zq h t))
  · exact Continuous.clm_comp continuous_const (mulB.continuous.comp (continuous_fst.comp (continuous_Zq h t)))

/- English proof (translation)
Use `set Y := Rq M' (Zq h t p) with hY`. Establish `hb0 : 0 ≤ bI M` using `by linarith [one_le_bI M]`. Establish `hZ : ‖(Zq h t p).1‖ ≤ bI M * (1 + ‖Y‖)`. Combine the equalities or inequalities in the displayed calculation. Establish `h1 : ‖dX Q h t M' p‖ ≤ ‖mulB‖ * bI M * (‖fderiv ℝ (⇑Q) Y‖ * (1 + ‖Y‖))`.

Rewrite using `[dX, norm_smul, norm_smul, norm_psiC, norm_psiC, one_mul, one_mul]`. Combine the equalities or inequalities in the displayed calculation. Establish `h2` using `hS Y`. Rewrite `h2` using `[norm_iteratedFDeriv_one]`. Establish `h3 : ‖fderiv ℝ (⇑Q) Y‖ * (1 + ‖Y‖) ≤ cA h t M ^ 7 * S * (1 + ‖p‖) ^ (-(7 : ℝ))` using `le_div_one_add_pow_succ_of_mul_le (by positivity) (by positivity) (cA_nonneg h t M) (one_add_le_Zq hh ht hM' p) (by calc (1 + ‖Y‖) ^ 7 * (‖fderiv ℝ (⇑Q) Y‖ * (1 + ‖Y‖)) = (1 + ‖Y‖) ^ 8 * ‖fderiv ℝ (⇑Q) Y‖ := by ring _ ≤ S := h2)`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem dX_bound (Q : Sw) {h : M22} {t : ℂ} (hh : (Matrix.of h).det ≠ 0) (ht : t ≠ 0) {M M' : complexMatrix3}
    (hM' : M' ∈ nb M) {S : ℝ} (hS : ∀ Y : E5, (1 + ‖Y‖) ^ 8 * ‖iteratedFDeriv ℝ 1 (⇑Q) Y‖ ≤ S)
    (p : (Fin 2 → ℂ) × ℂ) :
    ‖dX Q h t M' p‖ ≤ ‖mulB‖ * bI M * (cA h t M ^ 7 * S) * (1 + ‖p‖) ^ (-(7 : ℝ)) := by
  set Y := Rq M' (Zq h t p) with hY
  have hb0 : 0 ≤ bI M := by linarith [one_le_bI M]
  have hZ : ‖(Zq h t p).1‖ ≤ bI M * (1 + ‖Y‖) := by
    calc ‖(Zq h t p).1‖ ≤ ‖Zq h t p‖ := norm_fst_le _
      _ ≤ bI M * ‖Y‖ := norm_le_Rq hM' _
      _ ≤ bI M * (1 + ‖Y‖) := by gcongr; linarith
  have h1 : ‖dX Q h t M' p‖ ≤ ‖mulB‖ * bI M * (‖fderiv ℝ (⇑Q) Y‖ * (1 + ‖Y‖)) := by
    rw [dX, norm_smul, norm_smul, norm_psiC, norm_psiC, one_mul, one_mul]
    calc ‖(fderiv ℝ (⇑Q) Y).comp (Dq (Zq h t p).1)‖ ≤ ‖fderiv ℝ (⇑Q) Y‖ * ‖Dq (Zq h t p).1‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖fderiv ℝ (⇑Q) Y‖ * (‖mulB‖ * ‖(Zq h t p).1‖) := by gcongr; exact norm_Dq_le _
      _ ≤ ‖fderiv ℝ (⇑Q) Y‖ * (‖mulB‖ * (bI M * (1 + ‖Y‖))) := by gcongr
      _ = _ := by ring
  have h2 := hS Y
  rw [norm_iteratedFDeriv_one] at h2
  have h3 : ‖fderiv ℝ (⇑Q) Y‖ * (1 + ‖Y‖) ≤ cA h t M ^ 7 * S * (1 + ‖p‖) ^ (-(7 : ℝ)) :=
    le_div_one_add_pow_succ_of_mul_le (by positivity) (by positivity) (cA_nonneg h t M) (one_add_le_Zq hh ht hM' p)
      (by calc (1 + ‖Y‖) ^ 7 * (‖fderiv ℝ (⇑Q) Y‖ * (1 + ‖Y‖)) = (1 + ‖Y‖) ^ 8 * ‖fderiv ℝ (⇑Q) Y‖ := by ring
        _ ≤ S := h2)
  calc ‖dX Q h t M' p‖ ≤ ‖mulB‖ * bI M * (‖fderiv ℝ (⇑Q) Y‖ * (1 + ‖Y‖)) := h1
    _ ≤ ‖mulB‖ * bI M * (cA h t M ^ 7 * S * (1 + ‖p‖) ^ (-(7 : ℝ))) := by gcongr
    _ = _ := by ring

/- English proof (translation)
Establish `hw` using `wirtinger Q hM (Zq h t p).1 (Zq h t p).2 m`. Simplify using `only [Prod.mk.eta] at hw`. Establish `e : dX Q h t M p m = psiC (-(1 * p.2)) * (psiC (-(1 * p.1 1)) * fderiv ℝ (⇑Q) (Rq M (Zq h t p)) (mulB (Zq h t p).1 m, 0))` using `rfl`. Rewrite using `[e, hw, Finset.mul_sum, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[Finset.mul_sum, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Unfold `fX`. Apply the tactic sequence `split_ifs <;> ring`.
-/
theorem dX_apply (Q : Sw) (h : M22) (t : ℂ) {M : complexMatrix3} (hM : (Matrix.of M).det ≠ 0)
    (p : (Fin 2 → ℂ) × ℂ) (m : complexMatrix3) :
    dX Q h t M p m = ∑ i, ∑ j, (ell M i j m * (fX (PH i j Q) h t M p - if i = j then fX Q h t M p else 0) +
      ellc M i j m * (fX (PA i j Q) h t M p - if i = j then fX Q h t M p else 0)) := by
  have hw := wirtinger Q hM (Zq h t p).1 (Zq h t p).2 m
  simp only [Prod.mk.eta] at hw
  have e : dX Q h t M p m =
      psiC (-(1 * p.2)) * (psiC (-(1 * p.1 1)) * fderiv ℝ (⇑Q) (Rq M (Zq h t p)) (mulB (Zq h t p).1 m, 0)) := rfl
  rw [e, hw, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  unfold fX
  split_ifs <;> ring

/- English proof (translation)
Use `split_ifs`. Rewrite using `[integral_const_mul, integral_sub hf hg]`. Simplify using `[integral_const_mul]`.
-/
theorem integral_term {α : Type*} [MeasurableSpace α] {μ : Measure α} (a : ℂ) (f g : α → ℂ)
    (hf : Integrable f μ) (hg : Integrable g μ) (c : Prop) [Decidable c] :
    ∫ x, a * (f x - if c then g x else 0) ∂μ = a * ((∫ x, f x ∂μ) - if c then ∫ x, g x ∂μ else 0) := by
  split_ifs
  · rw [integral_const_mul, integral_sub hf hg]
  · simp [integral_const_mul]

/- English proof (translation)
Take `⟨S, hS⟩ : ∃ S : ℝ, ∀ Y : E5, (1 + ‖Y‖) ^ 8 * ‖iteratedFDeriv ℝ 1 (⇑Q) Y‖ ≤ S` from `⟨_, fun Y => SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (8, 1)) le_rfl le_rfl Q Y⟩`. Establish `hmain` using `hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := volume) (F := fun M' p => fX Q h t M' p) (F' := fun M' p => dX Q h t M' p) (x₀ := M) (bound := fun p => ‖mulB‖ * bI M * (cA h t M ^ 7 * S) * (1 + ‖p‖) ^ (-(7 : ℝ))) (nb_mem hM) (Eventually.of_forall fun M' => (continuous_fX Q h …`. Establish `hint : Integrable (dX Q h t M)` using `(integrable_bound _).mono' (continuous_dX Q h t M).aestronglyMeasurable (ae_of_all _ fun p => dX_bound Q hh ht (self_mem_nb hM) hS p)`. Establish `hfi : ∀ Q' : Sw, Integrable (fX Q' h t M)` using `fun Q' => integrable_fX Q' hh ht hM`. Establish `hI : ∀ (Q' : Sw) (a : ℂ) (i j : Fin 3), Integrable (fun p => a * (fX Q' h t M p - if i = j then fX Q h t M p else 0))`.

Introduce `Q' a i j`. Use `Integrable.const_mul ((hfi Q').sub ?_) a` and prove the remaining obligations. Use `split_ifs`. Conclude with `hfi Q`. Conclude with `integrable_zero _ _ _`.

Establish `e : (∫ p, dX Q h t M p) = dInn Q h t M`. Use `ContinuousLinearMap.ext fun m => ?_` and prove the remaining obligations. Rewrite using `[ContinuousLinearMap.integral_apply hint m]`. Simplify using `only [dX_apply Q h t hM]`. Establish `hadd : ∀ i j : Fin 3, Integrable (fun p => ell M i j m * (fX (PH i j Q) h t M p - if i = j then fX Q h t M p else 0) + ellc M i j m * (fX (PA i j Q) h t M p - if i = j then fX Q h t M p else 0))` using `fun i j => (hI _ _ i j).add (hI _ _ i j)`.

Rewrite using `[integral_finset_sum _ fun i _ => integrable_finset_sum _ fun j _ => hadd i j]`. Simplify using `only [dInn, ContinuousLinearMap.sum_apply, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[integral_finset_sum _ fun j _ => hadd i j]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Rewrite using `[integral_add (hI _ _ i j) (hI _ _ i j), integral_term _ _ _ (hfi _) (hfi _), integral_term _ _ _ (hfi _) (hfi _), J_eq, J_eq, J_eq, mul_comm, mul_comm (ellc M i j m)]`. Rewrite `hmain` using `[e]`. Conclude with `hmain`.
-/
theorem hasFDerivAt_J (Q : Sw) {h : M22} {t : ℂ} (hh : (Matrix.of h).det ≠ 0) (ht : t ≠ 0) {M : complexMatrix3}
    (hM : (Matrix.of M).det ≠ 0) : HasFDerivAt (fun M' => J Q M' h t) (dInn Q h t M) M := by
  obtain ⟨S, hS⟩ : ∃ S : ℝ, ∀ Y : E5, (1 + ‖Y‖) ^ 8 * ‖iteratedFDeriv ℝ 1 (⇑Q) Y‖ ≤ S :=
    ⟨_, fun Y => SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (8, 1)) le_rfl le_rfl Q Y⟩
  have hmain := hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := volume)
    (F := fun M' p => fX Q h t M' p) (F' := fun M' p => dX Q h t M' p) (x₀ := M)
    (bound := fun p => ‖mulB‖ * bI M * (cA h t M ^ 7 * S) * (1 + ‖p‖) ^ (-(7 : ℝ)))
    (nb_mem hM) (Eventually.of_forall fun M' => (continuous_fX Q h t M').aestronglyMeasurable)
    (integrable_fX Q hh ht hM) (continuous_dX Q h t M).aestronglyMeasurable
    (ae_of_all _ fun p M' hM' => dX_bound Q hh ht hM' hS p)
    (integrable_bound _)
    (ae_of_all _ fun p M' _ => hasFDerivAt_fX Q h t M' p)
  have hint : Integrable (dX Q h t M) :=
    (integrable_bound _).mono' (continuous_dX Q h t M).aestronglyMeasurable
      (ae_of_all _ fun p => dX_bound Q hh ht (self_mem_nb hM) hS p)
  have hfi : ∀ Q' : Sw, Integrable (fX Q' h t M) := fun Q' => integrable_fX Q' hh ht hM
  have hI : ∀ (Q' : Sw) (a : ℂ) (i j : Fin 3),
      Integrable (fun p => a * (fX Q' h t M p - if i = j then fX Q h t M p else 0)) := by
    intro Q' a i j
    refine Integrable.const_mul ((hfi Q').sub ?_) a
    split_ifs
    · exact hfi Q
    · exact integrable_zero _ _ _
  have e : (∫ p, dX Q h t M p) = dInn Q h t M := by
    refine ContinuousLinearMap.ext fun m => ?_
    rw [ContinuousLinearMap.integral_apply hint m]
    simp only [dX_apply Q h t hM]
    have hadd : ∀ i j : Fin 3, Integrable (fun p =>
        ell M i j m * (fX (PH i j Q) h t M p - if i = j then fX Q h t M p else 0) +
        ellc M i j m * (fX (PA i j Q) h t M p - if i = j then fX Q h t M p else 0)) :=
      fun i j => (hI _ _ i j).add (hI _ _ i j)
    rw [integral_finset_sum _ fun i _ => integrable_finset_sum _ fun j _ => hadd i j]
    simp only [dInn, ContinuousLinearMap.sum_apply, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finset_sum _ fun j _ => hadd i j]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_add (hI _ _ i j) (hI _ _ i j), integral_term _ _ _ (hfi _) (hfi _),
      integral_term _ _ _ (hfi _) (hfi _), J_eq, J_eq, J_eq, mul_comm, mul_comm (ellc M i j m)]
  rw [e] at hmain
  exact hmain

def dG (k : ℕ) (Q : Sw) (M : complexMatrix3) (p : M22 × ℂ) : complexMatrix3 →L[ℝ] ℂ :=
  ∑ i, ∑ j, ((G k (PH i j Q) M p - if i = j then G k Q M p else 0) • ell M i j +
    (G k (PA i j Q) M p - if i = j then G k Q M p else 0) • ellc M i j)

/- English proof (translation)
The claim follows from `(J_meas Q hM).mul (wt_meas k)`.
-/
theorem G_meas (k : ℕ) (Q : Sw) {M : complexMatrix3} (hM : (Matrix.of M).det ≠ 0) :
    AEStronglyMeasurable (G k Q M) volume :=
  (J_meas Q hM).mul (wt_meas k)

/- English proof (translation)
Establish `h1` using `hC M' hM' p.1 p.2 hp.1 hp.2`. Establish `h2` using `wt_norm k p`. Rewrite using `[G, norm_mul]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem G_bound (k : ℕ) {Q : Sw} {M M' : complexMatrix3} {C : ℝ} {N : ℕ}
    (hC : ∀ M' ∈ nb M, ∀ (h : M22) (t : ℂ), (Matrix.of h).det ≠ 0 → t ≠ 0 → ‖J Q M' h t‖ ≤ C * jm N h t 1 1)
    (hM' : M' ∈ nb M) {p : M22 × ℂ} (hp : (Matrix.of p.1).det ≠ 0 ∧ p.2 ≠ 0) :
    ‖G k Q M' p‖ ≤ C * ((‖(Matrix.of p.1).det‖ ^ 2)⁻¹ * jm N p.1 p.2 1 1) := by
  have h1 := hC M' hM' p.1 p.2 hp.1 hp.2
  have h2 := wt_norm k p
  rw [G, norm_mul]
  calc ‖J Q M' p.1 p.2‖ * ‖wt k p‖ ≤ (C * jm N p.1 p.2 1 1) * (‖(Matrix.of p.1).det‖ ^ 2)⁻¹ :=
        mul_le_mul h1 h2 (norm_nonneg _) ((norm_nonneg _).trans h1)
    _ = _ := by ring

/- English proof (translation)
Establish `h` using `(hasFDerivAt_J Q hp.1 hp.2 hM).mul_const (wt k p)`. Establish `e : wt k p • dInn Q p.1 p.2 M = dG k Q M p`. Simplify using `only [dInn, dG, G, Finset.smul_sum, smul_add, smul_smul]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Apply the tactic sequence `split_ifs <;> congr 2 <;> ring`.

Rewrite `h` using `[e]`. Conclude with `h`.
-/
theorem hasFDerivAt_G (k : ℕ) (Q : Sw) {M : complexMatrix3} (hM : (Matrix.of M).det ≠ 0) {p : M22 × ℂ}
    (hp : (Matrix.of p.1).det ≠ 0 ∧ p.2 ≠ 0) : HasFDerivAt (fun M' => G k Q M' p) (dG k Q M p) M := by
  have h := (hasFDerivAt_J Q hp.1 hp.2 hM).mul_const (wt k p)
  have e : wt k p • dInn Q p.1 p.2 M = dG k Q M p := by
    simp only [dInn, dG, G, Finset.smul_sum, smul_add, smul_smul]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    split_ifs <;> congr 2 <;> ring
  rw [e] at h
  exact h

/- English proof (translation)
Take `⟨N₀, hN₀⟩` from `hMj 1 one_pos`. Take `⟨C₀, hC₀⟩` from `hN₀ N₀ le_rfl`. Establish `hmaj` using `(hC₀ 1 1 one_ne_zero one_ne_zero).1`. Use `set maj : M22 × ℂ → ℝ := fun p => (‖(Matrix.of p.1).det‖ ^ 2)⁻¹ * jm N₀ p.1 p.2 1 1 with hmajdef`. Establish `hInt : ∀ Q : Sw, Integrable (G k Q M)`.

Introduce `Q`. Take `⟨C, hC⟩` from `J_bound hI N₀ Q hM`. Use `(hmaj.const_mul C).mono' (G_meas k Q hM) ?_` and prove the remaining obligations. Use `filter_upwards [ae_good] with p hp`. Conclude with `G_bound k hC (self_mem_nb hM) hp`.

Use `choose CH hCH using fun ij : Fin 3 × Fin 3 => J_bound hI N₀ (PH ij.1 ij.2 Ψ) hM`. Use `choose CA hCA using fun ij : Fin 3 × Fin 3 => J_bound hI N₀ (PA ij.1 ij.2 Ψ) hM`. Take `⟨C, hC⟩` from `J_bound hI N₀ Ψ hM`. Use `set c : ℝ := ‖mul3‖ * (‖minv M‖ + 1) with hc`. Establish `hc0 : 0 ≤ c` using `by positivity`.

Use `set K : ℝ := ∑ i, ∑ j, (((|CH (i, j)| + |C|) * c) + ((|CA (i, j)| + |C|) * c)) with hK`. Establish `hmaj0 : ∀ p, (Matrix.of p.1).det ≠ 0 ∧ p.2 ≠ 0 → 0 ≤ maj p`. Introduce `p hp`. Simplify using `only [hmajdef, jm]`. Check the signs of the components of the expression.

Establish `hbound : ∀ M' ∈ nb M, ∀ p : M22 × ℂ, (Matrix.of p.1).det ≠ 0 ∧ p.2 ≠ 0 → ‖dG k Ψ M' p‖ ≤ K * maj p`. Introduce `M' hM' p hp`. Establish `hm` using `hmaj0 p hp`. Establish `term : ∀ (Q : Sw) (D : ℝ) (i j : Fin 3) (L : complexMatrix3 →L[ℝ] ℂ), ‖L‖ ≤ c → (∀ M' ∈ nb M, ∀ (h : M22) (t : ℂ), (Matrix.of h).det ≠ 0 → t ≠ 0 → ‖J Q M' h t‖ ≤ D * jm N₀ h t 1 1) → ‖(G k Q M' p - if i = j then G k Ψ M' p else 0) • L‖ ≤ (|D| + |C|) * c * maj p`. Introduce `Q D i j L hL hD`.

Rewrite using `[norm_smul]`. Establish `h1 : ‖G k Q M' p‖ ≤ |D| * maj p` using `(G_bound k hD hM' hp).trans (by gcongr; exact le_abs_self D)`. Establish `h2 : ‖if i = j then G k Ψ M' p else 0‖ ≤ |C| * maj p` using `by split_ifs`. Conclude with `(G_bound k hC hM' hp).trans (by gcongr; exact le_abs_self C)`. Rewrite using `[norm_zero]`.

Check the signs of the components of the expression. Combine the equalities or inequalities in the displayed calculation. Conclude with `(norm_sub_le _ _).trans (add_le_add h1 h2)`. Use `_ = _ := by ring`. Rewrite using `[dG, hK, Finset.sum_mul]`.

Use `(norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)` and prove the remaining obligations. Rewrite using `[Finset.sum_mul]`. Use `(norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)` and prove the remaining obligations. Rewrite using `[add_mul]`. Conclude with `(norm_add_le _ _).trans (add_le_add (term _ _ i j _ (nb_ell hM' i j) (hCH (i, j))) (term _ _ i j _ (nb_ellc hM' i j) (hCA (i, j))))`.

Establish `hsm : ∀ (Q : Sw) (i j : Fin 3) (L : complexMatrix3 →L[ℝ] ℂ), AEStronglyMeasurable (fun p => (G k Q M p - if i = j then G k Ψ M p else 0) • L) volume`. Introduce `Q i j L`. Use `AEStronglyMeasurable.smul_const ?_ L` and prove the remaining obligations. Use `(G_meas k Q hM).sub ?_` and prove the remaining obligations. Use `split_ifs`.

Conclude with `G_meas k Ψ hM`. Conclude with `aestronglyMeasurable_const`. Establish `hmeas : AEStronglyMeasurable (dG k Ψ M) volume`. Establish `: dG k Ψ M = fun p => ∑ i, ∑ j, ((G k (PH i j Ψ) M p - if i = j then G k Ψ M p else 0) • ell M i j + (G k (PA i j Ψ) M p - if i = j then G k Ψ M p else 0) • ellc M i j)` using `rfl`. Rewrite using `[this]`.

Use `Finset.aestronglyMeasurable_fun_sum _ fun i _ => Finset.aestronglyMeasurable_fun_sum _ fun j _ => ?_` and prove the remaining obligations. Conclude with `(hsm _ i j _).add (hsm _ i j _)`. Establish `hmain` using `hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := volume) (F := fun M' p => G k Ψ M' p) (F' := fun M' p => dG k Ψ M' p) (x₀ := M) (bound := fun p => K * maj p) (nb_mem hM) (by filter_upwards [nb_mem hM] with M' hM' using G_meas k Ψ (nb_det hM')) (hInt Ψ) hmeas (by filter_upwar …`. Establish `hT : ∀ (Q : Sw) (i j : Fin 3) (L : complexMatrix3 →L[ℝ] ℂ), Integrable (fun p => (G k Q M p - if i = j then G k Ψ M p else 0) • L) ∧ ∫ p, (G k Q M p - if i = j then G k Ψ M p else 0) • L = ((∫ p, G k Q M p) - if i = j then ∫ p, G k Ψ M p else 0) • L`. Introduce `Q i j L`.

Establish `hi : Integrable (fun p => G k Q M p - if i = j then G k Ψ M p else 0)`. Use `(hInt Q).sub ?_` and prove the remaining obligations. Use `split_ifs`. Conclude with `hInt Ψ`. Conclude with `integrable_zero _ _ _`.

Use `⟨hi.smul_const L, ?_⟩` and prove the remaining obligations. Rewrite using `[integral_smul_const]`. Use `congr 1`. Use `split_ifs`. Conclude with `integral_sub (hInt Q) (hInt Ψ)`.

Simplify using the standard rewrite rules. Establish `e : (∫ p, dG k Ψ M p) = ∑ i, ∑ j, (((∫ p, G k (PH i j Ψ) M p) - if i = j then ∫ p, G k Ψ M p else 0) • ell M i j + ((∫ p, G k (PA i j Ψ) M p) - if i = j then ∫ p, G k Ψ M p else 0) • ellc M i j)`. Establish `hadd : ∀ i j : Fin 3, Integrable (fun p => (G k (PH i j Ψ) M p - if i = j then G k Ψ M p else 0) • ell M i j + (G k (PA i j Ψ) M p - if i = j then G k Ψ M p else 0) • ellc M i j)` using `fun i j => (hT _ i j _).1.add (hT _ i j _).1`. Simplify using `only [dG]`. Rewrite using `[integral_finset_sum _ fun i _ => integrable_finset_sum _ fun j _ => hadd i j]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[integral_finset_sum _ fun j _ => hadd i j]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[integral_add (hT _ i j _).1 (hT _ i j _).1, (hT _ i j _).2, (hT _ i j _).2]`. Rewrite `hmain` using `[e]`.

Conclude with `hmain`.
-/
theorem hasFDerivAt_intG (hI : IbpBound) (hMj : MajScaled) (k : ℕ) (Ψ : Sw) {M : complexMatrix3}
    (hM : (Matrix.of M).det ≠ 0) :
    HasFDerivAt (fun M' => ∫ p, G k Ψ M' p)
      (∑ i, ∑ j, (((∫ p, G k (PH i j Ψ) M p) - if i = j then ∫ p, G k Ψ M p else 0) • ell M i j +
        ((∫ p, G k (PA i j Ψ) M p) - if i = j then ∫ p, G k Ψ M p else 0) • ellc M i j)) M := by
  obtain ⟨N₀, hN₀⟩ := hMj 1 one_pos
  obtain ⟨C₀, hC₀⟩ := hN₀ N₀ le_rfl
  have hmaj := (hC₀ 1 1 one_ne_zero one_ne_zero).1
  set maj : M22 × ℂ → ℝ := fun p => (‖(Matrix.of p.1).det‖ ^ 2)⁻¹ * jm N₀ p.1 p.2 1 1 with hmajdef
  have hInt : ∀ Q : Sw, Integrable (G k Q M) := by
    intro Q
    obtain ⟨C, hC⟩ := J_bound hI N₀ Q hM
    refine (hmaj.const_mul C).mono' (G_meas k Q hM) ?_
    filter_upwards [ae_good] with p hp
    exact G_bound k hC (self_mem_nb hM) hp
  choose CH hCH using fun ij : Fin 3 × Fin 3 => J_bound hI N₀ (PH ij.1 ij.2 Ψ) hM
  choose CA hCA using fun ij : Fin 3 × Fin 3 => J_bound hI N₀ (PA ij.1 ij.2 Ψ) hM
  obtain ⟨C, hC⟩ := J_bound hI N₀ Ψ hM
  set c : ℝ := ‖mul3‖ * (‖minv M‖ + 1) with hc
  have hc0 : 0 ≤ c := by positivity
  set K : ℝ := ∑ i, ∑ j, (((|CH (i, j)| + |C|) * c) + ((|CA (i, j)| + |C|) * c)) with hK
  have hmaj0 : ∀ p, (Matrix.of p.1).det ≠ 0 ∧ p.2 ≠ 0 → 0 ≤ maj p := by
    intro p hp
    simp only [hmajdef, jm]
    positivity
  have hbound : ∀ M' ∈ nb M, ∀ p : M22 × ℂ, (Matrix.of p.1).det ≠ 0 ∧ p.2 ≠ 0 → ‖dG k Ψ M' p‖ ≤ K * maj p := by
    intro M' hM' p hp
    have hm := hmaj0 p hp
    have term : ∀ (Q : Sw) (D : ℝ) (i j : Fin 3) (L : complexMatrix3 →L[ℝ] ℂ), ‖L‖ ≤ c →
        (∀ M' ∈ nb M, ∀ (h : M22) (t : ℂ), (Matrix.of h).det ≠ 0 → t ≠ 0 → ‖J Q M' h t‖ ≤ D * jm N₀ h t 1 1) →
        ‖(G k Q M' p - if i = j then G k Ψ M' p else 0) • L‖ ≤ (|D| + |C|) * c * maj p := by
      intro Q D i j L hL hD
      rw [norm_smul]
      have h1 : ‖G k Q M' p‖ ≤ |D| * maj p :=
        (G_bound k hD hM' hp).trans (by gcongr; exact le_abs_self D)
      have h2 : ‖if i = j then G k Ψ M' p else 0‖ ≤ |C| * maj p := by
        split_ifs
        · exact (G_bound k hC hM' hp).trans (by gcongr; exact le_abs_self C)
        · rw [norm_zero]; positivity
      calc ‖G k Q M' p - if i = j then G k Ψ M' p else 0‖ * ‖L‖
          ≤ (|D| * maj p + |C| * maj p) * c := by
            gcongr
            exact (norm_sub_le _ _).trans (add_le_add h1 h2)
        _ = _ := by ring
    rw [dG, hK, Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [add_mul]
    exact (norm_add_le _ _).trans (add_le_add (term _ _ i j _ (nb_ell hM' i j) (hCH (i, j)))
      (term _ _ i j _ (nb_ellc hM' i j) (hCA (i, j))))
  have hsm : ∀ (Q : Sw) (i j : Fin 3) (L : complexMatrix3 →L[ℝ] ℂ),
      AEStronglyMeasurable (fun p => (G k Q M p - if i = j then G k Ψ M p else 0) • L) volume := by
    intro Q i j L
    refine AEStronglyMeasurable.smul_const ?_ L
    refine (G_meas k Q hM).sub ?_
    split_ifs
    · exact G_meas k Ψ hM
    · exact aestronglyMeasurable_const
  have hmeas : AEStronglyMeasurable (dG k Ψ M) volume := by
    have : dG k Ψ M = fun p => ∑ i, ∑ j, ((G k (PH i j Ψ) M p - if i = j then G k Ψ M p else 0) • ell M i j +
        (G k (PA i j Ψ) M p - if i = j then G k Ψ M p else 0) • ellc M i j) := rfl
    rw [this]
    refine Finset.aestronglyMeasurable_fun_sum _ fun i _ => Finset.aestronglyMeasurable_fun_sum _ fun j _ => ?_
    exact (hsm _ i j _).add (hsm _ i j _)
  have hmain := hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := volume)
    (F := fun M' p => G k Ψ M' p) (F' := fun M' p => dG k Ψ M' p) (x₀ := M)
    (bound := fun p => K * maj p)
    (nb_mem hM) (by filter_upwards [nb_mem hM] with M' hM' using G_meas k Ψ (nb_det hM')) (hInt Ψ) hmeas
    (by filter_upwards [ae_good] with p hp M' hM' using hbound M' hM' p hp)
    (hmaj.const_mul K)
    (by filter_upwards [ae_good] with p hp M' hM' using hasFDerivAt_G k Ψ (nb_det hM') hp)
  have hT : ∀ (Q : Sw) (i j : Fin 3) (L : complexMatrix3 →L[ℝ] ℂ),
      Integrable (fun p => (G k Q M p - if i = j then G k Ψ M p else 0) • L) ∧
      ∫ p, (G k Q M p - if i = j then G k Ψ M p else 0) • L =
        ((∫ p, G k Q M p) - if i = j then ∫ p, G k Ψ M p else 0) • L := by
    intro Q i j L
    have hi : Integrable (fun p => G k Q M p - if i = j then G k Ψ M p else 0) := by
      refine (hInt Q).sub ?_
      split_ifs
      · exact hInt Ψ
      · exact integrable_zero _ _ _
    refine ⟨hi.smul_const L, ?_⟩
    rw [integral_smul_const]
    congr 1
    split_ifs
    · exact integral_sub (hInt Q) (hInt Ψ)
    · simp
  have e : (∫ p, dG k Ψ M p) = ∑ i, ∑ j, (((∫ p, G k (PH i j Ψ) M p) - if i = j then ∫ p, G k Ψ M p else 0) • ell M i j +
        ((∫ p, G k (PA i j Ψ) M p) - if i = j then ∫ p, G k Ψ M p else 0) • ellc M i j) := by
    have hadd : ∀ i j : Fin 3, Integrable (fun p => (G k (PH i j Ψ) M p - if i = j then G k Ψ M p else 0) • ell M i j +
        (G k (PA i j Ψ) M p - if i = j then G k Ψ M p else 0) • ellc M i j) :=
      fun i j => (hT _ i j _).1.add (hT _ i j _).1
    simp only [dG]
    rw [integral_finset_sum _ fun i _ => integrable_finset_sum _ fun j _ => hadd i j]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finset_sum _ fun j _ => hadd i j]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_add (hT _ i j _).1 (hT _ i j _).1, (hT _ i j _).2, (hT _ i j _).2]
  rw [e] at hmain
  exact hmain

/- English proof (translation)
Simplify using `only [Fin.sum_univ_three]`. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.
-/
theorem alg (a b P R : Fin 3 → Fin 3 → ℂ) (I D : ℂ) :
    D * (∑ i, ∑ j, ((P i j - if i = j then I else 0) * a i j + (R i j - if i = j then I else 0) * b i j)) +
      I * (D * ∑ i, (a i i + b i i)) = ∑ i, ∑ j, (a i j * (D * P i j) + b i j * (D * R i j)) := by
  simp only [Fin.sum_univ_three]
  simp
  ring

/- English proof (translation)
Introduce `hI hMj k hk Ψ g`. Establish `hF` using `GlobalTheory.CompanionTheory.LCSecFub.secFub_of_secJ (GlobalTheory.CompanionTheory.SecJC.main hI hMj)`. Use `set M : complexMatrix3 := Matrix.of.symm (g : Matrix (Fin 3) (Fin 3) ℂ) with hMdef`. Establish `hM : (Matrix.of M).det ≠ 0`. Use `(Matrix.isUnits_det_units g).ne_zero` as an intermediate fact.

Simplify `this` using `[hMdef]`. Establish `hg : gl M hM = g` using `Units.ext rfl`. Establish `hsec : ∀ (M' : complexMatrix3) (hM' : (Matrix.of M').det ≠ 0) (Q : Sw), sec k Q (gl M' hM') = ((‖(Matrix.of M').det‖ ^ 2 : ℝ) : ℂ) * ∫ p, G k Q M' p`. Introduce `M' hM' Q`. Rewrite using `[hF k hk Q (gl M' hM')]`.

Simplify using `only [secI_eq_G _ _ _ hM', gl_val]`. Establish `hext : extC (sec k Ψ) =ᶠ[𝓝 M] fun M' => ((‖(Matrix.of M').det‖ ^ 2 : ℝ) : ℂ) * ∫ p, G k Ψ M' p` using `by filter_upwards [nb_mem hM] with M' hM'`. Rewrite using `[extC, dif_pos (nb_det hM')]`. Conclude with `hsec M' (nb_det hM') Ψ`. Establish `hD` using `((hasFDerivAt_normSq_det hM).mul (hasFDerivAt_intG hI hMj k Ψ hM)).congr_of_eventuallyEq hext`.

Use `⟨_, hD, fun m => ?_⟩` and prove the remaining obligations. Establish `hinv : (((g⁻¹ : GL (Fin 3) ℂ) : Matrix (Fin 3) (Fin 3) ℂ)) = (Matrix.of M)⁻¹`. Rewrite using `[Matrix.coe_units_inv]`. Both sides reduce to the same expression. Simplify using `only [hinv, ← ell_apply, ← ellc_apply]`.

Use `alg (fun i j => ell M i j m) (fun i j => ellc M i j m) (fun i j => ∫ p, G k (PH i j Ψ) M p) (fun i j => ∫ p, G k (PA i j Ψ) M p) (∫ p, G k Ψ M p) ((‖(Matrix.of M).det‖ ^ 2 : ℝ) : ℂ)` as an intermediate fact. Simplify using `only [← hg, hsec M hM]`. Simplify using `only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.sum_apply, smul_eq_mul]`. Conclude with `this`.
-/
theorem main : Ad3.K.LC.B.IbpBound → Ad3.K.LC.B.MajScaled → Ad3.K.LC.HasDer := by
  intro hI hMj k hk Ψ g
  have hF := GlobalTheory.CompanionTheory.LCSecFub.secFub_of_secJ (GlobalTheory.CompanionTheory.SecJC.main hI hMj)
  set M : complexMatrix3 := Matrix.of.symm (g : Matrix (Fin 3) (Fin 3) ℂ) with hMdef
  have hM : (Matrix.of M).det ≠ 0 := by
    have := (Matrix.isUnits_det_units g).ne_zero
    simpa [hMdef] using this
  have hg : gl M hM = g := Units.ext rfl
  have hsec : ∀ (M' : complexMatrix3) (hM' : (Matrix.of M').det ≠ 0) (Q : Sw), sec k Q (gl M' hM') =
      ((‖(Matrix.of M').det‖ ^ 2 : ℝ) : ℂ) * ∫ p, G k Q M' p := by
    intro M' hM' Q
    rw [hF k hk Q (gl M' hM')]
    simp only [secI_eq_G _ _ _ hM', gl_val]
  have hext : extC (sec k Ψ) =ᶠ[𝓝 M] fun M' => ((‖(Matrix.of M').det‖ ^ 2 : ℝ) : ℂ) * ∫ p, G k Ψ M' p := by
    filter_upwards [nb_mem hM] with M' hM'
    rw [extC, dif_pos (nb_det hM')]
    exact hsec M' (nb_det hM') Ψ
  have hD := ((hasFDerivAt_normSq_det hM).mul (hasFDerivAt_intG hI hMj k Ψ hM)).congr_of_eventuallyEq hext
  refine ⟨_, hD, fun m => ?_⟩
  have hinv : (((g⁻¹ : GL (Fin 3) ℂ) : Matrix (Fin 3) (Fin 3) ℂ)) = (Matrix.of M)⁻¹ := by
    rw [Matrix.coe_units_inv]; rfl
  simp only [hinv, ← ell_apply, ← ellc_apply]
  have := alg (fun i j => ell M i j m) (fun i j => ellc M i j m) (fun i j => ∫ p, G k (PH i j Ψ) M p)
    (fun i j => ∫ p, G k (PA i j Ψ) M p) (∫ p, G k Ψ M p) ((‖(Matrix.of M).det‖ ^ 2 : ℝ) : ℂ)
  simp only [← hg, hsec M hM]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.sum_apply, smul_eq_mul]
  exact this

end GlobalTheory.CompanionTheory.LCDer
