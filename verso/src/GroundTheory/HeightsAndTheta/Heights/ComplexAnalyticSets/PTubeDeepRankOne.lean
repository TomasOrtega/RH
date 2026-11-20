import Mathlib
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.LintegralImageEqLintegralNormSqDetMul
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PartsAlg
import ReciprocityTheory.AnalyticForms.PotentialTheory.HessCIsHermitian
import ReciprocityTheory.AnalyticForms.AnalyticCharts.Osgood
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PMaDensLeibniz
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StTubeDeepRankOne
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Matrix ComplexSets ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A Filter Topology

noncomputable section

namespace TubeDeepRankOne

/- English proof (translation)
Rewrite using `[mdisc_eq_sum_perm]`. Use `congr 1`. Establish `hterm : ∀ σ : Equiv.Perm (Fin D), (Matrix.of fun i j => vecMulVec (u (σ j)) (star (u (σ j))) i j).det = (Matrix.of u).det * ((Equiv.Perm.sign σ : ℤ) * ∏ j, star (u (σ j) j))`. Introduce `σ`. Establish `h1 : (Matrix.of fun i j => vecMulVec (u (σ j)) (star (u (σ j))) i j) = Matrix.of fun i j => (fun j => star (u (σ j) j)) j * ((Matrix.of u)ᵀ.submatrix id σ) i j`.

Use extensionality with `i j`. Simplify using `[vecMulVec_apply, mul_comm]`. Rewrite using `[h1, det_mul_row, det_permute', det_transpose]`. Expand and normalize the polynomial expressions, which then agree. Repeatedly rewrite using `[hterm]`.

Rewrite using `[← Finset.mul_sum]`. Establish `hconj : ∑ σ : Equiv.Perm (Fin D), ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ j, star (u (σ j) j) = starRingEnd ℂ (Matrix.of u).det`. Rewrite using `[RingHom.map_det, det_apply']`. Both sides reduce to the same expression. Rewrite using `[hconj, Complex.mul_conj]`.
-/
theorem mdisc_vecMulVec {D : ℕ} (u : Fin D → Fin D → ℂ) :
    mdisc (fun k => vecMulVec (u k) (star (u k))) =
      (1 / (D.factorial : ℂ)) * (Complex.normSq (Matrix.of u).det : ℂ) := by
  rw [mdisc_eq_sum_perm]
  congr 1
  have hterm : ∀ σ : Equiv.Perm (Fin D),
      (Matrix.of fun i j => vecMulVec (u (σ j)) (star (u (σ j))) i j).det =
        (Matrix.of u).det * ((Equiv.Perm.sign σ : ℤ) * ∏ j, star (u (σ j) j)) := by
    intro σ
    have h1 : (Matrix.of fun i j => vecMulVec (u (σ j)) (star (u (σ j))) i j) =
        Matrix.of fun i j => (fun j => star (u (σ j) j)) j * ((Matrix.of u)ᵀ.submatrix id σ) i j := by
      ext i j
      simp [vecMulVec_apply, mul_comm]
    rw [h1, det_mul_row, det_permute', det_transpose]
    ring
  simp_rw [hterm]
  rw [← Finset.mul_sum]
  have hconj : ∑ σ : Equiv.Perm (Fin D), ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ j, star (u (σ j) j) =
      starRingEnd ℂ (Matrix.of u).det := by
    rw [RingHom.map_det, det_apply']
    rfl
  rw [hconj, Complex.mul_conj]

/- English proof (translation)
Take `⟨L, hL⟩` from `exists_multilinearMap_eq_mdisc (D := d + 1)`. Rewrite using `[← hL]`. Establish `h` using `(L.curryLeft A₀).map_sum (fun (_ : Fin d) m => B m)`. Simplify `h` using `[MultilinearMap.curryLeft_apply]`.
-/
theorem mdisc_cons_sum {d n : ℕ} (A₀ : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ)
    (B : Fin n → Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) :
    mdisc (Fin.cons A₀ (fun _ => ∑ m, B m) : Fin (d + 1) → Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) =
      ∑ I : Fin d → Fin n,
        mdisc (Fin.cons A₀ (fun i => B (I i)) : Fin (d + 1) → Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) := by
  obtain ⟨L, hL⟩ := exists_multilinearMap_eq_mdisc (D := d + 1)
  rw [← hL]
  have h := (L.curryLeft A₀).map_sum (fun (_ : Fin d) m => B m)
  simpa [MultilinearMap.curryLeft_apply] using h

/- English proof (translation)
Establish `h : (euclPot : (Fin N → ℂ) → ℝ) = fun w => ∑ i, Complex.normSq (w i)`. Use function extensionality and compare the values at `w`. Simplify using `[euclPot, Complex.normSq_eq_norm_sq]`. Rewrite using `[h]`. Conclude with `hessC_sum_normSq z`.
-/
theorem hessC_euclPot_eq_one {N : ℕ} (z : Fin N → ℂ) : hessC (euclPot : (Fin N → ℂ) → ℝ) z = 1 := by
  have h : (euclPot : (Fin N → ℂ) → ℝ) = fun w => ∑ i, Complex.normSq (w i) := by
    funext w
    simp [euclPot, Complex.normSq_eq_norm_sq]
  rw [h]
  exact hessC_sum_normSq z

/- English proof (translation)
Establish `hE2 : ContDiffAt ℝ 2 (euclPot : (Fin n → ℂ) → ℝ) (s y)` using `((contDiff_euclPot n).of_le (WithTop.coe_le_coe.2 le_top)).contDiffAt`. Rewrite using `[hessC_comp _ s y hs hE2, hessC_euclPot_eq_one, Matrix.mul_one]`. Use extensionality with `i j`. Simplify using `[Matrix.mul_apply, vecMulVec_apply, Matrix.sum_apply]`.
-/
theorem hessC_euclPot_comp {n D : ℕ} (s : (Fin D → ℂ) → Fin n → ℂ) (y : Fin D → ℂ)
    (hs : AnalyticAt ℂ s y) :
    hessC (euclPot ∘ s) y = ∑ m, vecMulVec (fun j => jacC s y m j) (star fun j => jacC s y m j) := by
  have hE2 : ContDiffAt ℝ 2 (euclPot : (Fin n → ℂ) → ℝ) (s y) :=
    ((contDiff_euclPot n).of_le (WithTop.coe_le_coe.2 le_top)).contDiffAt
  rw [hessC_comp _ s y hs hE2, hessC_euclPot_eq_one, Matrix.mul_one]
  ext i j
  simp [Matrix.mul_apply, vecMulVec_apply, Matrix.sum_apply]

/- English proof (translation)
Establish `h` using `AnalyticAt.aeval_mvPolynomial (𝕜 := ℂ) (f := fun z : Fin m → ℂ => z) (z := y) (fun i => (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin m => ℂ) i).analyticAt y) P`. Simplify `h` using `[MvPolynomial.coe_aeval_eq_eval]`.
-/
theorem analyticAt_eval_poly {m : ℕ} (P : MvPolynomial (Fin m) ℂ) (y : Fin m → ℂ) :
    AnalyticAt ℂ (fun z => eval z P) y := by
  have h := AnalyticAt.aeval_mvPolynomial (𝕜 := ℂ) (f := fun z : Fin m → ℂ => z) (z := y)
    (fun i => (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin m => ℂ) i).analyticAt y) P
  simpa [MvPolynomial.coe_aeval_eq_eval] using h

/- English proof (translation)
Establish `hg` using `analyticAt_eval_poly P y`. Establish `hgd : HasFDerivAt (fun z => eval z P) (fderiv ℂ (fun z => eval z P) y) y` using `hg.differentiableAt.hasFDerivAt`. Establish `h1` using `(hgd.restrictScalars ℝ).norm_sq`. Establish `hne : ‖eval y P‖ ^ 2 ≠ 0` using `pow_ne_zero 2 (norm_ne_zero_iff.2 hP)`. Establish `h2` using `h1.log hne`.

Establish `hf : fderiv ℝ (logAbsSq P) y = _` using `h2.fderiv`. Use `set c := fderiv ℂ (fun z => eval z P) y (Pi.single j 1) with hc`. Use `set p := eval y P with hp`. Use `set w := c * (starRingEnd ℂ) p with hw`. Establish `hI : fderiv ℂ (fun z => eval z P) y (Complex.I • Pi.single j 1) = Complex.I * c`.

Rewrite using `[map_smul, smul_eq_mul]`. Establish `hN : Complex.normSq p ≠ 0` using `(Complex.normSq_pos.2 hP).ne'`. Establish `e1 : fderiv ℝ (logAbsSq P) y (Pi.single j 1) = 2 * w.re / Complex.normSq p`. Rewrite using `[hf]`. Simplify using `only [_root_.smul_apply, ContinuousLinearMap.comp_apply, innerSL_apply_apply, ContinuousLinearMap.coe_restrictScalars', Complex.inner, smul_eq_mul, nsmul_eq_mul, Complex.normSq_eq_norm_sq]`.

Rewrite using `[← hc, hw]`. Expand and normalize the polynomial expressions, which then agree. Establish `e2 : fderiv ℝ (logAbsSq P) y (Complex.I • Pi.single j 1) = -(2 * w.im / Complex.normSq p)`. Rewrite using `[hf]`. Simplify using `only [_root_.smul_apply, ContinuousLinearMap.comp_apply, innerSL_apply_apply, ContinuousLinearMap.coe_restrictScalars', Complex.inner, smul_eq_mul, nsmul_eq_mul, Complex.normSq_eq_norm_sq]`.

Rewrite using `[hI, hw]`. Simplify using `only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]`. Expand and normalize the polynomial expressions, which then agree. Establish `hcp : c / p = w / (Complex.normSq p : ℂ)`. Rewrite using `[← Complex.mul_conj, hw, mul_div_mul_right _ _ ((map_ne_zero _).2 hP)]`.

Rewrite using `[dz_cplx, e1, e2, hcp]`. Use `conv_rhs => rw [← Complex.re_add_im w]`. Establish `hN' : (Complex.normSq p : ℂ) ≠ 0` using `by exact_mod_cast hN`. Use `push_cast`. Clear the denominators using the available nonvanishing facts.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem dz_logAbsSq {m : ℕ} (P : MvPolynomial (Fin m) ℂ) (y : Fin m → ℂ) (hP : eval y P ≠ 0)
    (j : Fin m) :
    dz j (cplx (logAbsSq P)) y = fderiv ℂ (fun z => eval z P) y (Pi.single j 1) / eval y P := by
  have hg := analyticAt_eval_poly P y
  have hgd : HasFDerivAt (fun z => eval z P) (fderiv ℂ (fun z => eval z P) y) y :=
    hg.differentiableAt.hasFDerivAt
  have h1 := (hgd.restrictScalars ℝ).norm_sq
  have hne : ‖eval y P‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.2 hP)
  have h2 := h1.log hne
  have hf : fderiv ℝ (logAbsSq P) y = _ := h2.fderiv
  set c := fderiv ℂ (fun z => eval z P) y (Pi.single j 1) with hc
  set p := eval y P with hp
  set w := c * (starRingEnd ℂ) p with hw
  have hI : fderiv ℂ (fun z => eval z P) y (Complex.I • Pi.single j 1) = Complex.I * c := by
    rw [map_smul, smul_eq_mul]
  have hN : Complex.normSq p ≠ 0 := (Complex.normSq_pos.2 hP).ne'
  have e1 : fderiv ℝ (logAbsSq P) y (Pi.single j 1) = 2 * w.re / Complex.normSq p := by
    rw [hf]
    simp only [_root_.smul_apply, ContinuousLinearMap.comp_apply, innerSL_apply_apply,
      ContinuousLinearMap.coe_restrictScalars', Complex.inner, smul_eq_mul, nsmul_eq_mul,
      Complex.normSq_eq_norm_sq]
    rw [← hc, hw]
    ring
  have e2 : fderiv ℝ (logAbsSq P) y (Complex.I • Pi.single j 1) = -(2 * w.im / Complex.normSq p) := by
    rw [hf]
    simp only [_root_.smul_apply, ContinuousLinearMap.comp_apply, innerSL_apply_apply,
      ContinuousLinearMap.coe_restrictScalars', Complex.inner, smul_eq_mul, nsmul_eq_mul,
      Complex.normSq_eq_norm_sq]
    rw [hI, hw]
    simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
    ring
  have hcp : c / p = w / (Complex.normSq p : ℂ) := by
    rw [← Complex.mul_conj, hw, mul_div_mul_right _ _ ((map_ne_zero _).2 hP)]
  rw [dz_cplx, e1, e2, hcp]
  conv_rhs => rw [← Complex.re_add_im w]
  have hN' : (Complex.normSq p : ℂ) ≠ 0 := by exact_mod_cast hN
  push_cast
  field_simp
  ring

/- English proof (translation)
Establish `hg` using `analyticAt_eval_poly P y`. Establish `hv : ContDiffAt ℝ 2 (logAbsSq P) y`. Establish `h1 : ContDiffAt ℝ 2 (fun z => ‖eval z P‖ ^ 2) y` using `((hg.contDiffAt (n := 2)).restrict_scalars ℝ).norm_sq ℝ`. Conclude with `h1.log (by positivity)`. Establish `hv0 : hessC (logAbsSq P) y = 0`.

Establish `h : logAbsSq P = fun z => (2 : ℝ) * Real.log ‖eval z P‖`. Use function extensionality and compare the values at `z`. Rewrite using `[logAbsSq, Real.log_pow]`. Evaluate the numerical expressions. Rewrite using `[h, ReciprocityTheory.AnForm.M.hessC_const_mul', hessC_log_norm _ y hg hP, smul_zero]`.

Rewrite using `[MaDensLeibniz.hessC_sq_half _ y hv, hv0, smul_zero, zero_add, gradMat_eq_vecMulVec]`. Establish `ha : (fun j => dz j (cplx (logAbsSq P)) y) = fun j => fderiv ℂ (fun z => eval z P) y (Pi.single j 1) / eval y P`. Use function extensionality and compare the values at `fun j => dz_logAbsSq P y hP j`. Rewrite using `[ha]`.
-/
theorem hessC_logAbsSq_sq_half {m : ℕ} (P : MvPolynomial (Fin m) ℂ) (y : Fin m → ℂ) (hP : eval y P ≠ 0) :
    hessC (fun z => logAbsSq P z ^ 2 / 2) y =
      vecMulVec (fun j => fderiv ℂ (fun z => eval z P) y (Pi.single j 1) / eval y P)
        (star fun j => fderiv ℂ (fun z => eval z P) y (Pi.single j 1) / eval y P) := by
  have hg := analyticAt_eval_poly P y
  have hv : ContDiffAt ℝ 2 (logAbsSq P) y := by
    have h1 : ContDiffAt ℝ 2 (fun z => ‖eval z P‖ ^ 2) y :=
      ((hg.contDiffAt (n := 2)).restrict_scalars ℝ).norm_sq ℝ
    exact h1.log (by positivity)
  have hv0 : hessC (logAbsSq P) y = 0 := by
    have h : logAbsSq P = fun z => (2 : ℝ) * Real.log ‖eval z P‖ := by
      funext z
      rw [logAbsSq, Real.log_pow]
      norm_num
    rw [h, ReciprocityTheory.AnForm.M.hessC_const_mul', hessC_log_norm _ y hg hP, smul_zero]
  rw [MaDensLeibniz.hessC_sq_half _ y hv, hv0, smul_zero, zero_add, gradMat_eq_vecMulVec]
  have ha : (fun j => dz j (cplx (logAbsSq P)) y) =
      fun j => fderiv ℂ (fun z => eval z P) y (Pi.single j 1) / eval y P :=
    funext fun j => dz_logAbsSq P y hP j
  rw [ha]

/- English proof (translation)
Establish `e` using `((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin m => ℂ) a).hasFDerivAt.comp y hF.hasFDerivAt).fderiv`. Establish `e' : (fun x => F x a) = (ContinuousLinearMap.proj (R` using `ℂ) (φ := fun _ : Fin m => ℂ) a) ∘ F := rfl`. Rewrite using `[e', e]`. Both sides reduce to the same expression.
-/
theorem fderiv_apply_coord {D m : ℕ} (F : (Fin D → ℂ) → Fin m → ℂ) (y h : Fin D → ℂ)
    (hF : DifferentiableAt ℂ F y) (a : Fin m) :
    fderiv ℂ F y h a = fderiv ℂ (fun x => F x a) y h := by
  have e := ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin m => ℂ) a).hasFDerivAt.comp y
    hF.hasFDerivAt).fderiv
  have e' : (fun x => F x a) = (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin m => ℂ) a) ∘ F := rfl
  rw [e', e]
  rfl

/- English proof (translation)
Establish `hg` using `(analyticAt_eval_poly P y).differentiableAt`. Establish `hF : DifferentiableAt ℂ (deepMap P s I) y`. Use `differentiableAt_pi.2 fun k => ?_` and prove the remaining obligations. Use `Fin.cases ?_ (fun i => ?_) k` and prove the remaining obligations. Simplify `hg` using `[deepMap]`.

Simplify `differentiableAt_pi.1 hs (I i)` using `[deepMap]`. Use `set J := jacC (deepMap P s I) y with hJdef`. Establish `hJ : (Matrix.of (Fin.cons (fun j => fderiv ℂ (fun z => eval z P) y (Pi.single j 1) / eval y P) (fun i j => jacC s y (I i) j) : Fin (d + 1) → Fin (d + 1) → ℂ)) = J.updateRow 0 ((eval y P)⁻¹ • J 0)`. Use extensionality with `k j`. Use `Fin.cases ?_ (fun i => ?_) k` and prove the remaining obligations.

Establish `h0 : (fun x => deepMap P s I x 0) = fun z => eval z P`. Use function extensionality and compare the values at `x`. Simplify using `[deepMap]`. Simplify using `only [Matrix.of_apply, Fin.cons_zero, updateRow_self, Pi.smul_apply, smul_eq_mul, hJdef, jacC, fderiv_apply_coord _ _ _ hF, h0]`. Rewrite using `[div_eq_inv_mul]`.

Establish `hi : (fun x => deepMap P s I x i.succ) = fun x => s x (I i)`. Use function extensionality and compare the values at `x`. Simplify using `[deepMap]`. Simplify using `only [Matrix.of_apply, Fin.cons_succ, updateRow_ne (Fin.succ_ne_zero i), hJdef, jacC, fderiv_apply_coord _ _ _ hF, hi, fderiv_apply_coord _ _ _ hs]`. Rewrite using `[hJ, det_updateRow_smul, updateRow_eq_self, hJdef, det_jacC]`.

Both sides reduce to the same expression.
-/
theorem det_rows_eq_deepJacDet {n d : ℕ} (P : MvPolynomial (Fin (d + 1)) ℂ)
    (s : (Fin (d + 1) → ℂ) → Fin n → ℂ) (y : Fin (d + 1) → ℂ) (hs : DifferentiableAt ℂ s y)
    (I : Fin d → Fin n) :
    (Matrix.of (Fin.cons (fun j => fderiv ℂ (fun z => eval z P) y (Pi.single j 1) / eval y P)
        (fun i j => jacC s y (I i) j) : Fin (d + 1) → Fin (d + 1) → ℂ)).det =
      (eval y P)⁻¹ * deepJacDet P s I y := by
  have hg := (analyticAt_eval_poly P y).differentiableAt
  have hF : DifferentiableAt ℂ (deepMap P s I) y := by
    refine differentiableAt_pi.2 fun k => ?_
    refine Fin.cases ?_ (fun i => ?_) k
    · simpa [deepMap] using hg
    · simpa [deepMap] using differentiableAt_pi.1 hs (I i)
  set J := jacC (deepMap P s I) y with hJdef
  have hJ : (Matrix.of (Fin.cons (fun j => fderiv ℂ (fun z => eval z P) y (Pi.single j 1) / eval y P)
        (fun i j => jacC s y (I i) j) : Fin (d + 1) → Fin (d + 1) → ℂ)) =
      J.updateRow 0 ((eval y P)⁻¹ • J 0) := by
    ext k j
    refine Fin.cases ?_ (fun i => ?_) k
    · have h0 : (fun x => deepMap P s I x 0) = fun z => eval z P := by
        funext x
        simp [deepMap]
      simp only [Matrix.of_apply, Fin.cons_zero, updateRow_self, Pi.smul_apply, smul_eq_mul, hJdef,
        jacC, fderiv_apply_coord _ _ _ hF, h0]
      rw [div_eq_inv_mul]
    · have hi : (fun x => deepMap P s I x i.succ) = fun x => s x (I i) := by
        funext x
        simp [deepMap]
      simp only [Matrix.of_apply, Fin.cons_succ, updateRow_ne (Fin.succ_ne_zero i), hJdef, jacC,
        fderiv_apply_coord _ _ _ hF, hi, fderiv_apply_coord _ _ _ hs]
  rw [hJ, det_updateRow_smul, updateRow_eq_self, hJdef, det_jacC]
  rfl

/- English proof (translation)
Introduce `n d A P U s y hU hy hsd hAs hP`. Establish `hsa : AnalyticAt ℂ s y` using `analyticAt_pi_iff.2 fun j => ReciprocityTheory.AnForm.Osgood.osgood (d + 1) U (fun y => s y j) hU (differentiableOn_pi.1 hsd j) y hy`. Use `set a : Fin (d + 1) → ℂ := fun j => fderiv ℂ (fun z => eval z P) y (Pi.single j 1) / eval y P with ha`. Use `set b : Fin n → Fin (d + 1) → ℂ := fun m j => jacC s y m j with hb`. Establish `h0 : hessC ((fun x => logAbsSq P (A *ᵥ x) ^ 2 / 2) ∘ s) y = vecMulVec a (star a)`.

Establish `hev : ((fun x => logAbsSq P (A *ᵥ x) ^ 2 / 2) ∘ s) =ᶠ[𝓝 y] fun z => logAbsSq P z ^ 2 / 2` using `by filter_upwards [hU.mem_nhds hy] with z hz`. Simplify using `only [Function.comp_apply, hAs z hz]`. Rewrite using `[hessC_congr' hev, hessC_logAbsSq_sq_half P y hP]`. Establish `h1 : hessC (euclPot ∘ s) y = ∑ m, vecMulVec (b m) (star (b m))` using `hessC_euclPot_comp s y hsa`. Establish `hH : (fun k => hessC (vecCons (fun x => logAbsSq P (A *ᵥ x) ^ 2 / 2) (fun _ => euclPot) k ∘ s) y) = (Fin.cons (vecMulVec a (star a)) (fun _ => ∑ m, vecMulVec (b m) (star (b m))) : Fin (d + 1) → Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ)`.

Use function extensionality and compare the values at `k`. Use `Fin.cases ?_ (fun i => ?_) k` and prove the remaining obligations. Simplify using `using h0`. Simplify using `using h1`. Establish `hI : ∀ I : Fin d → Fin n, (Fin.cons (vecMulVec a (star a)) (fun i => vecMulVec (b (I i)) (star (b (I i)))) : Fin (d + 1) → Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) = fun k => vecMulVec ((Fin.cons a (fun i => b (I i)) : Fin (d + 1) → Fin (d + 1) → ℂ) k) (star ((Fin.cons a (fun i => b …`.

Introduce `I`. Use function extensionality and compare the values at `k`. Apply the tactic sequence `refine Fin.cases ?_ (fun i => ?_) k <;> simp`. Establish `hdet : ∀ I : Fin d → Fin n, (Matrix.of (Fin.cons a (fun i => b (I i)) : Fin (d + 1) → Fin (d + 1) → ℂ)).det = (eval y P)⁻¹ * deepJacDet P s I y` using `fun I => det_rows_eq_deepJacDet P s y (hsd.differentiableAt (hU.mem_nhds hy)) I`. Unfold `ReciprocityTheory.AnForm.maDens`.

Rewrite using `[hH, mdisc_cons_sum]`. Repeatedly rewrite using `[hI, mdisc_vecMulVec, hdet]`. Rewrite using `[Complex.re_sum, Finset.mul_sum, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun I _ => ?_` and prove the remaining obligations. Establish `hf : ((d + 1).factorial : ℝ) ≠ 0` using `by exact_mod_cast (d + 1).factorial_ne_zero`.

Establish `hre : ((1 / ((d + 1).factorial : ℂ)) * (Complex.normSq ((eval y P)⁻¹ * deepJacDet P s I y) : ℂ)).re = Complex.normSq ((eval y P)⁻¹ * deepJacDet P s I y) / ((d + 1).factorial : ℝ)`. Rewrite using `[show (1 / ((d + 1).factorial : ℂ)) = (((1 / ((d + 1).factorial : ℝ)) : ℝ) : ℂ) by push_cast; rfl, ← Complex.ofReal_mul, Complex.ofReal_re]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hre, map_mul, map_inv₀, Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]`. Establish `hp : ‖eval y P‖ ^ 2 ≠ 0` using `pow_ne_zero 2 (norm_ne_zero_iff.2 hP)`.

Clear the denominators using the available nonvanishing facts.
-/
theorem proof : TubeDeepRankOne.Statement := by
  intro n d A P U s y hU hy hsd hAs hP
  have hsa : AnalyticAt ℂ s y := analyticAt_pi_iff.2 fun j =>
    ReciprocityTheory.AnForm.Osgood.osgood (d + 1) U (fun y => s y j) hU (differentiableOn_pi.1 hsd j) y hy
  set a : Fin (d + 1) → ℂ := fun j => fderiv ℂ (fun z => eval z P) y (Pi.single j 1) / eval y P with ha
  set b : Fin n → Fin (d + 1) → ℂ := fun m j => jacC s y m j with hb
  have h0 : hessC ((fun x => logAbsSq P (A *ᵥ x) ^ 2 / 2) ∘ s) y = vecMulVec a (star a) := by
    have hev : ((fun x => logAbsSq P (A *ᵥ x) ^ 2 / 2) ∘ s) =ᶠ[𝓝 y] fun z => logAbsSq P z ^ 2 / 2 := by
      filter_upwards [hU.mem_nhds hy] with z hz
      simp only [Function.comp_apply, hAs z hz]
    rw [hessC_congr' hev, hessC_logAbsSq_sq_half P y hP]
  have h1 : hessC (euclPot ∘ s) y = ∑ m, vecMulVec (b m) (star (b m)) := hessC_euclPot_comp s y hsa
  have hH : (fun k => hessC (vecCons (fun x => logAbsSq P (A *ᵥ x) ^ 2 / 2) (fun _ => euclPot) k ∘ s) y) =
      (Fin.cons (vecMulVec a (star a)) (fun _ => ∑ m, vecMulVec (b m) (star (b m))) :
        Fin (d + 1) → Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) := by
    funext k
    refine Fin.cases ?_ (fun i => ?_) k
    · simpa using h0
    · simpa using h1
  have hI : ∀ I : Fin d → Fin n,
      (Fin.cons (vecMulVec a (star a)) (fun i => vecMulVec (b (I i)) (star (b (I i)))) :
        Fin (d + 1) → Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) =
      fun k => vecMulVec ((Fin.cons a (fun i => b (I i)) : Fin (d + 1) → Fin (d + 1) → ℂ) k)
        (star ((Fin.cons a (fun i => b (I i)) : Fin (d + 1) → Fin (d + 1) → ℂ) k)) := by
    intro I
    funext k
    refine Fin.cases ?_ (fun i => ?_) k <;> simp
  have hdet : ∀ I : Fin d → Fin n,
      (Matrix.of (Fin.cons a (fun i => b (I i)) : Fin (d + 1) → Fin (d + 1) → ℂ)).det =
        (eval y P)⁻¹ * deepJacDet P s I y := fun I =>
    det_rows_eq_deepJacDet P s y (hsd.differentiableAt (hU.mem_nhds hy)) I
  unfold ReciprocityTheory.AnForm.maDens
  rw [hH, mdisc_cons_sum]
  simp_rw [hI, mdisc_vecMulVec, hdet]
  rw [Complex.re_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun I _ => ?_
  have hf : ((d + 1).factorial : ℝ) ≠ 0 := by exact_mod_cast (d + 1).factorial_ne_zero
  have hre : ((1 / ((d + 1).factorial : ℂ)) *
      (Complex.normSq ((eval y P)⁻¹ * deepJacDet P s I y) : ℂ)).re =
      Complex.normSq ((eval y P)⁻¹ * deepJacDet P s I y) / ((d + 1).factorial : ℝ) := by
    rw [show (1 / ((d + 1).factorial : ℂ)) = (((1 / ((d + 1).factorial : ℝ)) : ℝ) : ℂ) by push_cast; rfl,
      ← Complex.ofReal_mul, Complex.ofReal_re]
    ring
  rw [hre, map_mul, map_inv₀, Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
  have hp : ‖eval y P‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.2 hP)
  field_simp

end TubeDeepRankOne

end

end GroundTheory.Heights₂.Heights
