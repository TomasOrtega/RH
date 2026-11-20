import Mathlib
import Formalism.FormalDegreeBessel.StatementWR

open scoped ContDiff
open MeasureTheory

noncomputable section

namespace Formalism.QuantumDeterminants

/- English proof (translation)
Establish `h : OmX m = ⋂ l, {x : Fin m → ℂ | x l ≠ 0}`. Use extensionality with `x`. Simplify using `[OmX]`. Rewrite using `[h]`. Conclude with `isOpen_iInter_of_finite fun l => isOpen_ne_fun (continuous_apply l) continuous_const`.
-/
theorem isOpen_OmX (m : ℕ) : IsOpen (OmX m) := by
  have h : OmX m = ⋂ l, {x : Fin m → ℂ | x l ≠ 0} := by
    ext x
    simp [OmX]
  rw [h]
  exact isOpen_iInter_of_finite fun l => isOpen_ne_fun (continuous_apply l) continuous_const

variable {m : ℕ}

/- English proof (translation)
Unfold `wirt`. Rewrite using `[show (fun y => a y * b y) = a * b from rfl, fderiv_mul ha hb]`. Simplify using `only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem wirt_mul_fun (l : Fin m) {a b : (Fin m → ℂ) → ℂ} {x : Fin m → ℂ}
    (ha : DifferentiableAt ℝ a x) (hb : DifferentiableAt ℝ b x) :
    wirt l (fun y => a y * b y) x = wirt l a x * b x + a x * wirt l b x := by
  unfold wirt
  rw [show (fun y => a y * b y) = a * b from rfl, fderiv_mul ha hb]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

/- English proof (translation)
Unfold `wirt wirtBar`. Rewrite using `[fderiv_star]`. Simplify using `only [ContinuousLinearMap.coe_comp', Function.comp_apply, ContinuousLinearMap.coe_coe, ContinuousLinearEquiv.coe_coe, starL'_apply, smul_eq_mul, Complex.star_def, map_add, map_mul, map_div₀, map_one, map_ofNat, Complex.conj_I]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem wirt_star_fun (l : Fin m) (g : (Fin m → ℂ) → ℂ) (x : Fin m → ℂ) :
    wirt l (fun y => star (g y)) x = star (wirtBar l g x) := by
  unfold wirt wirtBar
  rw [fderiv_star]
  simp only [ContinuousLinearMap.coe_comp', Function.comp_apply, ContinuousLinearMap.coe_coe,
    ContinuousLinearEquiv.coe_coe, starL'_apply, smul_eq_mul, Complex.star_def, map_add, map_mul, map_div₀, map_one, map_ofNat,
    Complex.conj_I]
  ring

def uW (l : Fin m) (x : Fin m → ℂ) : ℂ := x l * (((∏ k, Complex.normSq (x k))⁻¹ : ℝ) : ℂ)

/- English proof (translation)
Establish `hl : (x + t • (Pi.single l a : Fin m → ℂ)) l = x l + t * a`. Simplify using `[Complex.real_smul]`. Establish `hk : ∀ k ∈ Finset.univ.erase l, (x + t • (Pi.single l a : Fin m → ℂ)) k = x k`. Introduce `k hk`. Simplify using `[Finset.ne_of_mem_erase hk]`.

Establish `hprod : ∏ k, Complex.normSq ((x + t • (Pi.single l a : Fin m → ℂ)) k) = Complex.normSq (x l + t * a) * ∏ k ∈ Finset.univ.erase l, Complex.normSq (x k)`. Rewrite using `[← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ l), hl]`. Use `congr 1`. Conclude with `Finset.prod_congr rfl fun k hk' => by rw [hk k hk']`. Establish `key : (star (x l) + (t : ℂ) * star a)⁻¹ = (x l + t * a) * (((Complex.normSq (x l + t * a))⁻¹ : ℝ) : ℂ)`.

Establish `e : star (x l) + (t : ℂ) * star a = (starRingEnd ℂ) (x l + t * a)`. Simplify using `[Complex.star_def, map_add, map_mul, Complex.conj_ofReal]`. Rewrite using `[e, Complex.inv_def, Complex.conj_conj, Complex.normSq_conj]`. Unfold `uW`. Rewrite using `[hprod, hl, key, mul_inv, Complex.ofReal_mul]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem uW_line (l : Fin m) (x : Fin m → ℂ) (a : ℂ) (t : ℝ) :
    uW l (x + t • (Pi.single l a : Fin m → ℂ)) = (star (x l) + (t : ℂ) * star a)⁻¹ *
      (((∏ k ∈ Finset.univ.erase l, Complex.normSq (x k))⁻¹ : ℝ) : ℂ) := by
  have hl : (x + t • (Pi.single l a : Fin m → ℂ)) l = x l + t * a := by
    simp [Complex.real_smul]
  have hk : ∀ k ∈ Finset.univ.erase l, (x + t • (Pi.single l a : Fin m → ℂ)) k = x k := by
    intro k hk
    simp [Finset.ne_of_mem_erase hk]
  have hprod : ∏ k, Complex.normSq ((x + t • (Pi.single l a : Fin m → ℂ)) k) =
      Complex.normSq (x l + t * a) * ∏ k ∈ Finset.univ.erase l, Complex.normSq (x k) := by
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ l), hl]
    congr 1
    exact Finset.prod_congr rfl fun k hk' => by rw [hk k hk']
  have key : (star (x l) + (t : ℂ) * star a)⁻¹ =
      (x l + t * a) * (((Complex.normSq (x l + t * a))⁻¹ : ℝ) : ℂ) := by
    have e : star (x l) + (t : ℂ) * star a = (starRingEnd ℂ) (x l + t * a) := by
      simp [Complex.star_def, map_add, map_mul, Complex.conj_ofReal]
    rw [e, Complex.inv_def, Complex.conj_conj, Complex.normSq_conj]
  unfold uW
  rw [hprod, hl, key, mul_inv, Complex.ofReal_mul]
  ring

/- English proof (translation)
Use `set K : ℂ := (((∏ k ∈ Finset.univ.erase l, Complex.normSq (x k))⁻¹ : ℝ) : ℂ) with hK`. Establish `hc : star (x l) ≠ 0` using `star_ne_zero.mpr hx`. Establish `h1 : HasDerivAt (fun t : ℝ => star (x l) + (t : ℂ) * star a) (star a) 0`. Establish `h` using `((hasDerivAt_id (0 : ℝ)).ofReal_comp).mul_const (star a)`. Simplify using `using h.const_add (star (x l))`.

Establish `h0 : star (x l) + ((0 : ℝ) : ℂ) * star a = star (x l)` using `by simp`. Establish `hc' : star (x l) + ((0 : ℝ) : ℂ) * star a ≠ 0`. Rewrite using `[h0]`. Conclude with `hc`. Establish `h2` using `((hasDerivAt_inv hc').comp (0 : ℝ) h1).mul_const K`.

Unfold `HasLineDerivAt`. Establish `hf : (fun t : ℝ => uW l (x + t • (Pi.single l a : Fin m → ℂ))) = fun t : ℝ => (star (x l) + (t : ℂ) * star a)⁻¹ * K`. Use function extensionality and compare the values at `t`. Rewrite using `[uW_line]`. Rewrite using `[hf]`.

Conclude with `h2.congr_deriv (by rw [h0]; ring)`.
-/
theorem uW_hasLineDerivAt (l : Fin m) (x : Fin m → ℂ) (hx : x l ≠ 0) (a : ℂ) :
    HasLineDerivAt ℝ (uW l) (-(star a) / (star (x l)) ^ 2 *
      (((∏ k ∈ Finset.univ.erase l, Complex.normSq (x k))⁻¹ : ℝ) : ℂ)) x (Pi.single l a) := by
  set K : ℂ := (((∏ k ∈ Finset.univ.erase l, Complex.normSq (x k))⁻¹ : ℝ) : ℂ) with hK
  have hc : star (x l) ≠ 0 := star_ne_zero.mpr hx
  have h1 : HasDerivAt (fun t : ℝ => star (x l) + (t : ℂ) * star a) (star a) 0 := by
    have h := ((hasDerivAt_id (0 : ℝ)).ofReal_comp).mul_const (star a)
    simpa using h.const_add (star (x l))
  have h0 : star (x l) + ((0 : ℝ) : ℂ) * star a = star (x l) := by simp
  have hc' : star (x l) + ((0 : ℝ) : ℂ) * star a ≠ 0 := by
    rw [h0]
    exact hc
  have h2 := ((hasDerivAt_inv hc').comp (0 : ℝ) h1).mul_const K
  unfold HasLineDerivAt
  have hf : (fun t : ℝ => uW l (x + t • (Pi.single l a : Fin m → ℂ))) =
      fun t : ℝ => (star (x l) + (t : ℂ) * star a)⁻¹ * K := by
    funext t
    rw [uW_line]
  rw [hf]
  exact h2.congr_deriv (by rw [h0]; ring)

/- English proof (translation)
Establish `h1 : ContDiff ℝ ∞ (fun x : Fin m → ℂ => x l)` using `contDiff_apply ℝ ℂ l`. Establish `h2 : ContDiff ℝ ∞ (fun x : Fin m → ℂ => ∏ k, Complex.normSq (x k))`. Apply `contDiff_prod` to reduce the goal to its premises. Introduce `k _`. Establish `e : (fun x : Fin m → ℂ => Complex.normSq (x k)) = fun x => ‖x k‖ ^ 2`.

Use function extensionality and compare the values at `x`. Rewrite using `[Complex.normSq_eq_norm_sq]`. Rewrite using `[e]`. Conclude with `(contDiff_norm_sq ℝ).comp (contDiff_apply ℝ ℂ k)`. Establish `h3 : ContDiffOn ℝ ∞ (fun x : Fin m → ℂ => (∏ k, Complex.normSq (x k))⁻¹) (OmX m)`.

Apply `h2.contDiffOn.inv` to reduce the goal to its premises. Introduce `x hx`. Conclude with `Finset.prod_ne_zero_iff.mpr fun k _ => by simpa [Complex.normSq_eq_zero] using hx k`. Establish `h4` using `Complex.ofRealCLM.contDiff.comp_contDiffOn h3`. Establish `e : uW l = fun x => x l * (Complex.ofRealCLM ∘ fun x : Fin m → ℂ => (∏ k, Complex.normSq (x k))⁻¹) x`.

Use function extensionality and compare the values at `x`. Simplify using `[uW]`. Rewrite using `[e]`. Conclude with `h1.contDiffOn.mul h4`.
-/
theorem uW_contDiffOn (l : Fin m) : ContDiffOn ℝ ∞ (uW l) (OmX m) := by
  have h1 : ContDiff ℝ ∞ (fun x : Fin m → ℂ => x l) := contDiff_apply ℝ ℂ l
  have h2 : ContDiff ℝ ∞ (fun x : Fin m → ℂ => ∏ k, Complex.normSq (x k)) := by
    apply contDiff_prod
    intro k _
    have e : (fun x : Fin m → ℂ => Complex.normSq (x k)) = fun x => ‖x k‖ ^ 2 := by
      funext x
      rw [Complex.normSq_eq_norm_sq]
    rw [e]
    exact (contDiff_norm_sq ℝ).comp (contDiff_apply ℝ ℂ k)
  have h3 : ContDiffOn ℝ ∞ (fun x : Fin m → ℂ => (∏ k, Complex.normSq (x k))⁻¹) (OmX m) := by
    apply h2.contDiffOn.inv
    intro x hx
    exact Finset.prod_ne_zero_iff.mpr fun k _ => by simpa [Complex.normSq_eq_zero] using hx k
  have h4 := Complex.ofRealCLM.contDiff.comp_contDiffOn h3
  have e : uW l = fun x => x l * (Complex.ofRealCLM ∘ fun x : Fin m → ℂ =>
      (∏ k, Complex.normSq (x k))⁻¹) x := by
    funext x
    simp [uW]
  rw [e]
  exact h1.contDiffOn.mul h4

/- English proof (translation)
Establish `hd : DifferentiableAt ℝ (uW l) x` using `((uW_contDiffOn l).differentiableOn (by simp)).differentiableAt ((isOpen_OmX m).mem_nhds hx)`. Establish `hxl : x l ≠ 0` using `hx l`. Use `set K : ℂ := (((∏ k ∈ Finset.univ.erase l, Complex.normSq (x k))⁻¹ : ℝ) : ℂ) with hK`. Unfold `wirt`. Rewrite using `[← hd.lineDeriv_eq_fderiv, ← hd.lineDeriv_eq_fderiv, (uW_hasLineDerivAt l x hxl 1).lineDeriv, (uW_hasLineDerivAt l x hxl Complex.I).lineDeriv]`.

Simplify using `only [star_one, Complex.star_def, Complex.conj_I, smul_eq_mul]`. Take the linear combination `(-(1 / 2) * K / ((starRingEnd ℂ) (x l)) ^ 2) * Complex.I_mul_I`.
-/
theorem wirt_uW (l : Fin m) (x : Fin m → ℂ) (hx : x ∈ OmX m) : wirt l (uW l) x = 0 := by
  have hd : DifferentiableAt ℝ (uW l) x :=
    ((uW_contDiffOn l).differentiableOn (by simp)).differentiableAt ((isOpen_OmX m).mem_nhds hx)
  have hxl : x l ≠ 0 := hx l
  set K : ℂ := (((∏ k ∈ Finset.univ.erase l, Complex.normSq (x k))⁻¹ : ℝ) : ℂ) with hK
  unfold wirt
  rw [← hd.lineDeriv_eq_fderiv, ← hd.lineDeriv_eq_fderiv, (uW_hasLineDerivAt l x hxl 1).lineDeriv,
    (uW_hasLineDerivAt l x hxl Complex.I).lineDeriv]
  simp only [star_one, Complex.star_def, Complex.conj_I, smul_eq_mul]
  linear_combination (-(1 / 2) * K / ((starRingEnd ℂ) (x l)) ^ 2) * Complex.I_mul_I

/- English proof (translation)
Unfold `tsupport`. Use `congr 1`. Use extensionality with `x`. Simplify using `[Function.mem_support, star_eq_zero]`.
-/
theorem tsupport_star_fun (g : (Fin m → ℂ) → ℂ) : tsupport (fun y => star (g y)) = tsupport g := by
  unfold tsupport
  congr 1
  ext x
  simp [Function.mem_support, star_eq_zero]

/- English proof (translation)
Establish `hc' : Continuous φ` using `hc.continuous_of_tsupport_subset (isOpen_OmX m) (hs.trans hΩ)`. Establish `hK' : HasCompactSupport φ` using `IsCompact.of_isClosed_subset hK (isClosed_tsupport _) hs`. Conclude with `hc'.integrable_of_hasCompactSupport hK'`.
-/
theorem integrable_of_on {φ h : (Fin m → ℂ) → ℂ} (hc : ContinuousOn φ (OmX m))
    (hs : tsupport φ ⊆ tsupport h) (hK : HasCompactSupport h) (hΩ : tsupport h ⊆ OmX m) :
    Integrable φ := by
  have hc' : Continuous φ := hc.continuous_of_tsupport_subset (isOpen_OmX m) (hs.trans hΩ)
  have hK' : HasCompactSupport φ := IsCompact.of_isClosed_subset hK (isClosed_tsupport _) hs
  exact hc'.integrable_of_hasCompactSupport hK'

/- English proof (translation)
Introduce `m l f g hf hg hfc hgc hfΩ hgΩ`. Establish `hΩo` using `isOpen_OmX m`. Take `⟨hf1, hf2⟩` from `hf`. Take `⟨hg1, hg2⟩` from `hg`. Use `set h : (Fin m → ℂ) → ℂ := fun y => star (g y) * uW l y with hh`.

Establish `hsg : ContDiffOn ℝ ∞ (fun y => star (g y)) (OmX m)`. Establish `h1` using `(starL' ℝ : ℂ ≃L[ℝ] ℂ).contDiff.comp_contDiffOn hg1`. Use `h1 using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `y`. Simplify using the standard rewrite rules.

Establish `hhc : ContDiffOn ℝ ∞ h (OmX m)` using `hsg.mul (uW_contDiffOn l)`. Establish `hfd : ∀ x ∈ OmX m, DifferentiableAt ℝ f x` using `fun x hx => (hf1.differentiableOn (by simp)).differentiableAt (hΩo.mem_nhds hx)`. Establish `hgd : ∀ x ∈ OmX m, DifferentiableAt ℝ g x` using `fun x hx => (hg1.differentiableOn (by simp)).differentiableAt (hΩo.mem_nhds hx)`. Establish `hud : ∀ x ∈ OmX m, DifferentiableAt ℝ (uW l) x` using `fun x hx => ((uW_contDiffOn l).differentiableOn (by simp)).differentiableAt (hΩo.mem_nhds hx)`. Establish `hhd : ∀ x ∈ OmX m, DifferentiableAt ℝ h x` using `fun x hx => (hhc.differentiableOn (by simp)).differentiableAt (hΩo.mem_nhds hx)`.

Establish `hhg : tsupport h ⊆ tsupport g`. Establish `h1 : tsupport h ⊆ tsupport (fun y => star (g y))` using `tsupport_mul_subset_left`. Rewrite `h1` using `[tsupport_star_fun]`. Then use the resulting hypothesis. Establish `hhΩ : tsupport h ⊆ OmX m` using `hhg.trans hgΩ`. Establish `hhK : HasCompactSupport h` using `IsCompact.of_isClosed_subset hgc (isClosed_tsupport _) hhg`.

Establish `hfz : ∀ x, x ∉ OmX m → fderiv ℝ f x = 0`. Introduce `x hx`. Establish `hx' : x ∉ tsupport f` using `fun h' => hx (hfΩ h')`. Assume the negation of the conclusion as `hne`. Conclude with `hx' (support_fderiv_subset ℝ hne)`.

Establish `hL : ∀ x, pOp l f x * star (g x) * (((∏ k, Complex.normSq (x k))⁻¹ : ℝ) : ℂ) = wirt l f x * h x`. Introduce `x`. Distinguish the cases in `hx : x ∈ OmX m`. Simplify using `only [pOp, if_pos hx, smul_eq_mul, hh, uW]`. Expand and normalize the polynomial expressions, which then agree.

Simplify using `[pOp, hx, wirt, hfz x hx]`. Establish `hR : ∀ x, f x * star (pbOp l g x) * (((∏ k, Complex.normSq (x k))⁻¹ : ℝ) : ℂ) = f x * wirt l h x`. Introduce `x`. Distinguish the cases in `hx : x ∈ OmX m`. Establish `hsd : DifferentiableAt ℝ (fun y => star (g y)) x` using `(hgd x hx).star`.

Rewrite using `[hh, wirt_mul_fun l hsd (hud x hx), wirt_uW l x hx, wirt_star_fun]`. Simplify using `only [pbOp, if_pos hx, smul_eq_mul, star_mul', star_star, uW]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `[hf2 x hx]`. Establish `eL : (∫ x, pOp l f x * star (g x) * (((∏ k, Complex.normSq (x k))⁻¹ : ℝ) : ℂ)) = ∫ x, wirt l f x * h x`.

Use `congr 1`. Use function extensionality and compare the values at `x`. Conclude with `hL x`. Establish `eR : (∫ x, f x * star (pbOp l g x) * (((∏ k, Complex.normSq (x k))⁻¹ : ℝ) : ℂ)) = ∫ x, f x * wirt l h x`. Use `congr 1`.

Use function extensionality and compare the values at `x`. Conclude with `hR x`. Rewrite using `[eL, eR]`. Establish `I1 : ∀ v, Integrable (fun x => fderiv ℝ f x v * h x)`. Introduce `v`.

Use `integrable_of_on ?_ tsupport_mul_subset_right hhK hhΩ` and prove the remaining obligations. Conclude with `((hf1.continuousOn_fderiv_of_isOpen hΩo (by simp)).clm_apply continuousOn_const).mul hhc.continuousOn`. Establish `I2 : ∀ v, Integrable (fun x => f x * fderiv ℝ h x v)`. Introduce `v`. Use `integrable_of_on ?_ tsupport_mul_subset_left hfc hfΩ` and prove the remaining obligations.

Conclude with `hf1.continuousOn.mul ((hhc.continuousOn_fderiv_of_isOpen hΩo (by simp)).clm_apply continuousOn_const)`. Establish `I3 : Integrable (fun x => f x * h x)` using `integrable_of_on (hf1.continuousOn.mul hhc.continuousOn) tsupport_mul_subset_left hfc hfΩ`. Establish `ibp : ∀ v, ∫ x, f x * fderiv ℝ h x v = -∫ x, fderiv ℝ f x v * h x`. Introduce `v`. Conclude with `integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (I1 v) (I2 v) I3 (fun x hx => hfd x (hhΩ hx)) (fun x hx => hhd x (hfΩ hx))`.

Establish `hw : ∀ φ : (Fin m → ℂ) → ℂ, ∀ x, wirt l φ x = (1 / 2 : ℂ) * (fderiv ℝ φ x (Pi.single l 1) - Complex.I * fderiv ℝ φ x (Pi.single l Complex.I))`. Introduce `φ x`. Simplify using `[wirt, smul_eq_mul]`. Repeatedly rewrite using `[hw]`. Establish `lhs : (∫ x, (1 / 2 : ℂ) * (fderiv ℝ f x (Pi.single l 1) - Complex.I * fderiv ℝ f x (Pi.single l Complex.I)) * h x) = (1 / 2 : ℂ) * (∫ x, fderiv ℝ f x (Pi.single l 1) * h x) - ((1 / 2 : ℂ) * Complex.I) * ∫ x, fderiv ℝ f x (Pi.single l Complex.I) * h x`.

Rewrite using `[← integral_const_mul, ← integral_const_mul, ← integral_sub ((I1 _).const_mul _) ((I1 _).const_mul _)]`. Use `congr 1`. Use function extensionality and compare the values at `x`. Expand and normalize the polynomial expressions, which then agree. Establish `rhs : (∫ x, f x * ((1 / 2 : ℂ) * (fderiv ℝ h x (Pi.single l 1) - Complex.I * fderiv ℝ h x (Pi.single l Complex.I)))) = (1 / 2 : ℂ) * (∫ x, f x * fderiv ℝ h x (Pi.single l 1)) - ((1 / 2 : ℂ) * Complex.I) * ∫ x, f x * fderiv ℝ h x (Pi.single l Complex.I)`.

Rewrite using `[← integral_const_mul, ← integral_const_mul, ← integral_sub ((I2 _).const_mul _) ((I2 _).const_mul _)]`. Use `congr 1`. Use function extensionality and compare the values at `x`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[lhs, rhs, ibp, ibp]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem adjoint_functional_holds : AdjFun := by
  intro m l f g hf hg hfc hgc hfΩ hgΩ
  have hΩo := isOpen_OmX m
  obtain ⟨hf1, hf2⟩ := hf
  obtain ⟨hg1, hg2⟩ := hg
  set h : (Fin m → ℂ) → ℂ := fun y => star (g y) * uW l y with hh
  have hsg : ContDiffOn ℝ ∞ (fun y => star (g y)) (OmX m) := by
    have h1 := (starL' ℝ : ℂ ≃L[ℝ] ℂ).contDiff.comp_contDiffOn hg1
    convert h1 using 1
    funext y
    simp
  have hhc : ContDiffOn ℝ ∞ h (OmX m) := hsg.mul (uW_contDiffOn l)
  have hfd : ∀ x ∈ OmX m, DifferentiableAt ℝ f x := fun x hx =>
    (hf1.differentiableOn (by simp)).differentiableAt (hΩo.mem_nhds hx)
  have hgd : ∀ x ∈ OmX m, DifferentiableAt ℝ g x := fun x hx =>
    (hg1.differentiableOn (by simp)).differentiableAt (hΩo.mem_nhds hx)
  have hud : ∀ x ∈ OmX m, DifferentiableAt ℝ (uW l) x := fun x hx =>
    ((uW_contDiffOn l).differentiableOn (by simp)).differentiableAt (hΩo.mem_nhds hx)
  have hhd : ∀ x ∈ OmX m, DifferentiableAt ℝ h x := fun x hx =>
    (hhc.differentiableOn (by simp)).differentiableAt (hΩo.mem_nhds hx)
  have hhg : tsupport h ⊆ tsupport g := by
    have h1 : tsupport h ⊆ tsupport (fun y => star (g y)) := tsupport_mul_subset_left
    rwa [tsupport_star_fun] at h1
  have hhΩ : tsupport h ⊆ OmX m := hhg.trans hgΩ
  have hhK : HasCompactSupport h := IsCompact.of_isClosed_subset hgc (isClosed_tsupport _) hhg
  have hfz : ∀ x, x ∉ OmX m → fderiv ℝ f x = 0 := by
    intro x hx
    have hx' : x ∉ tsupport f := fun h' => hx (hfΩ h')
    by_contra hne
    exact hx' (support_fderiv_subset ℝ hne)
  have hL : ∀ x, pOp l f x * star (g x) * (((∏ k, Complex.normSq (x k))⁻¹ : ℝ) : ℂ) =
      wirt l f x * h x := by
    intro x
    by_cases hx : x ∈ OmX m
    · simp only [pOp, if_pos hx, smul_eq_mul, hh, uW]
      ring
    · simp [pOp, hx, wirt, hfz x hx]
  have hR : ∀ x, f x * star (pbOp l g x) * (((∏ k, Complex.normSq (x k))⁻¹ : ℝ) : ℂ) =
      f x * wirt l h x := by
    intro x
    by_cases hx : x ∈ OmX m
    · have hsd : DifferentiableAt ℝ (fun y => star (g y)) x := (hgd x hx).star
      rw [hh, wirt_mul_fun l hsd (hud x hx), wirt_uW l x hx, wirt_star_fun]
      simp only [pbOp, if_pos hx, smul_eq_mul, star_mul', star_star, uW]
      ring
    · simp [hf2 x hx]
  have eL : (∫ x, pOp l f x * star (g x) * (((∏ k, Complex.normSq (x k))⁻¹ : ℝ) : ℂ)) =
      ∫ x, wirt l f x * h x := by
    congr 1
    funext x
    exact hL x
  have eR : (∫ x, f x * star (pbOp l g x) * (((∏ k, Complex.normSq (x k))⁻¹ : ℝ) : ℂ)) =
      ∫ x, f x * wirt l h x := by
    congr 1
    funext x
    exact hR x
  rw [eL, eR]
  have I1 : ∀ v, Integrable (fun x => fderiv ℝ f x v * h x) := by
    intro v
    refine integrable_of_on ?_ tsupport_mul_subset_right hhK hhΩ
    exact ((hf1.continuousOn_fderiv_of_isOpen hΩo (by simp)).clm_apply continuousOn_const).mul
      hhc.continuousOn
  have I2 : ∀ v, Integrable (fun x => f x * fderiv ℝ h x v) := by
    intro v
    refine integrable_of_on ?_ tsupport_mul_subset_left hfc hfΩ
    exact hf1.continuousOn.mul
      ((hhc.continuousOn_fderiv_of_isOpen hΩo (by simp)).clm_apply continuousOn_const)
  have I3 : Integrable (fun x => f x * h x) :=
    integrable_of_on (hf1.continuousOn.mul hhc.continuousOn) tsupport_mul_subset_left hfc hfΩ
  have ibp : ∀ v, ∫ x, f x * fderiv ℝ h x v = -∫ x, fderiv ℝ f x v * h x := by
    intro v
    exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (I1 v) (I2 v) I3
      (fun x hx => hfd x (hhΩ hx)) (fun x hx => hhd x (hfΩ hx))
  have hw : ∀ φ : (Fin m → ℂ) → ℂ, ∀ x, wirt l φ x = (1 / 2 : ℂ) *
      (fderiv ℝ φ x (Pi.single l 1) - Complex.I * fderiv ℝ φ x (Pi.single l Complex.I)) := by
    intro φ x
    simp [wirt, smul_eq_mul]
  simp_rw [hw]
  have lhs : (∫ x, (1 / 2 : ℂ) * (fderiv ℝ f x (Pi.single l 1) -
      Complex.I * fderiv ℝ f x (Pi.single l Complex.I)) * h x) =
      (1 / 2 : ℂ) * (∫ x, fderiv ℝ f x (Pi.single l 1) * h x) -
        ((1 / 2 : ℂ) * Complex.I) * ∫ x, fderiv ℝ f x (Pi.single l Complex.I) * h x := by
    rw [← integral_const_mul, ← integral_const_mul,
      ← integral_sub ((I1 _).const_mul _) ((I1 _).const_mul _)]
    congr 1
    funext x
    ring
  have rhs : (∫ x, f x * ((1 / 2 : ℂ) * (fderiv ℝ h x (Pi.single l 1) -
      Complex.I * fderiv ℝ h x (Pi.single l Complex.I)))) =
      (1 / 2 : ℂ) * (∫ x, f x * fderiv ℝ h x (Pi.single l 1)) -
        ((1 / 2 : ℂ) * Complex.I) * ∫ x, f x * fderiv ℝ h x (Pi.single l Complex.I) := by
    rw [← integral_const_mul, ← integral_const_mul,
      ← integral_sub ((I2 _).const_mul _) ((I2 _).const_mul _)]
    congr 1
    funext x
    ring
  rw [lhs, rhs, ibp, ibp]
  ring

end Formalism.QuantumDeterminants
