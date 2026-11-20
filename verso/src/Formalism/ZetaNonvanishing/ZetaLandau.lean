import Formalism.StatementU
import Formalism.ZetaNonvanishing.OfRealNeOfRealOfLt
import Formalism.ZetaNonvanishing.LandauEq
import Formalism.ZetaNonvanishing.MellinSgen
import Formalism.ZetaNonvanishing.MellinElem
import Formalism.ZetaNonvanishing.ZetaRealNonvanish
import Formalism.ZetaNonvanishing.LogDerivZeroFree
import Formalism.ZetaNonvanishing.MellinDeriv

open Complex MeasureTheory Set Filter Topology

noncomputable section

namespace Formalism

open ArithmeticFunction

def linZ (s : ℂ) : ℂ := -1 + (1 + (Real.eulerMascheroniConstant : ℂ)) * s

def nZ (s : ℂ) : ℂ := -(deriv riemannZeta₁ s / riemannZeta₁ s) + linZ s

def AZ (s : ℂ) : ℂ := -deriv riemannZeta₁ s + linZ s * riemannZeta₁ s

def HZ (ε C θ : ℝ) (x : ℝ) : ℝ := ε * Gz x + C * x ^ θ

def IZ (ε C θ : ℝ) (s : ℂ) : ℂ :=
  ∫ x in Ioi (1:ℝ), ((HZ ε C θ x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)

def PhiZ (ε C θ : ℝ) (s : ℂ) : ℂ := ε * dslope AZ 1 s / (s * riemannZeta₁ s) + C / (s - θ)

/- English proof (authored)
Multiply the corrected negative logarithmic derivative by the regularized zeta function. Since the regularized zeta value is nonzero, the denominator in its logarithmic derivative cancels. The remaining expression is the negative derivative plus the stated linear term times regularized zeta.
-/
lemma AZ_eq {s : ℂ} (hZ : riemannZeta₁ s ≠ 0) : AZ s = riemannZeta₁ s * nZ s := by
  unfold AZ nZ
  field_simp

/- English proof (authored)
At one the regularized zeta function has value one and derivative equal to the Euler–Mascheroni constant. The linear correction at one equals this same constant, so the two terms cancel.
-/
lemma AZ_one : AZ 1 = 0 := by
  unfold AZ linZ
  rw [deriv_riemannZeta₁_one, riemannZeta₁_one]
  ring

/- English proof (authored)
The regularized zeta function is entire, so its derivative is complex differentiable. The linear correction is also differentiable. Their indicated products and sum are differentiable everywhere.
-/
lemma differentiable_AZ : Differentiable ℂ AZ := by
  have hZ : Differentiable ℂ riemannZeta₁ := differentiable_riemannZeta₁
  have hZ' : Differentiable ℂ (deriv riemannZeta₁) := differentiable_deriv_of hZ
  unfold AZ linZ
  fun_prop

/- English proof (authored)
In the half-plane of real part greater than one the Mellin formula for the corrected weighted sum converges and the zeta factors are nonzero. Substitute the relation between the logarithmic derivatives of zeta and its regularization. Combining the rational terms gives the corrected negative logarithmic derivative divided by the product of the variable and the variable minus one.
-/
lemma mellin_Gz_n (h3 : MellinSgen) (h5 : MellinElem) {s : ℂ} (hs : 1 < s.re) :
    ∫ x in Ioi (1:ℝ), (Gz x : ℂ) * (x : ℂ) ^ (-s - 1) = nZ s / (s * (s - 1)) := by
  have hs1 : s ≠ 1 := ne_one_of_one_lt_re hs
  have hs1' : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  have hs0 : s ≠ 0 := ne_zero_of_lt_re zero_le_one hs
  have hz := riemannZeta_ne_zero_of_one_le_re hs.le
  have hZ1 := riemannZetaOne_ne_zero_of_one_le_re hs.le
  rw [(mellin_Gz h3 h5 hs).2, logderiv_zeta_eq hs1 hz]
  unfold nZ linZ
  field_simp
  ring

/- English proof (authored)
The corrected weighted sum is measurable, as is the real power function. A linear combination with constant coefficients is measurable.
-/
lemma measurable_HZ (h3 : MellinSgen) (ε C θ : ℝ) : Measurable (HZ ε C θ) := by
  have hz := measurable_Gz h3
  unfold HZ
  exact (measurable_const.mul hz).add (measurable_const.mul (measurable_id.pow_const _))

/- English proof (authored)
After distributing the Mellin weight, the integrand is the sum of a constant multiple of the corrected weighted sum times that weight and a constant multiple of the power term times the weight. The first is integrable for the real exponent above one. The second is integrable because the real exponent is also above the power exponent. Their sum is integrable.
-/
lemma rint_HZ (h3 : MellinSgen) (h5 : MellinElem) {ε C θ : ℝ} (hθ : θ < 1) {σ : ℝ}
    (hσ : 1 < σ) : IntegrableOn (fun x : ℝ => HZ ε C θ x * x ^ (-σ - 1)) (Ioi 1) := by
  have a1 := rint_Gz h3 h5 hσ
  have a4 := h5.1 θ σ (by linarith)
  have hfun : (fun x : ℝ => HZ ε C θ x * x ^ (-σ - 1)) = fun x =>
      ε * (Gz x * x ^ (-σ - 1)) + C * (x ^ θ * x ^ (-σ - 1)) := by
    funext x
    simp only [HZ]
    ring
  rw [hfun]
  exact Integrable.add (Integrable.const_mul a1 _) (Integrable.const_mul a4 _)

/- English proof (authored)
Both weighted summands are integrable when the real part exceeds one because the power exponent is below one. Split the integral and take out the constant coefficients. The weighted sum has the corrected logarithmic-derivative Mellin formula, and integrating the power gives the reciprocal of the complex variable minus the power exponent. Combining the two terms gives the stated transform.
-/
lemma mellin_HZ (h3 : MellinSgen) (h5 : MellinElem) {ε C θ : ℝ} (hθ : θ < 1)
    {s : ℂ} (hs : 1 < s.re) :
    IZ ε C θ s = ε * nZ s / (s * (s - 1)) + C / (s - θ) := by
  have iz := (mellin_Gz h3 h5 hs).1
  have i4 : IntegrableOn (fun x : ℝ => ((x ^ θ : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)) (Ioi 1) :=
    cint_of_abs _ (by fun_prop) s (int_abs_rpow h5 (by linarith))
  have hfun : (fun x : ℝ => ((HZ ε C θ x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)) = fun x =>
      (ε : ℂ) * ((Gz x : ℂ) * (x : ℂ) ^ (-s - 1))
        + (C : ℂ) * (((x ^ θ : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)) := by
    funext x
    simp only [HZ]
    push_cast
    ring
  unfold IZ
  rw [hfun, integral_add (Integrable.const_mul iz _) (Integrable.const_mul i4 _),
    integral_const_mul, integral_const_mul, mellin_Gz_n h3 h5 hs, h5.2.2.1 θ s (by linarith)]
  ring

/- English proof (authored)
Away from one the divided difference is the difference of the two values divided by the difference of the inputs. The value of the numerator function at one is zero. Substitute its expression as regularized zeta times the corrected logarithmic derivative, and cancel the nonzero regularized zeta value.
-/
lemma PhiZ_eq {ε C θ : ℝ} {s : ℂ} (hs1 : s ≠ 1) (hs0 : s ≠ 0) (hZ : riemannZeta₁ s ≠ 0) :
    PhiZ ε C θ s = ε * nZ s / (s * (s - 1)) + C / (s - θ) := by
  have hs1' : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  unfold PhiZ
  rw [dslope_of_ne _ hs1, slope_def_field, AZ_one, sub_zero, AZ_eq hZ]
  field_simp

/- English proof (authored)
In the half-plane of real part greater than one, the variable is neither zero nor one, and the regularized zeta function is nonzero. The algebraic continuation formula and the Mellin integral evaluation therefore give the same rational expression there.
-/
lemma PhiZ_eq_IZ (h3 : MellinSgen) (h5 : MellinElem) {ε C θ : ℝ} (hθ : θ < 1)
    {s : ℂ} (hs : 1 < s.re) : PhiZ ε C θ s = IZ ε C θ s := by
  rw [mellin_HZ h3 h5 hθ hs, PhiZ_eq (ne_one_of_one_lt_re hs) (ne_zero_of_lt_re zero_le_one hs)
    (riemannZetaOne_ne_zero_of_one_le_re hs.le)]

/- English proof (authored)
Work in the open set where the variable, its regularized zeta value, and its difference from the chosen real exponent are nonzero. The divided difference of the entire numerator function, with its derivative value at one, is complex differentiable everywhere. On this open set the denominators do not vanish, so both displayed quotients are complex differentiable. Their sum is analytic at every point of the open set.
-/
lemma PhiZ_analyticAt (ε C θ : ℝ) {s : ℂ} (hs0 : s ≠ 0)
    (hE : riemannZeta₁ s ≠ 0) (hsθ : s ≠ θ) : AnalyticAt ℂ (PhiZ ε C θ) s := by
  set V : Set ℂ := {z | z ≠ 0 ∧ riemannZeta₁ z ≠ 0 ∧ z ≠ θ} with hV
  have hEd : Differentiable ℂ riemannZeta₁ := differentiable_riemannZeta₁
  have hVo : IsOpen V :=
    isOpen_ne.inter ((isOpen_ne_fun hEd.continuous continuous_const).inter isOpen_ne)
  have hdsl : DifferentiableOn ℂ (dslope AZ 1) univ :=
    (differentiableOn_dslope Filter.univ_mem).mpr differentiable_AZ.differentiableOn
  have hd : DifferentiableOn ℂ (PhiZ ε C θ) V := by
    intro z hz
    apply DifferentiableAt.differentiableWithinAt
    have h1 : DifferentiableAt ℂ (dslope AZ 1) z :=
      (hdsl z (mem_univ z)).differentiableAt Filter.univ_mem
    have h2 : DifferentiableAt ℂ riemannZeta₁ z := hEd z
    unfold PhiZ
    apply DifferentiableAt.add
    · exact (h1.const_mul _).div (differentiableAt_id.mul h2) (mul_ne_zero hz.1 hz.2.1)
    · exact (differentiableAt_const _).div (differentiableAt_id.sub_const _)
        (sub_ne_zero.mpr hz.2.2)
  exact hd.analyticAt (hVo.mem_nhds ⟨hs0, hE, hsθ⟩)

/- English proof (authored)
The modified weighted sum is measurable and nonnegative, and its Mellin integral converges for real exponents above one. There the proposed continuation agrees with the transform and is analytic. At every real exponent above the chosen positive exponent and at most one, its denominators are nonzero by real nonvanishing of regularized zeta and by the explicit value at one. The continuation is analytic around those real points as well. Landau's positive-integrand theorem therefore gives integrability for every real exponent above the chosen one.
-/
lemma landau_Z (h2 : LandauEq) (h3 : MellinSgen) (h5 : MellinElem) (h8 : ZetaRealNonvanish)
    {ε C θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (hH : ∀ x : ℝ, 1 ≤ x → 0 ≤ HZ ε C θ x) :
    ∀ σ : ℝ, θ < σ → IntegrableOn (fun x : ℝ => HZ ε C θ x * x ^ (-σ - 1)) (Ioi 1) := by
  intro σ hσ
  refine (h2 (HZ ε C θ) θ 1 hθ1 (measurable_HZ h3 ε C θ).aestronglyMeasurable
    (fun x hx => hH x (le_of_lt hx)) (fun σ hσ => rint_HZ h3 h5 hθ1 hσ) (PhiZ ε C θ)
    ?_ ?_ (fun s hs => PhiZ_eq_IZ h3 h5 hθ1 hs) σ hσ).1
  · intro s hs
    exact PhiZ_analyticAt ε C θ (ne_zero_of_lt_re zero_le_one hs)
      (riemannZetaOne_ne_zero_of_one_le_re hs.le) (ne_ofReal_of_lt_re (by linarith))
  · intro σ h1' h2'
    have hσ0 : (σ : ℂ) ≠ 0 := by exact_mod_cast (show σ ≠ 0 by linarith)
    have hσθ : (σ : ℂ) ≠ θ := ofReal_ne_ofReal_of_lt (by linarith)
    refine PhiZ_analyticAt ε C θ hσ0 ?_ hσθ
    rcases h2'.lt_or_eq with h2' | h2'
    · exact riemannZetaOne_ne_zero_of_real_mem_Ioo h8 (by linarith) h2'
    · subst h2'
      exact riemannZetaOne_ne_zero_of_one_le_re (by simp)

/- English proof (authored)
On the half-plane above the chosen exponent, the Mellin transform is analytic by differentiation under the integral. Subtract the elementary power contribution and multiply by the variable, the variable minus one, and regularized zeta. This gives an analytic function on that half-plane. In the smaller half-plane to the right of one, the Mellin formula identifies it with the signed entire numerator used in the continuation. The identity theorem gives this equality throughout the larger half-plane.

Use the sign squared equal to one to rearrange the identity as a differential equation. The derivative of regularized zeta equals regularized zeta times an analytic function on the half-plane. Regularized zeta is entire and has value one at one, so the logarithmic-derivative nonvanishing criterion rules out any zero there.
-/
lemma riemannZetaOne_ne_zero_of_integrable_mellin (h1 : MellinDeriv) (h3 : MellinSgen) (h5 : MellinElem)
    (h11 : LogDerivZeroFree) {ε C θ : ℝ} (hε : ε * ε = 1) (hθ1 : θ < 1)
    (hH : ∀ x : ℝ, 1 ≤ x → 0 ≤ HZ ε C θ x)
    (hInt : ∀ σ : ℝ, θ < σ → IntegrableOn (fun x : ℝ => HZ ε C θ x * x ^ (-σ - 1)) (Ioi 1)) :
    ∀ s : ℂ, θ < s.re → riemannZeta₁ s ≠ 0 := by
  set U : Set ℂ := {s | θ < s.re} with hU_def
  have hUopen : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hId : DifferentiableOn ℂ (IZ ε C θ) U := by
    intro s hs
    have hD := h1 (fun x => ((HZ ε C θ x : ℝ) : ℂ)) θ
      (Complex.measurable_ofReal.comp (measurable_HZ h3 ε C θ)).aestronglyMeasurable
      (fun σ hσ => (hInt σ hσ).congr_fun (fun x hx => by
        simp only [Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (hH x (le_of_lt (mem_Ioi.mp hx)))])
        measurableSet_Ioi) s hs
    exact hD.differentiableAt.differentiableWithinAt
  have hZd : Differentiable ℂ riemannZeta₁ := differentiable_riemannZeta₁
  have hAd := differentiable_AZ
  have hf1 : DifferentiableOn ℂ
      (fun s => s * (s - 1) * riemannZeta₁ s * (IZ ε C θ s - C / (s - θ))) U := by
    intro s hs
    have hsθ : s - (θ : ℂ) ≠ 0 := sub_ne_zero_of_lt_re hs
    have hIs := (hId s hs).differentiableAt (hUopen.mem_nhds hs)
    have hEs := hZd s
    apply DifferentiableAt.differentiableWithinAt
    fun_prop (disch := exact hsθ)
  have hEq : EqOn (fun s => s * (s - 1) * riemannZeta₁ s * (IZ ε C θ s - C / (s - θ)))
      (fun s => (ε : ℂ) * AZ s) U := by
    refine AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq
      (hf1.analyticOnNhd hUopen)
      ((hAd.const_mul (ε : ℂ)).differentiableOn.analyticOnNhd hUopen)
      (convex_halfSpace_re_gt θ).isPreconnected (z₀ := 2)
      (show θ < (2:ℂ).re by simp; linarith) ?_
    have h2mem : (2:ℂ) ∈ {s : ℂ | 1 < s.re} := by simp
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds h2mem] with z hz
    have hz' : 1 < z.re := hz
    have hZ := riemannZetaOne_ne_zero_of_one_le_re hz'.le
    have hs1' : z - 1 ≠ 0 := sub_ne_zero.mpr (ne_one_of_one_lt_re hz')
    have hs0 : z ≠ 0 := ne_zero_of_lt_re zero_le_one hz'
    have hsθ : z - θ ≠ 0 := sub_ne_zero_of_lt_re (a := θ) (by linarith)
    rw [mellin_HZ h3 h5 hθ1 hz', AZ_eq hZ]
    field_simp
    ring
  set q : ℂ → ℂ := fun s => linZ s - (ε : ℂ) * (s * (s - 1) * (IZ ε C θ s - C / (s - θ)))
    with hq_def
  have hqd : DifferentiableOn ℂ q U := by
    intro s hs
    have hsθ : s - (θ : ℂ) ≠ 0 := sub_ne_zero_of_lt_re hs
    have hIs := (hId s hs).differentiableAt (hUopen.mem_nhds hs)
    apply DifferentiableAt.differentiableWithinAt
    simp only [hq_def, linZ]
    fun_prop (disch := exact hsθ)
  have hid : ∀ s ∈ U, deriv riemannZeta₁ s = q s * riemannZeta₁ s := by
    intro s hs
    have he := hEq hs
    simp only at he
    unfold AZ at he
    have hεc : (ε : ℂ) * ε = 1 := by exact_mod_cast hε
    simp only [hq_def]
    linear_combination (ε : ℂ) * he - (deriv riemannZeta₁ s - linZ s * riemannZeta₁ s) * hεc
  intro s hs
  exact h11 riemannZeta₁ q U hUopen hZd ⟨1, by simp⟩ hqd hid s hs

/- English proof (authored)
Every summand is nonnegative because the von Mangoldt weight is nonnegative and the index is at most the argument. Since the index is at least one, the factor given by the argument divided by the index minus one is at most the argument and hence at most the larger bound. Replace each factor by this bound, then extend the sum to the larger set of indices using nonnegativity.
-/
lemma Sz_bound {x X : ℝ} (hx1 : 1 ≤ x) (hxX : x ≤ X) :
    0 ≤ Sz x ∧ Sz x ≤ X * ∑ n ∈ Finset.Icc 1 ⌊X⌋₊, Λ n := by
  unfold Sz
  constructor
  · apply Finset.sum_nonneg
    intro n hn
    have hn' := Finset.mem_Icc.mp hn
    have hnpos : (0:ℝ) < n := by exact_mod_cast hn'.1
    have hnx : (n:ℝ) ≤ x := (Nat.cast_le.mpr hn'.2).trans (Nat.floor_le (by linarith))
    apply mul_nonneg vonMangoldt_nonneg
    rw [sub_nonneg, le_div_iff₀ hnpos]
    linarith
  · rw [Finset.mul_sum]
    calc ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, Λ n * (x / n - 1)
        ≤ ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, X * Λ n := by
          apply Finset.sum_le_sum
          intro n hn
          have hn' := Finset.mem_Icc.mp hn
          have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn'.1
          have hdiv : x / n ≤ x := div_le_self (by linarith) hn1
          have hΛ : (0:ℝ) ≤ Λ n := vonMangoldt_nonneg
          nlinarith [mul_nonneg hΛ (show 0 ≤ x - x / n + 1 by linarith),
            mul_nonneg hΛ (show 0 ≤ X - x by linarith)]
      _ ≤ ∑ n ∈ Finset.Icc 1 ⌊X⌋₊, X * Λ n := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · exact Finset.Icc_subset_Icc le_rfl (Nat.floor_mono hxX)
          · intro n _ _
            exact mul_nonneg (by linarith) vonMangoldt_nonneg

/- English proof (authored)
On the given finite interval the weighted sum is nonnegative and bounded by the larger endpoint times the sum of the weights through its integer part. The term given by the argument times its logarithm is nonnegative and bounded by its value at the endpoint, because both factors are nonnegative and increasing there. The positive linear correction is likewise bounded at the endpoint. The sum of these three endpoint bounds bounds the absolute value of the corrected sum.
-/
lemma Gz_bdd {X : ℝ} (hX : 1 ≤ X) : ∃ B : ℝ, 0 ≤ B ∧ ∀ x : ℝ, 1 ≤ x → x ≤ X → |Gz x| ≤ B := by
  have hγ : 0 ≤ Real.eulerMascheroniConstant := by
    linarith [Real.one_half_lt_eulerMascheroniConstant]
  have hS0 : 0 ≤ X * ∑ n ∈ Finset.Icc 1 ⌊X⌋₊, Λ n :=
    mul_nonneg (by linarith) (Finset.sum_nonneg fun n _ => vonMangoldt_nonneg)
  have hlX : 0 ≤ Real.log X := Real.log_nonneg hX
  refine ⟨X * ∑ n ∈ Finset.Icc 1 ⌊X⌋₊, Λ n + X * Real.log X
      + (1 + Real.eulerMascheroniConstant) * X, by positivity, ?_⟩
  intro x hx1 hxX
  obtain ⟨hS1, hS2⟩ := Sz_bound hx1 hxX
  have hl0 : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hl1 : Real.log x ≤ Real.log X := Real.log_le_log (by linarith) hxX
  have hxl : x * Real.log x ≤ X * Real.log X := mul_le_mul hxX hl1 hl0 (by linarith)
  have hxl0 : 0 ≤ x * Real.log x := mul_nonneg (by linarith) hl0
  have hg : (1 + Real.eulerMascheroniConstant) * x ≤ (1 + Real.eulerMascheroniConstant) * X :=
    mul_le_mul_of_nonneg_left hxX (by linarith)
  have hg0 : 0 ≤ (1 + Real.eulerMascheroniConstant) * x := mul_nonneg (by linarith) (by linarith)
  unfold Gz
  rw [abs_le]
  constructor <;> nlinarith

/- English proof (authored)
Choose a constant at least as large as the constant in the eventual one-sided bound and the absolute bound on the initial finite interval. Since the exponent is positive, the power of an argument at least one is at least one. Thus subtracting the given signed corrected sum from this power term gives a nonnegative function on the whole integration interval. Its sign coefficient squares to one. The Landau integrability theorem and the differential-equation criterion give nonvanishing of regularized zeta above the chosen exponent. Away from one this implies nonvanishing of ordinary zeta by the regularization identity. At one use the stated zeta nonvanishing on the line of real part one.
-/
theorem zetaLandau : ZetaLandau := by
  intro s₀ hs₀ θ hθ0 hθ1 hCex s hs
  obtain ⟨C, x₀, hC⟩ := hCex
  obtain ⟨B, hB0, hB⟩ := Gz_bdd (le_max_right x₀ 1)
  have hs₀abs : |s₀| = 1 := by rcases hs₀ with h | h <;> simp [h]
  have hε : (-s₀) * (-s₀) = 1 := by rcases hs₀ with h | h <;> simp [h]
  have hCC : C ≤ max C B := le_max_left _ _
  have hBC : B ≤ max C B := le_max_right _ _
  have hH : ∀ x : ℝ, 1 ≤ x → 0 ≤ HZ (-s₀) (max C B) θ x := by
    intro x hx
    have hxθ : 1 ≤ x ^ θ := Real.one_le_rpow hx hθ0.le
    unfold HZ
    rcases le_or_gt x (max x₀ 1) with hxX | hxX
    · have h1 := hB x hx hxX
      have h2 : s₀ * Gz x ≤ B := by
        calc s₀ * Gz x ≤ |s₀ * Gz x| := le_abs_self _
          _ = |Gz x| := by rw [abs_mul, hs₀abs, one_mul]
          _ ≤ B := h1
      have h3 : B ≤ max C B * x ^ θ := by
        nlinarith [mul_nonneg (show 0 ≤ max C B by linarith) (show 0 ≤ x ^ θ - 1 by linarith)]
      linarith
    · have h1 := hC x (le_of_lt (lt_of_le_of_lt (le_max_left _ _) hxX))
      have h2 : C * x ^ θ ≤ max C B * x ^ θ := mul_le_mul_of_nonneg_right hCC (by linarith)
      linarith
  have hInt := landau_Z landauEq mellinSgen mellinElem zetaRealNonvanish
    hθ0 hθ1 hH
  have hZ1 := riemannZetaOne_ne_zero_of_integrable_mellin mellinDeriv mellinSgen mellinElem
    logDerivZeroFree hε hθ1 hH hInt s hs
  by_cases h1 : s = 1
  · subst h1
    exact riemannZeta_ne_zero_of_one_le_re (by simp)
  · rw [riemannZetaOne_eq_mul_of_ne_one h1] at hZ1
    exact right_ne_zero_of_mul hZ1

/- English proof (authored)
Choose a positive allowance no larger than half either gap, the gap from the given exponent to the point's real part and the gap to one. The shifted exponent is still below both. The given eventual bound at that shifted exponent now meets the one-sided zeta Landau theorem, which gives nonvanishing at the point.
-/
theorem zetaLandauEps : ZetaLandauEps := by
  intro s₀ hs₀ θ hθ0 hθ1 hB s hs
  obtain ⟨ε, hε0, hε1, hε2⟩ : ∃ ε : ℝ, 0 < ε ∧ θ + ε < s.re ∧ θ + ε < 1 := by
    refine ⟨min ((s.re - θ) / 2) ((1 - θ) / 2), lt_min (by linarith) (by linarith), ?_, ?_⟩
    · have := min_le_left ((s.re - θ) / 2) ((1 - θ) / 2); linarith
    · have := min_le_right ((s.re - θ) / 2) ((1 - θ) / 2); linarith
  exact zetaLandau s₀ hs₀ (θ + ε) (by linarith) hε2 (hB ε hε0) s hε1

end Formalism
