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

/- English proof (translation)
Unfold `AZ nZ`. Clear the denominators using the available nonvanishing facts.
-/
lemma AZ_eq {s : ℂ} (hZ : riemannZeta₁ s ≠ 0) : AZ s = riemannZeta₁ s * nZ s := by
  unfold AZ nZ
  field_simp

/- English proof (translation)
Unfold `AZ linZ`. Rewrite using `[deriv_riemannZeta₁_one, riemannZeta₁_one]`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma AZ_one : AZ 1 = 0 := by
  unfold AZ linZ
  rw [deriv_riemannZeta₁_one, riemannZeta₁_one]
  ring

/- English proof (translation)
Establish `hZ : Differentiable ℂ riemannZeta₁` using `differentiable_riemannZeta₁`. Establish `hZ' : Differentiable ℂ (deriv riemannZeta₁)` using `differentiable_deriv_of hZ`. Unfold `AZ linZ`. Use `fun_prop`.
-/
lemma differentiable_AZ : Differentiable ℂ AZ := by
  have hZ : Differentiable ℂ riemannZeta₁ := differentiable_riemannZeta₁
  have hZ' : Differentiable ℂ (deriv riemannZeta₁) := differentiable_deriv_of hZ
  unfold AZ linZ
  fun_prop

/- English proof (translation)
Establish `hs1 : s ≠ 1` using `ne_one_of_one_lt_re hs`. Establish `hs1' : s - 1 ≠ 0` using `sub_ne_zero.mpr hs1`. Establish `hs0 : s ≠ 0` using `ne_zero_of_lt_re zero_le_one hs`. Establish `hz` using `riemannZeta_ne_zero_of_one_le_re hs.le`. Establish `hZ1` using `riemannZetaOne_ne_zero_of_one_le_re hs.le`.

Rewrite using `[(mellin_Gz h3 h5 hs).2, logderiv_zeta_eq hs1 hz]`. Unfold `nZ linZ`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
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

/- English proof (translation)
Establish `hz` using `measurable_Gz h3`. Unfold `HZ`. Conclude with `(measurable_const.mul hz).add (measurable_const.mul (measurable_id.pow_const _))`.
-/
lemma measurable_HZ (h3 : MellinSgen) (ε C θ : ℝ) : Measurable (HZ ε C θ) := by
  have hz := measurable_Gz h3
  unfold HZ
  exact (measurable_const.mul hz).add (measurable_const.mul (measurable_id.pow_const _))

/- English proof (translation)
Establish `a1` using `rint_Gz h3 h5 hσ`. Establish `a4` using `h5.1 θ σ (by linarith)`. Establish `hfun : (fun x : ℝ => HZ ε C θ x * x ^ (-σ - 1)) = fun x => ε * (Gz x * x ^ (-σ - 1)) + C * (x ^ θ * x ^ (-σ - 1))`. Use function extensionality and compare the values at `x`. Simplify using `only [HZ]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hfun]`. Conclude with `Integrable.add (Integrable.const_mul a1 _) (Integrable.const_mul a4 _)`.
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

/- English proof (translation)
Establish `iz` using `(mellin_Gz h3 h5 hs).1`. Establish `i4 : IntegrableOn (fun x : ℝ => ((x ^ θ : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)) (Ioi 1)` using `cint_of_abs _ (by fun_prop) s (int_abs_rpow h5 (by linarith))`. Establish `hfun : (fun x : ℝ => ((HZ ε C θ x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)) = fun x => (ε : ℂ) * ((Gz x : ℂ) * (x : ℂ) ^ (-s - 1)) + (C : ℂ) * (((x ^ θ : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1))`. Use function extensionality and compare the values at `x`. Simplify using `only [HZ]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Unfold `IZ`. Rewrite using `[hfun, integral_add (Integrable.const_mul iz _) (Integrable.const_mul i4 _), integral_const_mul, integral_const_mul, mellin_Gz_n h3 h5 hs, h5.2.2.1 θ s (by linarith)]`. Expand and normalize the polynomial expressions, which then agree.
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

/- English proof (translation)
Establish `hs1' : s - 1 ≠ 0` using `sub_ne_zero.mpr hs1`. Unfold `PhiZ`. Rewrite using `[dslope_of_ne _ hs1, slope_def_field, AZ_one, sub_zero, AZ_eq hZ]`. Clear the denominators using the available nonvanishing facts.
-/
lemma PhiZ_eq {ε C θ : ℝ} {s : ℂ} (hs1 : s ≠ 1) (hs0 : s ≠ 0) (hZ : riemannZeta₁ s ≠ 0) :
    PhiZ ε C θ s = ε * nZ s / (s * (s - 1)) + C / (s - θ) := by
  have hs1' : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  unfold PhiZ
  rw [dslope_of_ne _ hs1, slope_def_field, AZ_one, sub_zero, AZ_eq hZ]
  field_simp

/- English proof (translation)
Rewrite using `[mellin_HZ h3 h5 hθ hs, PhiZ_eq (ne_one_of_one_lt_re hs) (ne_zero_of_lt_re zero_le_one hs) (riemannZetaOne_ne_zero_of_one_le_re hs.le)]`.
-/
lemma PhiZ_eq_IZ (h3 : MellinSgen) (h5 : MellinElem) {ε C θ : ℝ} (hθ : θ < 1)
    {s : ℂ} (hs : 1 < s.re) : PhiZ ε C θ s = IZ ε C θ s := by
  rw [mellin_HZ h3 h5 hθ hs, PhiZ_eq (ne_one_of_one_lt_re hs) (ne_zero_of_lt_re zero_le_one hs)
    (riemannZetaOne_ne_zero_of_one_le_re hs.le)]

/- English proof (translation)
Use `set V : Set ℂ := {z | z ≠ 0 ∧ riemannZeta₁ z ≠ 0 ∧ z ≠ θ} with hV`. Establish `hEd : Differentiable ℂ riemannZeta₁` using `differentiable_riemannZeta₁`. Establish `hVo : IsOpen V` using `isOpen_ne.inter ((isOpen_ne_fun hEd.continuous continuous_const).inter isOpen_ne)`. Establish `hdsl : DifferentiableOn ℂ (dslope AZ 1) univ` using `(differentiableOn_dslope Filter.univ_mem).mpr differentiable_AZ.differentiableOn`. Establish `hd : DifferentiableOn ℂ (PhiZ ε C θ) V`.

Introduce `z hz`. Apply `DifferentiableAt.differentiableWithinAt` to reduce the goal to its premises. Establish `h1 : DifferentiableAt ℂ (dslope AZ 1) z` using `(hdsl z (mem_univ z)).differentiableAt Filter.univ_mem`. Establish `h2 : DifferentiableAt ℂ riemannZeta₁ z` using `hEd z`. Unfold `PhiZ`.

Apply `DifferentiableAt.add` to reduce the goal to its premises. Conclude with `(h1.const_mul _).div (differentiableAt_id.mul h2) (mul_ne_zero hz.1 hz.2.1)`. Conclude with `(differentiableAt_const _).div (differentiableAt_id.sub_const _) (sub_ne_zero.mpr hz.2.2)`. Conclude with `hd.analyticAt (hVo.mem_nhds ⟨hs0, hE, hsθ⟩)`.
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

/- English proof (translation)
Introduce `σ hσ`. Use `(h2 (HZ ε C θ) θ 1 hθ1 (measurable_HZ h3 ε C θ).aestronglyMeasurable (fun x hx => hH x (le_of_lt hx)) (fun σ hσ => rint_HZ h3 h5 hθ1 hσ) (PhiZ ε C θ) ?_ ?_ (fun s hs => PhiZ_eq_IZ h3 h5 hθ1 hs) σ hσ).1` and prove the remaining obligations. Introduce `s hs`. Conclude with `PhiZ_analyticAt ε C θ (ne_zero_of_lt_re zero_le_one hs) (riemannZetaOne_ne_zero_of_one_le_re hs.le) (ne_ofReal_of_lt_re (by linarith))`. Introduce `σ h1' h2'`.

Establish `hσ0 : (σ : ℂ) ≠ 0` using `by exact_mod_cast (show σ ≠ 0 by linarith)`. Establish `hσθ : (σ : ℂ) ≠ θ` using `ofReal_ne_ofReal_of_lt (by linarith)`. Use `PhiZ_analyticAt ε C θ hσ0 ?_ hσθ` and prove the remaining obligations. Break down `h2'.lt_or_eq with h2' | h2'` into its components or cases. Conclude with `riemannZetaOne_ne_zero_of_real_mem_Ioo h8 (by linarith) h2'`.

Substitute `h2'` using the available equality. Conclude with `riemannZetaOne_ne_zero_of_one_le_re (by simp)`.
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

/- English proof (translation)
Use `set U : Set ℂ := {s | θ < s.re} with hU_def`. Establish `hUopen : IsOpen U` using `isOpen_lt continuous_const Complex.continuous_re`. Establish `hId : DifferentiableOn ℂ (IZ ε C θ) U`. Introduce `s hs`. Establish `hD` using `h1 (fun x => ((HZ ε C θ x : ℝ) : ℂ)) θ (Complex.measurable_ofReal.comp (measurable_HZ h3 ε C θ)).aestronglyMeasurable (fun σ hσ => (hInt σ hσ).congr_fun (fun x hx => by`.

Simplify using `only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hH x (le_of_lt (mem_Ioi.mp hx)))])`. Use the proof step `measurableSet_Ioi) s hs`. Conclude with `hD.differentiableAt.differentiableWithinAt`. Establish `hZd : Differentiable ℂ riemannZeta₁` using `differentiable_riemannZeta₁`. Establish `hAd` using `differentiable_AZ`.

Establish `hf1 : DifferentiableOn ℂ (fun s => s * (s - 1) * riemannZeta₁ s * (IZ ε C θ s - C / (s - θ))) U`. Introduce `s hs`. Establish `hsθ : s - (θ : ℂ) ≠ 0` using `sub_ne_zero_of_lt_re hs`. Establish `hIs` using `(hId s hs).differentiableAt (hUopen.mem_nhds hs)`. Establish `hEs` using `hZd s`.

Apply `DifferentiableAt.differentiableWithinAt` to reduce the goal to its premises. Use `fun_prop (disch := exact hsθ)`. Establish `hEq : EqOn (fun s => s * (s - 1) * riemannZeta₁ s * (IZ ε C θ s - C / (s - θ))) (fun s => (ε : ℂ) * AZ s) U`. Use `AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq (hf1.analyticOnNhd hUopen) ((hAd.const_mul (ε : ℂ)).differentiableOn.analyticOnNhd hUopen) (convex_halfSpace_re_gt θ).isPreconnected (z₀ := 2) (show θ < (2:ℂ).re by simp; linarith) ?_` and prove the remaining obligations. Establish `h2mem : (2:ℂ) ∈ {s : ℂ | 1 < s.re}` using `by simp`.

Use `filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds h2mem] with z hz`. Establish `hz' : 1 < z.re` using `hz`. Establish `hZ` using `riemannZetaOne_ne_zero_of_one_le_re hz'.le`. Establish `hs1' : z - 1 ≠ 0` using `sub_ne_zero.mpr (ne_one_of_one_lt_re hz')`. Establish `hs0 : z ≠ 0` using `ne_zero_of_lt_re zero_le_one hz'`.

Establish `hsθ : z - θ ≠ 0` using `sub_ne_zero_of_lt_re (a := θ) (by linarith)`. Rewrite using `[mellin_HZ h3 h5 hθ1 hz', AZ_eq hZ]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Use `set q : ℂ → ℂ := fun s => linZ s - (ε : ℂ) * (s * (s - 1) * (IZ ε C θ s - C / (s - θ))) with hq_def`.

Establish `hqd : DifferentiableOn ℂ q U`. Introduce `s hs`. Establish `hsθ : s - (θ : ℂ) ≠ 0` using `sub_ne_zero_of_lt_re hs`. Establish `hIs` using `(hId s hs).differentiableAt (hUopen.mem_nhds hs)`. Apply `DifferentiableAt.differentiableWithinAt` to reduce the goal to its premises.

Simplify using `only [hq_def, linZ]`. Use `fun_prop (disch := exact hsθ)`. Establish `hid : ∀ s ∈ U, deriv riemannZeta₁ s = q s * riemannZeta₁ s`. Introduce `s hs`. Establish `he` using `hEq hs`.

Simplify using `only at he`. Unfold `AZ at he`. Establish `hεc : (ε : ℂ) * ε = 1` using `by exact_mod_cast hε`. Simplify using `only [hq_def]`. Take the linear combination `(ε : ℂ) * he - (deriv riemannZeta₁ s - linZ s * riemannZeta₁ s) * hεc`.

Introduce `s hs`. Conclude with `h11 riemannZeta₁ q U hUopen hZd ⟨1, by simp⟩ hqd hid s hs`.
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

/- English proof (translation)
Unfold `Sz`. Prove the components needed by the constructor for the conclusion. Apply `Finset.sum_nonneg` to reduce the goal to its premises. Introduce `n hn`. Establish `hn'` using `Finset.mem_Icc.mp hn`.

Establish `hnpos : (0:ℝ) < n` using `by exact_mod_cast hn'.1`. Establish `hnx : (n:ℝ) ≤ x` using `(Nat.cast_le.mpr hn'.2).trans (Nat.floor_le (by linarith))`. Apply `mul_nonneg vonMangoldt_nonneg` to reduce the goal to its premises. Rewrite using `[sub_nonneg, le_div_iff₀ hnpos]`. Combine the linear equalities and inequalities to obtain the conclusion.

Rewrite using `[Finset.mul_sum]`. Combine the equalities or inequalities in the displayed calculation. Apply `Finset.sum_le_sum` to reduce the goal to its premises. Introduce `n hn`. Establish `hn'` using `Finset.mem_Icc.mp hn`.

Establish `hn1 : (1:ℝ) ≤ n` using `by exact_mod_cast hn'.1`. Establish `hdiv : x / n ≤ x` using `div_le_self (by linarith) hn1`. Establish `hΛ : (0:ℝ) ≤ Λ n` using `vonMangoldt_nonneg`. Use polynomial arithmetic with `[mul_nonneg hΛ (show 0 ≤ x - x / n + 1 by linarith), mul_nonneg hΛ (show 0 ≤ X - x by linarith)]`. Use `_ ≤ ∑ n ∈ Finset.Icc 1 ⌊X⌋₊, X * Λ n := by`.

Apply `Finset.sum_le_sum_of_subset_of_nonneg` to reduce the goal to its premises. Conclude with `Finset.Icc_subset_Icc le_rfl (Nat.floor_mono hxX)`. Introduce `n _ _`. Conclude with `mul_nonneg (by linarith) vonMangoldt_nonneg`.
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

/- English proof (translation)
Establish `hγ : 0 ≤ Real.eulerMascheroniConstant`. Combine the linear relations using `[Real.one_half_lt_eulerMascheroniConstant]`. Establish `hS0 : 0 ≤ X * ∑ n ∈ Finset.Icc 1 ⌊X⌋₊, Λ n` using `mul_nonneg (by linarith) (Finset.sum_nonneg fun n _ => vonMangoldt_nonneg)`. Establish `hlX : 0 ≤ Real.log X` using `Real.log_nonneg hX`. Use `⟨X * ∑ n ∈ Finset.Icc 1 ⌊X⌋₊, Λ n + X * Real.log X + (1 + Real.eulerMascheroniConstant) * X, by positivity, ?_⟩` and prove the remaining obligations.

Introduce `x hx1 hxX`. Take `⟨hS1, hS2⟩` from `Sz_bound hx1 hxX`. Establish `hl0 : 0 ≤ Real.log x` using `Real.log_nonneg hx1`. Establish `hl1 : Real.log x ≤ Real.log X` using `Real.log_le_log (by linarith) hxX`. Establish `hxl : x * Real.log x ≤ X * Real.log X` using `mul_le_mul hxX hl1 hl0 (by linarith)`.

Establish `hxl0 : 0 ≤ x * Real.log x` using `mul_nonneg (by linarith) hl0`. Establish `hg : (1 + Real.eulerMascheroniConstant) * x ≤ (1 + Real.eulerMascheroniConstant) * X` using `mul_le_mul_of_nonneg_left hxX (by linarith)`. Establish `hg0 : 0 ≤ (1 + Real.eulerMascheroniConstant) * x` using `mul_nonneg (by linarith) (by linarith)`. Unfold `Gz`. Rewrite using `[abs_le]`.

Apply the tactic sequence `constructor <;> nlinarith`.
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

/- English proof (translation)
Introduce `s₀ hs₀ θ hθ0 hθ1 hCex s hs`. Take `⟨C, x₀, hC⟩` from `hCex`. Take `⟨B, hB0, hB⟩` from `Gz_bdd (le_max_right x₀ 1)`. Apply the tactic sequence `have hs₀abs : |s₀| = 1 := by rcases hs₀ with h | h <;> simp [h]`. Apply the tactic sequence `have hε : (-s₀) * (-s₀) = 1 := by rcases hs₀ with h | h <;> simp [h]`.

Establish `hCC : C ≤ max C B` using `le_max_left _ _`. Establish `hBC : B ≤ max C B` using `le_max_right _ _`. Establish `hH : ∀ x : ℝ, 1 ≤ x → 0 ≤ HZ (-s₀) (max C B) θ x`. Introduce `x hx`. Establish `hxθ : 1 ≤ x ^ θ` using `Real.one_le_rpow hx hθ0.le`.

Unfold `HZ`. Break down `le_or_gt x (max x₀ 1) with hxX | hxX` into its components or cases. Establish `h1` using `hB x hx hxX`. Establish `h2 : s₀ * Gz x ≤ B`. Combine the equalities or inequalities in the displayed calculation.

Establish `h3 : B ≤ max C B * x ^ θ`. Use polynomial arithmetic with `[mul_nonneg (show 0 ≤ max C B by linarith) (show 0 ≤ x ^ θ - 1 by linarith)]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h1` using `hC x (le_of_lt (lt_of_le_of_lt (le_max_left _ _) hxX))`. Establish `h2 : C * x ^ θ ≤ max C B * x ^ θ` using `mul_le_mul_of_nonneg_right hCC (by linarith)`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hInt` using `landau_Z landauEq mellinSgen mellinElem zetaRealNonvanish hθ0 hθ1 hH`. Establish `hZ1` using `riemannZetaOne_ne_zero_of_integrable_mellin mellinDeriv mellinSgen mellinElem logDerivZeroFree hε hθ1 hH hInt s hs`. Distinguish the cases in `h1 : s = 1`. Substitute `h1` using the available equality.

Conclude with `riemannZeta_ne_zero_of_one_le_re (by simp)`. Rewrite `hZ1` using `[riemannZetaOne_eq_mul_of_ne_one h1]`. Conclude with `right_ne_zero_of_mul hZ1`.
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

/- English proof (translation)
Introduce `s₀ hs₀ θ hθ0 hθ1 hB s hs`. Choose the witnesses or unpack the hypotheses as in `⟨ε, hε0, hε1, hε2⟩ : ∃ ε : ℝ, 0 < ε ∧ θ + ε < s.re ∧ θ + ε < 1 := by`. Use `⟨min ((s.re - θ) / 2) ((1 - θ) / 2), lt_min (by linarith) (by linarith), ?_, ?_⟩` and prove the remaining obligations. Use `min_le_left ((s.re - θ) / 2) ((1 - θ) / 2)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.

Use `min_le_right ((s.re - θ) / 2) ((1 - θ) / 2)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `zetaLandau s₀ hs₀ (θ + ε) (by linarith) hε2 (hB ε hε0) s hε1`.
-/
theorem zetaLandauEps : ZetaLandauEps := by
  intro s₀ hs₀ θ hθ0 hθ1 hB s hs
  obtain ⟨ε, hε0, hε1, hε2⟩ : ∃ ε : ℝ, 0 < ε ∧ θ + ε < s.re ∧ θ + ε < 1 := by
    refine ⟨min ((s.re - θ) / 2) ((1 - θ) / 2), lt_min (by linarith) (by linarith), ?_, ?_⟩
    · have := min_le_left ((s.re - θ) / 2) ((1 - θ) / 2); linarith
    · have := min_le_right ((s.re - θ) / 2) ((1 - θ) / 2); linarith
  exact zetaLandau s₀ hs₀ (θ + ε) (by linarith) hε2 (hB ε hε0) s hε1

end Formalism
