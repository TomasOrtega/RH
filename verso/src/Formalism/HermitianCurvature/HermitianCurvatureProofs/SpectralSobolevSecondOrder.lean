import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSEJSliceCut

open MeasureTheory Filter Topology Set

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSE

/- English proof (translation)
Establish `hL : 0 < b - a` using `sub_pos.2 hab`. Establish `hφc : ContinuousOn φ (Icc a b)` using `fun t ht => (hd t ht).continuousAt.continuousWithinAt`. Establish `hi1 : IntegrableOn (fun y => ‖φ y‖ ^ 2) (Icc a b)` using `(hφc.norm.pow 2).integrableOn_compact isCompact_Icc`. Establish `hi2 : IntegrableOn (fun y => ‖φ' y‖ ^ 2) (Icc a b)` using `(hc.norm.pow 2).integrableOn_compact isCompact_Icc`. Establish `hi3 : IntegrableOn (fun y => ‖φ' y‖) (Icc a b)` using `hc.norm.integrableOn_compact isCompact_Icc`.

Establish `hconst : ∀ c : ℝ, IntegrableOn (fun _ : ℝ => c) (Icc a b)` using `fun c => continuousOn_const.integrableOn_compact isCompact_Icc`. Establish `hvol : volume.real (Icc a b) = b - a`. Rewrite using `[Measure.real, Real.volume_Icc, ENNReal.toReal_ofReal hL.le]`. Use `set P := ∫ y in Icc a b, ‖φ' y‖ with hP`. Use `set Q := ∫ y in Icc a b, ‖φ' y‖ ^ 2 with hQ`.

Use `set A := ∫ y in Icc a b, ‖φ y‖ ^ 2 with hA`. Establish `hQ0 : 0 ≤ Q` using `setIntegral_nonneg measurableSet_Icc fun y _ => sq_nonneg _`. Establish `hdiff : ∀ y ∈ Icc a b, ‖φ x - φ y‖ ≤ P`. Introduce `y hy`. Establish `hsub : uIcc y x ⊆ Icc a b` using `uIcc_subset_Icc hy hx`.

Establish `hftc : ∫ t in y..x, φ' t = φ x - φ y` using `intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t ht => hd t (hsub ht)) ((hc.mono hsub).intervalIntegrable)`. Rewrite using `[← hftc]`. Use `intervalIntegral.norm_integral_le_integral_norm_uIoc.trans ?_` and prove the remaining obligations. Conclude with `setIntegral_mono_set hi3 (Filter.Eventually.of_forall fun _ => norm_nonneg _) (Filter.Eventually.of_forall (uIoc_subset_uIcc.trans hsub))`. Establish `hpt : ∀ y ∈ Icc a b, ‖φ x‖ ^ 2 ≤ 2 * ‖φ y‖ ^ 2 + 2 * P ^ 2`.

Introduce `y hy`. Establish `h1 : ‖φ x‖ ≤ ‖φ y‖ + P`. Use `norm_sub_norm_le (φ x) (φ y)` as an intermediate fact. Combine the linear relations using `[hdiff y hy]`. Establish `h0 : 0 ≤ ‖φ x‖` using `norm_nonneg _`.

Use polynomial arithmetic with `[mul_self_le_mul_self h0 h1, sq_nonneg (‖φ y‖ - P)]`. Establish `hmono : ∫ _ in Icc a b, ‖φ x‖ ^ 2 ≤ ∫ y in Icc a b, (2 * ‖φ y‖ ^ 2 + 2 * P ^ 2)` using `setIntegral_mono_on (hconst _) ((hi1.const_mul 2).add (hconst _)) measurableSet_Icc hpt`. Rewrite `hmono` using `[setIntegral_const, hvol, smul_eq_mul, integral_add (hi1.const_mul 2) (hconst _), integral_const_mul, setIntegral_const, hvol, smul_eq_mul]`. Establish `hPQ : P ^ 2 ≤ (b - a) * Q`. Establish `hnn : 0 ≤ ∫ y in Icc a b, (‖φ' y‖ - P / (b - a)) ^ 2` using `setIntegral_nonneg measurableSet_Icc fun y _ => sq_nonneg _`.

Establish `hexp : ∫ y in Icc a b, (‖φ' y‖ - P / (b - a)) ^ 2 = Q - 2 * (P / (b - a)) * P + (b - a) * (P / (b - a)) ^ 2`. Establish `hfun : (fun y => (‖φ' y‖ - P / (b - a)) ^ 2) = fun y => ‖φ' y‖ ^ 2 - 2 * (P / (b - a)) * ‖φ' y‖ + (P / (b - a)) ^ 2`. Use function extensionality and compare the values at `y`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hfun, integral_add (f := fun y => ‖φ' y‖ ^ 2 - 2 * (P / (b - a)) * ‖φ' y‖) (g := fun _ => (P / (b - a)) ^ 2) (by exact hi2.sub (hi3.const_mul (2 * (P / (b - a))))) (hconst _), integral_sub (f := fun y => ‖φ' y‖ ^ 2) (g := fun y => 2 * (P / (b - a)) * ‖φ' y‖) hi2 (hi3.const_mul ( …`.

Rewrite `hnn` using `[hexp]`. Establish `hsimp : Q - 2 * (P / (b - a)) * P + (b - a) * (P / (b - a)) ^ 2 = Q - P ^ 2 / (b - a)`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Rewrite `hnn` using `[hsimp, sub_nonneg, div_le_iff₀ hL]`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `key : (b - a) * ‖φ x‖ ^ 2 ≤ 2 * A + (b - a) * (2 * ((b - a) * Q))`. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_left hPQ (by positivity : (0 : ℝ) ≤ 2 * (b - a))]`. Establish `hx2 : ‖φ x‖ ^ 2 ≤ (2 * A + (b - a) * (2 * ((b - a) * Q))) / (b - a)`. Rewrite using `[le_div_iff₀ hL]`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `he : (2 * A + (b - a) * (2 * ((b - a) * Q))) / (b - a) = 2 / (b - a) * A + 2 * (b - a) * Q`. Clear the denominators using the available nonvanishing facts. Rewrite `hx2` using `[he]`. Use polynomial arithmetic with `[mul_nonneg hL.le hQ0]`.
-/
theorem sob1 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] {a b : ℝ} (hab : a < b) {φ φ' : ℝ → E}
    (hd : ∀ x ∈ Icc a b, HasDerivAt φ (φ' x) x) (hc : ContinuousOn φ' (Icc a b))
    {x : ℝ} (hx : x ∈ Icc a b) :
    ‖φ x‖ ^ 2 ≤ 2 / (b - a) * (∫ y in Icc a b, ‖φ y‖ ^ 2) + 8 * (b - a) * ∫ y in Icc a b, ‖φ' y‖ ^ 2 := by
  have hL : 0 < b - a := sub_pos.2 hab
  have hφc : ContinuousOn φ (Icc a b) := fun t ht => (hd t ht).continuousAt.continuousWithinAt
  have hi1 : IntegrableOn (fun y => ‖φ y‖ ^ 2) (Icc a b) :=
    (hφc.norm.pow 2).integrableOn_compact isCompact_Icc
  have hi2 : IntegrableOn (fun y => ‖φ' y‖ ^ 2) (Icc a b) :=
    (hc.norm.pow 2).integrableOn_compact isCompact_Icc
  have hi3 : IntegrableOn (fun y => ‖φ' y‖) (Icc a b) := hc.norm.integrableOn_compact isCompact_Icc
  have hconst : ∀ c : ℝ, IntegrableOn (fun _ : ℝ => c) (Icc a b) := fun c =>
    continuousOn_const.integrableOn_compact isCompact_Icc
  have hvol : volume.real (Icc a b) = b - a := by
    rw [Measure.real, Real.volume_Icc, ENNReal.toReal_ofReal hL.le]
  set P := ∫ y in Icc a b, ‖φ' y‖ with hP
  set Q := ∫ y in Icc a b, ‖φ' y‖ ^ 2 with hQ
  set A := ∫ y in Icc a b, ‖φ y‖ ^ 2 with hA
  have hQ0 : 0 ≤ Q := setIntegral_nonneg measurableSet_Icc fun y _ => sq_nonneg _
  have hdiff : ∀ y ∈ Icc a b, ‖φ x - φ y‖ ≤ P := by
    intro y hy
    have hsub : uIcc y x ⊆ Icc a b := uIcc_subset_Icc hy hx
    have hftc : ∫ t in y..x, φ' t = φ x - φ y :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t ht => hd t (hsub ht))
        ((hc.mono hsub).intervalIntegrable)
    rw [← hftc]
    refine intervalIntegral.norm_integral_le_integral_norm_uIoc.trans ?_
    exact setIntegral_mono_set hi3 (Filter.Eventually.of_forall fun _ => norm_nonneg _)
      (Filter.Eventually.of_forall (uIoc_subset_uIcc.trans hsub))
  have hpt : ∀ y ∈ Icc a b, ‖φ x‖ ^ 2 ≤ 2 * ‖φ y‖ ^ 2 + 2 * P ^ 2 := by
    intro y hy
    have h1 : ‖φ x‖ ≤ ‖φ y‖ + P := by
      have := norm_sub_norm_le (φ x) (φ y)
      linarith [hdiff y hy]
    have h0 : 0 ≤ ‖φ x‖ := norm_nonneg _
    nlinarith [mul_self_le_mul_self h0 h1, sq_nonneg (‖φ y‖ - P)]
  have hmono : ∫ _ in Icc a b, ‖φ x‖ ^ 2 ≤ ∫ y in Icc a b, (2 * ‖φ y‖ ^ 2 + 2 * P ^ 2) :=
    setIntegral_mono_on (hconst _) ((hi1.const_mul 2).add (hconst _)) measurableSet_Icc hpt
  rw [setIntegral_const, hvol, smul_eq_mul, integral_add (hi1.const_mul 2) (hconst _),
    integral_const_mul, setIntegral_const, hvol, smul_eq_mul] at hmono
  have hPQ : P ^ 2 ≤ (b - a) * Q := by
    have hnn : 0 ≤ ∫ y in Icc a b, (‖φ' y‖ - P / (b - a)) ^ 2 :=
      setIntegral_nonneg measurableSet_Icc fun y _ => sq_nonneg _
    have hexp : ∫ y in Icc a b, (‖φ' y‖ - P / (b - a)) ^ 2 =
        Q - 2 * (P / (b - a)) * P + (b - a) * (P / (b - a)) ^ 2 := by
      have hfun : (fun y => (‖φ' y‖ - P / (b - a)) ^ 2) =
          fun y => ‖φ' y‖ ^ 2 - 2 * (P / (b - a)) * ‖φ' y‖ + (P / (b - a)) ^ 2 := by
        funext y
        ring
      rw [hfun, integral_add (f := fun y => ‖φ' y‖ ^ 2 - 2 * (P / (b - a)) * ‖φ' y‖)
        (g := fun _ => (P / (b - a)) ^ 2) (by exact hi2.sub (hi3.const_mul (2 * (P / (b - a))))) (hconst _),
        integral_sub (f := fun y => ‖φ' y‖ ^ 2) (g := fun y => 2 * (P / (b - a)) * ‖φ' y‖) hi2
          (hi3.const_mul (2 * (P / (b - a)))), integral_const_mul, setIntegral_const, hvol, smul_eq_mul]
    rw [hexp] at hnn
    have hsimp : Q - 2 * (P / (b - a)) * P + (b - a) * (P / (b - a)) ^ 2 = Q - P ^ 2 / (b - a) := by
      field_simp
      ring
    rw [hsimp, sub_nonneg, div_le_iff₀ hL] at hnn
    linarith
  have key : (b - a) * ‖φ x‖ ^ 2 ≤ 2 * A + (b - a) * (2 * ((b - a) * Q)) := by
    nlinarith [mul_le_mul_of_nonneg_left hPQ (by positivity : (0 : ℝ) ≤ 2 * (b - a))]
  have hx2 : ‖φ x‖ ^ 2 ≤ (2 * A + (b - a) * (2 * ((b - a) * Q))) / (b - a) := by
    rw [le_div_iff₀ hL]
    linarith
  have he : (2 * A + (b - a) * (2 * ((b - a) * Q))) / (b - a) = 2 / (b - a) * A + 2 * (b - a) * Q := by
    field_simp
  rw [he] at hx2
  nlinarith [mul_nonneg hL.le hQ0]

/- English proof (translation)
Set `ι : E →L[ℝ] UniformSpace.Completion E` to `UniformSpace.Completion.toComplL`. Establish `hd' : ∀ t ∈ Icc a b, HasDerivAt (fun s => ι (φ s)) (ι (φ' t)) t` using `fun t ht => ι.hasFDerivAt.comp_hasDerivAt t (hd t ht)`. Establish `hc' : ContinuousOn (fun s => ι (φ' s)) (Icc a b)` using `ι.continuous.comp_continuousOn hc`. Establish `h` using `sob1 hab hd' hc' hx`. Simplify `h` using `[ι, UniformSpace.Completion.norm_coe]`.
-/
theorem sob1' {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {a b : ℝ} (hab : a < b) {φ φ' : ℝ → E}
    (hd : ∀ x ∈ Icc a b, HasDerivAt φ (φ' x) x) (hc : ContinuousOn φ' (Icc a b))
    {x : ℝ} (hx : x ∈ Icc a b) :
    ‖φ x‖ ^ 2 ≤ 2 / (b - a) * (∫ y in Icc a b, ‖φ y‖ ^ 2) + 8 * (b - a) * ∫ y in Icc a b, ‖φ' y‖ ^ 2 := by
  let ι : E →L[ℝ] UniformSpace.Completion E := UniformSpace.Completion.toComplL
  have hd' : ∀ t ∈ Icc a b, HasDerivAt (fun s => ι (φ s)) (ι (φ' t)) t := fun t ht =>
    ι.hasFDerivAt.comp_hasDerivAt t (hd t ht)
  have hc' : ContinuousOn (fun s => ι (φ' s)) (Icc a b) := ι.continuous.comp_continuousOn hc
  have h := sob1 hab hd' hc' hx
  simpa [ι, UniformSpace.Completion.norm_coe] using h

/- English proof (translation)
Simplify using `using (((hasDerivAt_id v).ofReal_comp).mul_const Complex.I).const_add (x : ℂ)`.
-/
theorem path_hasDerivAt_im (x v : ℝ) :
    HasDerivAt (fun w : ℝ => (x : ℂ) + (w : ℂ) * Complex.I) Complex.I v := by
  simpa using (((hasDerivAt_id v).ofReal_comp).mul_const Complex.I).const_add (x : ℂ)

/- English proof (translation)
Simplify using `using ((hasDerivAt_id u).ofReal_comp).add_const ((v : ℂ) * Complex.I)`.
-/
theorem path_hasDerivAt_re (u v : ℝ) :
    HasDerivAt (fun w : ℝ => (w : ℂ) + (v : ℂ) * Complex.I) 1 u := by
  simpa using ((hasDerivAt_id u).ofReal_comp).add_const ((v : ℂ) * Complex.I)

/- English proof (translation)
Use `fun_prop`.
-/
theorem path_cont_re (v : ℝ) : Continuous (fun w : ℝ => (w : ℂ) + (v : ℂ) * Complex.I) := by
  fun_prop

/- English proof (translation)
Use `fun_prop`.
-/
theorem path_cont_im (x : ℝ) : Continuous (fun w : ℝ => (x : ℂ) + (w : ℂ) * Complex.I) := by
  fun_prop

/- English proof (translation)
Establish `hL : 0 < b - a` using `sub_pos.2 hab`. Establish `hφc : ContinuousOn φ (Icc a b)` using `fun t ht => (hd t ht).continuousAt.continuousWithinAt`. Establish `hi1 : IntegrableOn (fun y => ‖φ y‖ ^ 2) (Icc a b)` using `(hφc.norm.pow 2).integrableOn_compact isCompact_Icc`. Establish `hi2 : IntegrableOn (fun y => ‖φ' y‖ ^ 2) (Icc a b)` using `(hc.norm.pow 2).integrableOn_compact isCompact_Icc`. Establish `h1 : 0 ≤ ∫ y in Icc a b, ‖φ y‖ ^ 2` using `setIntegral_nonneg measurableSet_Icc fun _ _ => sq_nonneg _`.

Establish `h2 : 0 ≤ ∫ y in Icc a b, ‖φ' y‖ ^ 2` using `setIntegral_nonneg measurableSet_Icc fun _ _ => sq_nonneg _`. Use `(ENNReal.ofReal_le_ofReal (sob1' hab hd hc hx)).trans (le_of_eq ?_)` and prove the remaining obligations. Rewrite using `[ENNReal.ofReal_add (mul_nonneg (by positivity) h1) (mul_nonneg (by positivity) h2), ENNReal.ofReal_mul (show (0 : ℝ) ≤ 2 / (b - a) by positivity), ENNReal.ofReal_mul (show (0 : ℝ) ≤ 8 * (b - a) by positivity), ofReal_integral_eq_lintegral_ofReal hi1 (Filter.Eventually.of_forall …`.
-/
private theorem sq_norm_le_of_hasDerivAt_on_Icc {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {a b : ℝ} (hab : a < b)
    {φ φ' : ℝ → E} (hd : ∀ x ∈ Icc a b, HasDerivAt φ (φ' x) x) (hc : ContinuousOn φ' (Icc a b))
    {x : ℝ} (hx : x ∈ Icc a b) :
    ENNReal.ofReal (‖φ x‖ ^ 2) ≤
      ENNReal.ofReal (2 / (b - a)) * (∫⁻ y in Icc a b, ENNReal.ofReal (‖φ y‖ ^ 2)) +
        ENNReal.ofReal (8 * (b - a)) * ∫⁻ y in Icc a b, ENNReal.ofReal (‖φ' y‖ ^ 2) := by
  have hL : 0 < b - a := sub_pos.2 hab
  have hφc : ContinuousOn φ (Icc a b) := fun t ht => (hd t ht).continuousAt.continuousWithinAt
  have hi1 : IntegrableOn (fun y => ‖φ y‖ ^ 2) (Icc a b) :=
    (hφc.norm.pow 2).integrableOn_compact isCompact_Icc
  have hi2 : IntegrableOn (fun y => ‖φ' y‖ ^ 2) (Icc a b) :=
    (hc.norm.pow 2).integrableOn_compact isCompact_Icc
  have h1 : 0 ≤ ∫ y in Icc a b, ‖φ y‖ ^ 2 := setIntegral_nonneg measurableSet_Icc fun _ _ => sq_nonneg _
  have h2 : 0 ≤ ∫ y in Icc a b, ‖φ' y‖ ^ 2 := setIntegral_nonneg measurableSet_Icc fun _ _ => sq_nonneg _
  refine (ENNReal.ofReal_le_ofReal (sob1' hab hd hc hx)).trans (le_of_eq ?_)
  rw [ENNReal.ofReal_add (mul_nonneg (by positivity) h1) (mul_nonneg (by positivity) h2),
    ENNReal.ofReal_mul (show (0 : ℝ) ≤ 2 / (b - a) by positivity),
    ENNReal.ofReal_mul (show (0 : ℝ) ≤ 8 * (b - a) by positivity),
    ofReal_integral_eq_lintegral_ofReal hi1 (Filter.Eventually.of_forall fun _ => sq_nonneg _),
    ofReal_integral_eq_lintegral_ofReal hi2 (Filter.Eventually.of_forall fun _ => sq_nonneg _)]

/- English proof (translation)
Introduce `t0 δ hδ`. Use `⟨(2 / δ + 8 * δ) ^ 2, ?_⟩` and prove the remaining obligations. Introduce `E _ _ f fx fy fxy hf hfy hfxc hfxyc t ht`. Take `⟨x, y, rfl⟩ : ∃ x y : ℝ, t = (x : ℂ) + (y : ℂ) * Complex.I` from `⟨t.re, t.im, (Complex.re_add_im t).symm⟩`. Use `set D := Metric.closedBall t0 (2 * δ) with hD`.

Establish `hh0 : 0 < δ / 2` using `by positivity`. Establish `hfC : ContinuousOn f D` using `fun p hp => (hf p hp).continuousAt.continuousWithinAt`. Establish `hfyC : ContinuousOn fy D` using `fun p hp => by`. Take `⟨_, H⟩` from `hfy p hp`. Conclude with `H.continuousAt.continuousWithinAt`.

Use `set g : ℂ → ℝ := fun p => ‖f p‖ ^ 2 + ‖fx p‖ ^ 2 + ‖fy p‖ ^ 2 + ‖fxy p‖ ^ 2 with hg`. Establish `hg0 : ∀ p, 0 ≤ g p` using `fun p => by simp only [hg]; positivity`. Establish `hgC : ContinuousOn g D` using `(((hfC.norm.pow 2).add (hfxc.norm.pow 2)).add (hfyC.norm.pow 2)).add (hfxyc.norm.pow 2)`. Establish `hin : ∀ u ∈ Icc (x - δ / 2) (x + δ / 2), ∀ w ∈ Icc (y - δ / 2) (y + δ / 2), (u : ℂ) + (w : ℂ) * Complex.I ∈ D`. Introduce `u hu w hw`.

Rewrite using `[hD, Metric.mem_closedBall]`. Establish `hz : (u : ℂ) + (w : ℂ) * Complex.I - ((x : ℂ) + (y : ℂ) * Complex.I) = ((u - x : ℝ) : ℂ) + ((w - y : ℝ) : ℂ) * Complex.I`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hu' : |u - x| ≤ δ / 2` using `abs_le.2 ⟨by linarith [hu.1], by linarith [hu.2]⟩`.

Establish `hw' : |w - y| ≤ δ / 2` using `abs_le.2 ⟨by linarith [hw.1], by linarith [hw.2]⟩`. Establish `h1 : dist ((u : ℂ) + (w : ℂ) * Complex.I) ((x : ℂ) + (y : ℂ) * Complex.I) ≤ δ`. Rewrite using `[dist_eq_norm, hz]`. Use `(Complex.norm_le_abs_re_add_abs_im _).trans ?_` and prove the remaining obligations. Simplify using `only [Complex.add_re, Complex.ofReal_re, Complex.re_ofReal_mul, Complex.I_re, mul_zero, add_zero, Complex.add_im, Complex.ofReal_im, Complex.im_ofReal_mul, Complex.I_im, mul_one, zero_add]`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `h2 : dist ((x : ℂ) + (y : ℂ) * Complex.I) t0 < δ` using `ht`. Combine the linear relations using `[dist_triangle ((u : ℂ) + (w : ℂ) * Complex.I) ((x : ℂ) + (y : ℂ) * Complex.I) t0]`. Establish `hxA : x ∈ Icc (x - δ / 2) (x + δ / 2)` using `⟨by linarith, by linarith⟩`. Establish `hyB : y ∈ Icc (y - δ / 2) (y + δ / 2)` using `⟨by linarith, by linarith⟩`.

Establish `hab : ∀ c : ℝ, c - δ / 2 < c + δ / 2` using `fun c => by linarith`. Establish `hL : ∀ c : ℝ, c + δ / 2 - (c - δ / 2) = δ` using `fun c => by ring`. Establish `dIm : ∀ u w : ℝ, (u : ℂ) + (w : ℂ) * Complex.I ∈ D → HasDerivAt (fun s : ℝ => f ((u : ℂ) + (s : ℂ) * Complex.I)) (fy ((u : ℂ) + (w : ℂ) * Complex.I)) w`. Introduce `u w hp`. Use `(hf _ hp).comp_hasDerivAt w (path_hasDerivAt_im u w)` as an intermediate fact.

Simplify `this` using `[Function.comp_def]`. Establish `dRe : ∀ u w : ℝ, (u : ℂ) + (w : ℂ) * Complex.I ∈ D → HasDerivAt (fun s : ℝ => f ((s : ℂ) + (w : ℂ) * Complex.I)) (fx ((u : ℂ) + (w : ℂ) * Complex.I)) u`. Introduce `u w hp`. Use `(hf _ hp).comp_hasDerivAt u (path_hasDerivAt_re u w)` as an intermediate fact. Simplify `this` using `[Function.comp_def]`.

Establish `dReY : ∀ u w : ℝ, (u : ℂ) + (w : ℂ) * Complex.I ∈ D → HasDerivAt (fun s : ℝ => fy ((s : ℂ) + (w : ℂ) * Complex.I)) (fxy ((u : ℂ) + (w : ℂ) * Complex.I)) u`. Introduce `u w hp`. Take `⟨_, H⟩` from `hfy _ hp`. Use `H.comp_hasDerivAt u (path_hasDerivAt_re u w)` as an intermediate fact. Simplify `this` using `[Function.comp_def]`.

Establish `hCeq : ENNReal.ofReal (2 / δ) + ENNReal.ofReal (8 * δ) = ENNReal.ofReal (2 / δ + 8 * δ)` using `(ENNReal.ofReal_add (by positivity) (by positivity)).symm`. Establish `hC : ENNReal.ofReal (2 / δ + 8 * δ) ≠ ⊤` using `ENNReal.ofReal_ne_top`. Establish `step2f : ∀ w ∈ Icc (y - δ / 2) (y + δ / 2), ENNReal.ofReal (‖f ((x : ℂ) + (w : ℂ) * Complex.I)‖ ^ 2) ≤ ENNReal.ofReal (2 / δ + 8 * δ) * ∫⁻ u in Icc (x - δ / 2) (x + δ / 2), ENNReal.ofReal (g ((u : ℂ) + (w : ℂ) * Complex.I))`. Introduce `w hw`. Establish `hs` using `sq_norm_le_of_hasDerivAt_on_Icc (hab x) (φ := fun s : ℝ => f ((s : ℂ) + (w : ℂ) * Complex.I)) (φ' := fun s : ℝ => fx ((s : ℂ) + (w : ℂ) * Complex.I)) (fun u hu => dRe u w (hin u hu w hw)) (hfxc.comp (path_cont_re w).continuousOn fun u hu => hin u hu w hw) hxA`.

Rewrite `hs` using `[hL x]`. Use `hs.trans ?_` and prove the remaining obligations. Rewrite using `[← hCeq, add_mul]`. Use `add_le_add (mul_le_mul' le_rfl (lintegral_mono fun u => ENNReal.ofReal_le_ofReal ?_)) (mul_le_mul' le_rfl (lintegral_mono fun u => ENNReal.ofReal_le_ofReal ?_))` and prove the remaining obligations. Simplify using `only [hg]`.

Use polynomial arithmetic with `[sq_nonneg ‖fx ((u : ℂ) + (w : ℂ) * Complex.I)‖, sq_nonneg ‖fy ((u : ℂ) + (w : ℂ) * Complex.I)‖, sq_nonneg ‖fxy ((u : ℂ) + (w : ℂ) * Complex.I)‖]`. Simplify using `only [hg]`. Use polynomial arithmetic with `[sq_nonneg ‖f ((u : ℂ) + (w : ℂ) * Complex.I)‖, sq_nonneg ‖fy ((u : ℂ) + (w : ℂ) * Complex.I)‖, sq_nonneg ‖fxy ((u : ℂ) + (w : ℂ) * Complex.I)‖]`. Establish `step2fy : ∀ w ∈ Icc (y - δ / 2) (y + δ / 2), ENNReal.ofReal (‖fy ((x : ℂ) + (w : ℂ) * Complex.I)‖ ^ 2) ≤ ENNReal.ofReal (2 / δ + 8 * δ) * ∫⁻ u in Icc (x - δ / 2) (x + δ / 2), ENNReal.ofReal (g ((u : ℂ) + (w : ℂ) * Complex.I))`. Introduce `w hw`.

Establish `hs` using `sq_norm_le_of_hasDerivAt_on_Icc (hab x) (φ := fun s : ℝ => fy ((s : ℂ) + (w : ℂ) * Complex.I)) (φ' := fun s : ℝ => fxy ((s : ℂ) + (w : ℂ) * Complex.I)) (fun u hu => dReY u w (hin u hu w hw)) (hfxyc.comp (path_cont_re w).continuousOn fun u hu => hin u hu w hw) hxA`. Rewrite `hs` using `[hL x]`. Use `hs.trans ?_` and prove the remaining obligations. Rewrite using `[← hCeq, add_mul]`. Use `add_le_add (mul_le_mul' le_rfl (lintegral_mono fun u => ENNReal.ofReal_le_ofReal ?_)) (mul_le_mul' le_rfl (lintegral_mono fun u => ENNReal.ofReal_le_ofReal ?_))` and prove the remaining obligations.

Simplify using `only [hg]`. Use polynomial arithmetic with `[sq_nonneg ‖fx ((u : ℂ) + (w : ℂ) * Complex.I)‖, sq_nonneg ‖f ((u : ℂ) + (w : ℂ) * Complex.I)‖, sq_nonneg ‖fxy ((u : ℂ) + (w : ℂ) * Complex.I)‖]`. Simplify using `only [hg]`. Use polynomial arithmetic with `[sq_nonneg ‖f ((u : ℂ) + (w : ℂ) * Complex.I)‖, sq_nonneg ‖fy ((u : ℂ) + (w : ℂ) * Complex.I)‖, sq_nonneg ‖fx ((u : ℂ) + (w : ℂ) * Complex.I)‖]`. Establish `step1` using `sq_norm_le_of_hasDerivAt_on_Icc (hab y) (φ := fun s : ℝ => f ((x : ℂ) + (s : ℂ) * Complex.I)) (φ' := fun s : ℝ => fy ((x : ℂ) + (s : ℂ) * Complex.I)) (fun w hw => dIm x w (hin x hxA w hw)) (hfyC.comp (path_cont_im x).continuousOn fun w hw => hin x hxA w hw) hyB`.

Rewrite `step1` using `[hL y]`. Establish `hJ1` using `lintegral_mono_ae (μ := volume.restrict (Icc (y - δ / 2) (y + δ / 2))) ((ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall step2f))`. Establish `hJ2` using `lintegral_mono_ae (μ := volume.restrict (Icc (y - δ / 2) (y + δ / 2))) ((ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall step2fy))`. Rewrite `hJ1`, `hJ2` using `[lintegral_const_mul' _ _ hC]`. Use `set J := ∫⁻ w in Icc (y - δ / 2) (y + δ / 2), ∫⁻ u in Icc (x - δ / 2) (x + δ / 2), ENNReal.ofReal (g ((u : ℂ) + (w : ℂ) * Complex.I)) with hJ`.

Establish `hmain : ENNReal.ofReal (‖f ((x : ℂ) + (y : ℂ) * Complex.I)‖ ^ 2) ≤ ENNReal.ofReal (2 / δ + 8 * δ) * ENNReal.ofReal (2 / δ + 8 * δ) * J`. Use `step1.trans ?_` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← add_mul, hCeq, mul_assoc]`. Establish `hJD : J ≤ ∫⁻ z in D, ENNReal.ofReal (g z)`.

Establish `hpc : Continuous fun p : ℝ × ℝ => (p.1 : ℂ) + (p.2 : ℂ) * Complex.I` using `by fun_prop`. Establish `hGc : ContinuousOn (fun p : ℝ × ℝ => ENNReal.ofReal (g ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I))) (Icc (x - δ / 2) (x + δ / 2) ×ˢ Icc (y - δ / 2) (y + δ / 2))` using `ENNReal.continuous_ofReal.comp_continuousOn (hgC.comp hpc.continuousOn fun p hp => hin p.1 hp.1 p.2 hp.2)`. Establish `hmeas : AEMeasurable (fun p : ℝ × ℝ => ENNReal.ofReal (g ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I))) ((volume.restrict (Icc (x - δ / 2) (x + δ / 2))).prod (volume.restrict (Icc (y - δ / 2) (y + δ / 2))))`. Rewrite using `[Measure.prod_restrict]`. Conclude with `hGc.aemeasurable (measurableSet_Icc.prod measurableSet_Icc)`.

Establish `hfub : J = ∫⁻ p in Icc (x - δ / 2) (x + δ / 2) ×ˢ Icc (y - δ / 2) (y + δ / 2), ENNReal.ofReal (g ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I))`. Rewrite using `[Measure.volume_eq_prod, ← Measure.prod_restrict, lintegral_prod_symm _ hmeas]`. Establish `hmp` using `Complex.volume_preserving_equiv_real_prod.setLIntegral_comp_preimage_emb Complex.measurableEquivRealProd.measurableEmbedding (fun p : ℝ × ℝ => ENNReal.ofReal (g ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I))) (Icc (x - δ / 2) (x + δ / 2) ×ˢ Icc (y - δ / 2) (y + δ / 2))`. Simplify using `only [Complex.measurableEquivRealProd_apply, Complex.re_add_im] at hmp`. Rewrite using `[hfub, ← hmp]`.

Use `lintegral_mono_set fun z hz => ?_` and prove the remaining obligations. Establish `hz' : (z.re, z.im) ∈ Icc (x - δ / 2) (x + δ / 2) ×ˢ Icc (y - δ / 2) (y + δ / 2)`. Simplify `hz` using `[Complex.measurableEquivRealProd_apply]`. Use `hin z.re hz'.1 z.im hz'.2` as an intermediate fact. Rewrite `this` using `[Complex.re_add_im]`. Then use the resulting hypothesis.

Establish `hgi : IntegrableOn g D` using `hgC.integrableOn_compact (isCompact_closedBall _ _)`. Establish `hG : ∫⁻ z in D, ENNReal.ofReal (g z) = ENNReal.ofReal (∫ z in D, g z)` using `(ofReal_integral_eq_lintegral_ofReal hgi (Filter.Eventually.of_forall fun z => hg0 z)).symm`. Establish `hint_nn : 0 ≤ (2 / δ + 8 * δ) ^ 2 * ∫ z in D, g z` using `mul_nonneg (sq_nonneg _) (setIntegral_nonneg measurableSet_closedBall fun z _ => hg0 z)`. Establish `hfin : ENNReal.ofReal (‖f ((x : ℂ) + (y : ℂ) * Complex.I)‖ ^ 2) ≤ ENNReal.ofReal ((2 / δ + 8 * δ) ^ 2 * ∫ z in D, g z)`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[hG, ← ENNReal.ofReal_mul (show (0 : ℝ) ≤ 2 / δ + 8 * δ by positivity), ← ENNReal.ofReal_mul (show (0 : ℝ) ≤ (2 / δ + 8 * δ) * (2 / δ + 8 * δ) by positivity)]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Conclude with `(ENNReal.ofReal_le_ofReal_iff hint_nn).1 hfin`.
-/
theorem spectral_sobolev_second_order : JSSob2 := by
  intro t0 δ hδ
  refine ⟨(2 / δ + 8 * δ) ^ 2, ?_⟩
  intro E _ _ f fx fy fxy hf hfy hfxc hfxyc t ht
  obtain ⟨x, y, rfl⟩ : ∃ x y : ℝ, t = (x : ℂ) + (y : ℂ) * Complex.I :=
    ⟨t.re, t.im, (Complex.re_add_im t).symm⟩
  set D := Metric.closedBall t0 (2 * δ) with hD
  have hh0 : 0 < δ / 2 := by positivity
  have hfC : ContinuousOn f D := fun p hp => (hf p hp).continuousAt.continuousWithinAt
  have hfyC : ContinuousOn fy D := fun p hp => by
    obtain ⟨_, H⟩ := hfy p hp
    exact H.continuousAt.continuousWithinAt
  set g : ℂ → ℝ := fun p => ‖f p‖ ^ 2 + ‖fx p‖ ^ 2 + ‖fy p‖ ^ 2 + ‖fxy p‖ ^ 2 with hg
  have hg0 : ∀ p, 0 ≤ g p := fun p => by simp only [hg]; positivity
  have hgC : ContinuousOn g D :=
    (((hfC.norm.pow 2).add (hfxc.norm.pow 2)).add (hfyC.norm.pow 2)).add (hfxyc.norm.pow 2)
  have hin : ∀ u ∈ Icc (x - δ / 2) (x + δ / 2), ∀ w ∈ Icc (y - δ / 2) (y + δ / 2),
      (u : ℂ) + (w : ℂ) * Complex.I ∈ D := by
    intro u hu w hw
    rw [hD, Metric.mem_closedBall]
    have hz : (u : ℂ) + (w : ℂ) * Complex.I - ((x : ℂ) + (y : ℂ) * Complex.I) =
        ((u - x : ℝ) : ℂ) + ((w - y : ℝ) : ℂ) * Complex.I := by
      push_cast
      ring
    have hu' : |u - x| ≤ δ / 2 := abs_le.2 ⟨by linarith [hu.1], by linarith [hu.2]⟩
    have hw' : |w - y| ≤ δ / 2 := abs_le.2 ⟨by linarith [hw.1], by linarith [hw.2]⟩
    have h1 : dist ((u : ℂ) + (w : ℂ) * Complex.I) ((x : ℂ) + (y : ℂ) * Complex.I) ≤ δ := by
      rw [dist_eq_norm, hz]
      refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
      simp only [Complex.add_re, Complex.ofReal_re, Complex.re_ofReal_mul, Complex.I_re, mul_zero,
        add_zero, Complex.add_im, Complex.ofReal_im, Complex.im_ofReal_mul, Complex.I_im, mul_one,
        zero_add]
      linarith
    have h2 : dist ((x : ℂ) + (y : ℂ) * Complex.I) t0 < δ := ht
    linarith [dist_triangle ((u : ℂ) + (w : ℂ) * Complex.I) ((x : ℂ) + (y : ℂ) * Complex.I) t0]
  have hxA : x ∈ Icc (x - δ / 2) (x + δ / 2) := ⟨by linarith, by linarith⟩
  have hyB : y ∈ Icc (y - δ / 2) (y + δ / 2) := ⟨by linarith, by linarith⟩
  have hab : ∀ c : ℝ, c - δ / 2 < c + δ / 2 := fun c => by linarith
  have hL : ∀ c : ℝ, c + δ / 2 - (c - δ / 2) = δ := fun c => by ring
  have dIm : ∀ u w : ℝ, (u : ℂ) + (w : ℂ) * Complex.I ∈ D →
      HasDerivAt (fun s : ℝ => f ((u : ℂ) + (s : ℂ) * Complex.I)) (fy ((u : ℂ) + (w : ℂ) * Complex.I)) w := by
    intro u w hp
    have := (hf _ hp).comp_hasDerivAt w (path_hasDerivAt_im u w)
    simpa [Function.comp_def] using this
  have dRe : ∀ u w : ℝ, (u : ℂ) + (w : ℂ) * Complex.I ∈ D →
      HasDerivAt (fun s : ℝ => f ((s : ℂ) + (w : ℂ) * Complex.I)) (fx ((u : ℂ) + (w : ℂ) * Complex.I)) u := by
    intro u w hp
    have := (hf _ hp).comp_hasDerivAt u (path_hasDerivAt_re u w)
    simpa [Function.comp_def] using this
  have dReY : ∀ u w : ℝ, (u : ℂ) + (w : ℂ) * Complex.I ∈ D →
      HasDerivAt (fun s : ℝ => fy ((s : ℂ) + (w : ℂ) * Complex.I)) (fxy ((u : ℂ) + (w : ℂ) * Complex.I)) u := by
    intro u w hp
    obtain ⟨_, H⟩ := hfy _ hp
    have := H.comp_hasDerivAt u (path_hasDerivAt_re u w)
    simpa [Function.comp_def] using this
  have hCeq : ENNReal.ofReal (2 / δ) + ENNReal.ofReal (8 * δ) = ENNReal.ofReal (2 / δ + 8 * δ) :=
    (ENNReal.ofReal_add (by positivity) (by positivity)).symm
  have hC : ENNReal.ofReal (2 / δ + 8 * δ) ≠ ⊤ := ENNReal.ofReal_ne_top
  have step2f : ∀ w ∈ Icc (y - δ / 2) (y + δ / 2),
      ENNReal.ofReal (‖f ((x : ℂ) + (w : ℂ) * Complex.I)‖ ^ 2) ≤
        ENNReal.ofReal (2 / δ + 8 * δ) *
          ∫⁻ u in Icc (x - δ / 2) (x + δ / 2), ENNReal.ofReal (g ((u : ℂ) + (w : ℂ) * Complex.I)) := by
    intro w hw
    have hs := sq_norm_le_of_hasDerivAt_on_Icc (hab x) (φ := fun s : ℝ => f ((s : ℂ) + (w : ℂ) * Complex.I))
      (φ' := fun s : ℝ => fx ((s : ℂ) + (w : ℂ) * Complex.I))
      (fun u hu => dRe u w (hin u hu w hw))
      (hfxc.comp (path_cont_re w).continuousOn fun u hu => hin u hu w hw) hxA
    rw [hL x] at hs
    refine hs.trans ?_
    rw [← hCeq, add_mul]
    refine add_le_add (mul_le_mul' le_rfl (lintegral_mono fun u => ENNReal.ofReal_le_ofReal ?_))
      (mul_le_mul' le_rfl (lintegral_mono fun u => ENNReal.ofReal_le_ofReal ?_))
    · simp only [hg]
      nlinarith [sq_nonneg ‖fx ((u : ℂ) + (w : ℂ) * Complex.I)‖, sq_nonneg ‖fy ((u : ℂ) + (w : ℂ) * Complex.I)‖,
        sq_nonneg ‖fxy ((u : ℂ) + (w : ℂ) * Complex.I)‖]
    · simp only [hg]
      nlinarith [sq_nonneg ‖f ((u : ℂ) + (w : ℂ) * Complex.I)‖, sq_nonneg ‖fy ((u : ℂ) + (w : ℂ) * Complex.I)‖,
        sq_nonneg ‖fxy ((u : ℂ) + (w : ℂ) * Complex.I)‖]
  have step2fy : ∀ w ∈ Icc (y - δ / 2) (y + δ / 2),
      ENNReal.ofReal (‖fy ((x : ℂ) + (w : ℂ) * Complex.I)‖ ^ 2) ≤
        ENNReal.ofReal (2 / δ + 8 * δ) *
          ∫⁻ u in Icc (x - δ / 2) (x + δ / 2), ENNReal.ofReal (g ((u : ℂ) + (w : ℂ) * Complex.I)) := by
    intro w hw
    have hs := sq_norm_le_of_hasDerivAt_on_Icc (hab x) (φ := fun s : ℝ => fy ((s : ℂ) + (w : ℂ) * Complex.I))
      (φ' := fun s : ℝ => fxy ((s : ℂ) + (w : ℂ) * Complex.I))
      (fun u hu => dReY u w (hin u hu w hw))
      (hfxyc.comp (path_cont_re w).continuousOn fun u hu => hin u hu w hw) hxA
    rw [hL x] at hs
    refine hs.trans ?_
    rw [← hCeq, add_mul]
    refine add_le_add (mul_le_mul' le_rfl (lintegral_mono fun u => ENNReal.ofReal_le_ofReal ?_))
      (mul_le_mul' le_rfl (lintegral_mono fun u => ENNReal.ofReal_le_ofReal ?_))
    · simp only [hg]
      nlinarith [sq_nonneg ‖fx ((u : ℂ) + (w : ℂ) * Complex.I)‖, sq_nonneg ‖f ((u : ℂ) + (w : ℂ) * Complex.I)‖,
        sq_nonneg ‖fxy ((u : ℂ) + (w : ℂ) * Complex.I)‖]
    · simp only [hg]
      nlinarith [sq_nonneg ‖f ((u : ℂ) + (w : ℂ) * Complex.I)‖, sq_nonneg ‖fy ((u : ℂ) + (w : ℂ) * Complex.I)‖,
        sq_nonneg ‖fx ((u : ℂ) + (w : ℂ) * Complex.I)‖]
  have step1 := sq_norm_le_of_hasDerivAt_on_Icc (hab y) (φ := fun s : ℝ => f ((x : ℂ) + (s : ℂ) * Complex.I))
    (φ' := fun s : ℝ => fy ((x : ℂ) + (s : ℂ) * Complex.I))
    (fun w hw => dIm x w (hin x hxA w hw))
    (hfyC.comp (path_cont_im x).continuousOn fun w hw => hin x hxA w hw) hyB
  rw [hL y] at step1
  have hJ1 := lintegral_mono_ae (μ := volume.restrict (Icc (y - δ / 2) (y + δ / 2)))
    ((ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall step2f))
  have hJ2 := lintegral_mono_ae (μ := volume.restrict (Icc (y - δ / 2) (y + δ / 2)))
    ((ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall step2fy))
  rw [lintegral_const_mul' _ _ hC] at hJ1 hJ2
  set J := ∫⁻ w in Icc (y - δ / 2) (y + δ / 2),
    ∫⁻ u in Icc (x - δ / 2) (x + δ / 2), ENNReal.ofReal (g ((u : ℂ) + (w : ℂ) * Complex.I)) with hJ
  have hmain : ENNReal.ofReal (‖f ((x : ℂ) + (y : ℂ) * Complex.I)‖ ^ 2) ≤
      ENNReal.ofReal (2 / δ + 8 * δ) * ENNReal.ofReal (2 / δ + 8 * δ) * J := by
    refine step1.trans ?_
    calc _ ≤ ENNReal.ofReal (2 / δ) * (ENNReal.ofReal (2 / δ + 8 * δ) * J) +
          ENNReal.ofReal (8 * δ) * (ENNReal.ofReal (2 / δ + 8 * δ) * J) :=
          add_le_add (mul_le_mul' le_rfl hJ1) (mul_le_mul' le_rfl hJ2)
      _ = ENNReal.ofReal (2 / δ + 8 * δ) * ENNReal.ofReal (2 / δ + 8 * δ) * J := by
          rw [← add_mul, hCeq, mul_assoc]
  have hJD : J ≤ ∫⁻ z in D, ENNReal.ofReal (g z) := by
    have hpc : Continuous fun p : ℝ × ℝ => (p.1 : ℂ) + (p.2 : ℂ) * Complex.I := by fun_prop
    have hGc : ContinuousOn (fun p : ℝ × ℝ => ENNReal.ofReal (g ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I)))
        (Icc (x - δ / 2) (x + δ / 2) ×ˢ Icc (y - δ / 2) (y + δ / 2)) :=
      ENNReal.continuous_ofReal.comp_continuousOn
        (hgC.comp hpc.continuousOn fun p hp => hin p.1 hp.1 p.2 hp.2)
    have hmeas : AEMeasurable (fun p : ℝ × ℝ => ENNReal.ofReal (g ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I)))
        ((volume.restrict (Icc (x - δ / 2) (x + δ / 2))).prod (volume.restrict (Icc (y - δ / 2) (y + δ / 2)))) := by
      rw [Measure.prod_restrict]
      exact hGc.aemeasurable (measurableSet_Icc.prod measurableSet_Icc)
    have hfub : J = ∫⁻ p in Icc (x - δ / 2) (x + δ / 2) ×ˢ Icc (y - δ / 2) (y + δ / 2),
        ENNReal.ofReal (g ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I)) := by
      rw [Measure.volume_eq_prod, ← Measure.prod_restrict, lintegral_prod_symm _ hmeas]
    have hmp := Complex.volume_preserving_equiv_real_prod.setLIntegral_comp_preimage_emb
      Complex.measurableEquivRealProd.measurableEmbedding
      (fun p : ℝ × ℝ => ENNReal.ofReal (g ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I)))
      (Icc (x - δ / 2) (x + δ / 2) ×ˢ Icc (y - δ / 2) (y + δ / 2))
    simp only [Complex.measurableEquivRealProd_apply, Complex.re_add_im] at hmp
    rw [hfub, ← hmp]
    refine lintegral_mono_set fun z hz => ?_
    have hz' : (z.re, z.im) ∈ Icc (x - δ / 2) (x + δ / 2) ×ˢ Icc (y - δ / 2) (y + δ / 2) := by
      simpa [Complex.measurableEquivRealProd_apply] using hz
    have := hin z.re hz'.1 z.im hz'.2
    rwa [Complex.re_add_im] at this
  have hgi : IntegrableOn g D := hgC.integrableOn_compact (isCompact_closedBall _ _)
  have hG : ∫⁻ z in D, ENNReal.ofReal (g z) = ENNReal.ofReal (∫ z in D, g z) :=
    (ofReal_integral_eq_lintegral_ofReal hgi (Filter.Eventually.of_forall fun z => hg0 z)).symm
  have hint_nn : 0 ≤ (2 / δ + 8 * δ) ^ 2 * ∫ z in D, g z :=
    mul_nonneg (sq_nonneg _) (setIntegral_nonneg measurableSet_closedBall fun z _ => hg0 z)
  have hfin : ENNReal.ofReal (‖f ((x : ℂ) + (y : ℂ) * Complex.I)‖ ^ 2) ≤
      ENNReal.ofReal ((2 / δ + 8 * δ) ^ 2 * ∫ z in D, g z) := by
    calc _ ≤ ENNReal.ofReal (2 / δ + 8 * δ) * ENNReal.ofReal (2 / δ + 8 * δ) * J := hmain
      _ ≤ ENNReal.ofReal (2 / δ + 8 * δ) * ENNReal.ofReal (2 / δ + 8 * δ) *
          ∫⁻ z in D, ENNReal.ofReal (g z) := mul_le_mul' le_rfl hJD
      _ = _ := by
        rw [hG, ← ENNReal.ofReal_mul (show (0 : ℝ) ≤ 2 / δ + 8 * δ by positivity),
          ← ENNReal.ofReal_mul (show (0 : ℝ) ≤ (2 / δ + 8 * δ) * (2 / δ + 8 * δ) by positivity)]
        congr 1
        ring
  exact (ENNReal.ofReal_le_ofReal_iff hint_nn).1 hfin

end Formalism.FourierDecayAlt.P.CutSE
