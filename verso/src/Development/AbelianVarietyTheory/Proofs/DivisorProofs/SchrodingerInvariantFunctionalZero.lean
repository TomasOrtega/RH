import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPairingStdP
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeShiftedCutoffSummable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModulatedSchwartzSeminormPolynomial
open scoped SchwartzMap
open MeasureTheory

noncomputable section

namespace GlobalTheory.SchrIrred

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

/- English proof (translation)
Use `set D : ℕ → ℝ := fun j => (n.choose j : ℝ) * ((2 ^ (k + N) * (Finset.Iic (k + N, j)).sup (fun m => SchwartzMap.seminorm ℂ m.1 m.2) h) * (2 ^ N * (Finset.Iic (N, n - j)).sup (fun m => SchwartzMap.seminorm ℂ m.1 m.2) f)) with hD`. Establish `hD0 : ∀ j, 0 ≤ D j` using `fun j => by`. Establish `h1 : 0 ≤ (Finset.Iic (k + N, j)).sup (fun m => SchwartzMap.seminorm ℂ m.1 m.2) h` using `apply_nonneg _ _`. Establish `h2 : 0 ≤ (Finset.Iic (N, n - j)).sup (fun m => SchwartzMap.seminorm ℂ m.1 m.2) f` using `apply_nonneg _ _`. Check the signs of the components of the expression.

Use `set C := ∑ j ∈ Finset.range (n + 1), D j with hC`. Establish `hC0 : 0 ≤ C` using `Finset.sum_nonneg fun j _ => hD0 j`. Use `⟨C, fun l u hu => ?_⟩` and prove the remaining obligations. Use `SchwartzMap.seminorm_le_bound ℂ k n u (by positivity) fun x => ?_` and prove the remaining obligations. Establish `hul : (u : V → ℂ) = fun y => h y * f (y - l)` using `funext hu`.

Rewrite using `[hul]`. Establish `hg : ContDiff ℝ n (fun y : V => f (y - l))` using `(f.smooth n).comp (contDiff_id.sub contDiff_const)`. Establish `hL` using `norm_iteratedFDeriv_mul_le (𝕜 := ℝ) (h.smooth n) hg x (n := n) le_rfl`. Rewrite `hL` using `[iteratedFDeriv_comp_sub]`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => by ring`. Use `_ ≤ ∑ j ∈ Finset.range (n + 1), D j * ((1 + ‖l‖)⁻¹) ^ N := by`. Use `Finset.sum_le_sum fun j _ => ?_` and prove the remaining obligations. Use `(mul_le_mul_of_nonneg_left (GlobalTheory.LatticeSchwartz.term_le h f k N j (n - j) x l) (Nat.cast_nonneg _)).trans (le_of_eq ?_)` and prove the remaining obligations. Rewrite using `[hD]`.

Expand and normalize the polynomial expressions, which then agree. Use `_ = C * ((1 + ‖l‖)⁻¹) ^ N := by rw [hC, Finset.sum_mul]`.
-/
theorem seminorm_mul_comp_sub_le (h f : 𝓢(V, ℂ)) (k n N : ℕ) : ∃ C : ℝ, ∀ (l : V) (u : 𝓢(V, ℂ)),
    (∀ x, u x = h x * f (x - l)) → SchwartzMap.seminorm ℂ k n u ≤ C * ((1 + ‖l‖)⁻¹) ^ N := by
  set D : ℕ → ℝ := fun j => (n.choose j : ℝ) *
      ((2 ^ (k + N) * (Finset.Iic (k + N, j)).sup (fun m => SchwartzMap.seminorm ℂ m.1 m.2) h) *
      (2 ^ N * (Finset.Iic (N, n - j)).sup (fun m => SchwartzMap.seminorm ℂ m.1 m.2) f)) with hD
  have hD0 : ∀ j, 0 ≤ D j := fun j => by
    have h1 : 0 ≤ (Finset.Iic (k + N, j)).sup (fun m => SchwartzMap.seminorm ℂ m.1 m.2) h := apply_nonneg _ _
    have h2 : 0 ≤ (Finset.Iic (N, n - j)).sup (fun m => SchwartzMap.seminorm ℂ m.1 m.2) f := apply_nonneg _ _
    positivity
  set C := ∑ j ∈ Finset.range (n + 1), D j with hC
  have hC0 : 0 ≤ C := Finset.sum_nonneg fun j _ => hD0 j
  refine ⟨C, fun l u hu => ?_⟩
  refine SchwartzMap.seminorm_le_bound ℂ k n u (by positivity) fun x => ?_
  have hul : (u : V → ℂ) = fun y => h y * f (y - l) := funext hu
  rw [hul]
  have hg : ContDiff ℝ n (fun y : V => f (y - l)) :=
    (f.smooth n).comp (contDiff_id.sub contDiff_const)
  have hL := norm_iteratedFDeriv_mul_le (𝕜 := ℝ) (h.smooth n) hg x (n := n) le_rfl
  simp_rw [iteratedFDeriv_comp_sub] at hL
  calc ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (fun y => h y * f (y - l)) x‖
      ≤ ‖x‖ ^ k * ∑ j ∈ Finset.range (n + 1),
          (n.choose j : ℝ) * ‖iteratedFDeriv ℝ j h x‖ * ‖iteratedFDeriv ℝ (n - j) f (x - l)‖ := by
        gcongr
    _ = ∑ j ∈ Finset.range (n + 1), (n.choose j : ℝ) *
          (‖x‖ ^ k * ‖iteratedFDeriv ℝ j h x‖ * ‖iteratedFDeriv ℝ (n - j) f (x - l)‖) := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => by ring
    _ ≤ ∑ j ∈ Finset.range (n + 1), D j * ((1 + ‖l‖)⁻¹) ^ N := by
        refine Finset.sum_le_sum fun j _ => ?_
        refine (mul_le_mul_of_nonneg_left (GlobalTheory.LatticeSchwartz.term_le h f k N j (n - j) x l)
          (Nat.cast_nonneg _)).trans (le_of_eq ?_)
        rw [hD]; ring
    _ = C * ((1 + ‖l‖)⁻¹) ^ N := by rw [hC, Finset.sum_mul]

/- English proof (translation)
Use `borelize V`. Set `μ : Measure V` to `Measure.addHaar`. Set `gc : 𝓢(V, ℂ)` to `SchwartzMap.postcompCLM (𝕜 := ℝ) (Complex.conjCLE : ℂ →L[ℝ] ℂ) g`. Establish `hgc : ∀ x, gc x = (starRingEnd ℂ) (g x)` using `fun x => rfl`. Set `G : 𝓢(V, ℂ)` to `SchwartzMap.smulLeftCLM ℂ (⇑g) gc`.

Establish `hG : ∀ x, G x = g x * gc x` using `fun x => by`. Simplify using `only [G, SchwartzMap.smulLeftCLM_apply_apply g.hasTemperateGrowth, smul_eq_mul]`. Establish `hG' : ∀ x, G x = ((‖g x‖ ^ 2 : ℝ) : ℂ)` using `fun x => by`. Rewrite using `[hG, hgc, Complex.mul_conj, Complex.normSq_eq_norm_sq]`. Establish `hc : ∫ x, G x ∂μ ≠ 0`.

Repeatedly rewrite using `[hG']`. Rewrite using `[integral_complex_ofReal, Complex.ofReal_ne_zero]`. Choose the witnesses or unpack the hypotheses as in `⟨x₀, hx₀⟩ : ∃ x, g x ≠ 0 := by`. Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`.

Conclude with `hg (SchwartzMap.ext hcon)`. Establish `hint : Integrable (fun x => ‖g x‖ ^ 2) μ`. Use `(G.integrable (μ := μ)).norm.congr (ae_of_all _ fun x => ?_)` and prove the remaining obligations. Simplify using `only [hG', Complex.norm_real, Real.norm_eq_abs]`. Conclude with `abs_of_nonneg (by positivity)`.

Conclude with `(integral_pos_of_integrable_nonneg_nonzero (x := x₀) (g.continuous.norm.pow 2) hint (fun x => sq_nonneg _) (by simpa using hx₀)).ne'`. Use extensionality with `f`. Set `F : V → 𝓢(V, ℂ)` to `fun a => SchwartzMap.smulLeftCLM ℂ (⇑f) (SchwartzMap.compSubConstCLM ℂ a G)`. Establish `hF : ∀ a x, F a x = f x * G (x - a)` using `fun a x => by`. Simplify using `only [F, SchwartzMap.smulLeftCLM_apply_apply f.hasTemperateGrowth, smul_eq_mul, SchwartzMap.compSubConstCLM_apply]`.

Take `⟨u, hu, hL⟩` from `GlobalTheory.SchwartzPettis.exists_integral (μ := μ) F (fun y => by`. Repeatedly rewrite using `[hF]`. Conclude with `(continuous_const.mul (G.continuous.comp (continuous_const.sub continuous_id))).aestronglyMeasurable)`. Use the proof step `(fun k n => by`. Take `⟨C, hC⟩` from `seminorm_mul_comp_sub_le f G k n (Module.finrank ℝ V + 1)`.

Use `⟨_, ?_, fun a => hC a (F a) (hF a)⟩` and prove the remaining obligations. Use `((integrable_one_add_norm (E := V) (μ := μ) (r := ((Module.finrank ℝ V + 1 : ℕ) : ℝ)) (by push_cast; linarith)).const_mul C).congr (ae_of_all _ fun a => ?_)` and prove the remaining obligations. Simplify using `only`. Rewrite using `[Real.rpow_neg (by positivity), Real.rpow_natCast, inv_pow])`. Establish `h0 : T u = 0`.

Rewrite using `[(hL T).2]`. Use `integral_eq_zero_of_ae (ae_of_all _ fun a => ?_)` and prove the remaining obligations. Use `hT a (SchwartzMap.smulLeftCLM ℂ (⇑f) (SchwartzMap.compSubConstCLM ℂ a gc)) (F a) fun x => ?_` and prove the remaining obligations. Simplify using `only [hF, hG, SchwartzMap.smulLeftCLM_apply_apply f.hasTemperateGrowth, smul_eq_mul, SchwartzMap.compSubConstCLM_apply]`. Expand and normalize the polynomial expressions, which then agree.

Establish `h1 : u = (∫ x, G x ∂μ) • f`. Use extensionality with `y`. Rewrite using `[hu, SchwartzMap.smul_apply, smul_eq_mul]`. Repeatedly rewrite using `[hF]`. Rewrite using `[integral_const_mul, integral_sub_left_eq_self (fun x => G x) μ y, mul_comm]`.

Rewrite `h0` using `[h1, map_smul, smul_eq_mul]`. Simplify using `using (mul_eq_zero.1 h0).resolve_left hc`.
-/
theorem eq_zero_of_mul_translates [FiniteDimensional ℝ V] (T : 𝓢(V, ℂ) →L[ℂ] ℂ) (g : 𝓢(V, ℂ)) (hg : g ≠ 0)
    (hT : ∀ (a : V) (ψ h : 𝓢(V, ℂ)), (∀ x, h x = g (x - a) * ψ x) → T h = 0) : T = 0 := by
  borelize V
  let μ : Measure V := Measure.addHaar
  let gc : 𝓢(V, ℂ) := SchwartzMap.postcompCLM (𝕜 := ℝ) (Complex.conjCLE : ℂ →L[ℝ] ℂ) g
  have hgc : ∀ x, gc x = (starRingEnd ℂ) (g x) := fun x => rfl
  let G : 𝓢(V, ℂ) := SchwartzMap.smulLeftCLM ℂ (⇑g) gc
  have hG : ∀ x, G x = g x * gc x := fun x => by
    simp only [G, SchwartzMap.smulLeftCLM_apply_apply g.hasTemperateGrowth, smul_eq_mul]
  have hG' : ∀ x, G x = ((‖g x‖ ^ 2 : ℝ) : ℂ) := fun x => by
    rw [hG, hgc, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hc : ∫ x, G x ∂μ ≠ 0 := by
    simp_rw [hG']
    rw [integral_complex_ofReal, Complex.ofReal_ne_zero]
    obtain ⟨x₀, hx₀⟩ : ∃ x, g x ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      exact hg (SchwartzMap.ext hcon)
    have hint : Integrable (fun x => ‖g x‖ ^ 2) μ := by
      refine (G.integrable (μ := μ)).norm.congr (ae_of_all _ fun x => ?_)
      simp only [hG', Complex.norm_real, Real.norm_eq_abs]
      exact abs_of_nonneg (by positivity)
    exact (integral_pos_of_integrable_nonneg_nonzero (x := x₀) (g.continuous.norm.pow 2) hint
      (fun x => sq_nonneg _) (by simpa using hx₀)).ne'
  ext f
  let F : V → 𝓢(V, ℂ) := fun a => SchwartzMap.smulLeftCLM ℂ (⇑f) (SchwartzMap.compSubConstCLM ℂ a G)
  have hF : ∀ a x, F a x = f x * G (x - a) := fun a x => by
    simp only [F, SchwartzMap.smulLeftCLM_apply_apply f.hasTemperateGrowth, smul_eq_mul,
      SchwartzMap.compSubConstCLM_apply]
  obtain ⟨u, hu, hL⟩ := GlobalTheory.SchwartzPettis.exists_integral (μ := μ) F
    (fun y => by
      simp_rw [hF]
      exact (continuous_const.mul (G.continuous.comp (continuous_const.sub continuous_id))).aestronglyMeasurable)
    (fun k n => by
      obtain ⟨C, hC⟩ := seminorm_mul_comp_sub_le f G k n (Module.finrank ℝ V + 1)
      refine ⟨_, ?_, fun a => hC a (F a) (hF a)⟩
      refine ((integrable_one_add_norm (E := V) (μ := μ) (r := ((Module.finrank ℝ V + 1 : ℕ) : ℝ))
        (by push_cast; linarith)).const_mul C).congr (ae_of_all _ fun a => ?_)
      simp only
      rw [Real.rpow_neg (by positivity), Real.rpow_natCast, inv_pow])
  have h0 : T u = 0 := by
    rw [(hL T).2]
    refine integral_eq_zero_of_ae (ae_of_all _ fun a => ?_)
    refine hT a (SchwartzMap.smulLeftCLM ℂ (⇑f) (SchwartzMap.compSubConstCLM ℂ a gc)) (F a) fun x => ?_
    simp only [hF, hG, SchwartzMap.smulLeftCLM_apply_apply f.hasTemperateGrowth, smul_eq_mul,
      SchwartzMap.compSubConstCLM_apply]
    ring
  have h1 : u = (∫ x, G x ∂μ) • f := by
    ext y
    rw [hu, SchwartzMap.smul_apply, smul_eq_mul]
    simp_rw [hF]
    rw [integral_const_mul, integral_sub_left_eq_self (fun x => G x) μ y, mul_comm]
  rw [h1, map_smul, smul_eq_mul] at h0
  simpa using (mul_eq_zero.1 h0).resolve_left hc

/- English proof (translation)
Set `A : V ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ V))` to `toEuclidean`. Set `ψ'` to `SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A.symm ψ`. Set `φ : 𝓢(EuclideanSpace ℝ (Fin (Module.finrank ℝ V)), ℂ)` to `FourierTransform.fourier ψ'`. Set `L : EuclideanSpace ℝ (Fin (Module.finrank ℝ V)) → V →L[ℝ] ℝ` to `fun ξ => (innerSL ℝ ξ).comp A.toContinuousLinearMap`. Establish `hL : ∀ ξ x, L ξ x = inner ℝ ξ (A x)` using `fun ξ x => rfl`.

Set `e : EuclideanSpace ℝ (Fin (Module.finrank ℝ V)) → V → ℂ` to `fun ξ x => Complex.exp ((Complex.I * (2 * Real.pi : ℝ)) * (L ξ x : ℂ))`. Establish `he : ∀ ξ, (e ξ).HasTemperateGrowth` using `fun ξ => ⟨Complex.contDiff_exp.comp (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp (L ξ).contDiff)), fun n => ⟨0, (|2 * Real.pi| * ‖L ξ‖) ^ n, fun x => by`. Rewrite using `[pow_zero, mul_one]`. Conclude with `GlobalTheory.CharModGrowth.norm_iteratedFDeriv_char_le (L ξ) (2 * Real.pi) n x⟩⟩`. Set `M : EuclideanSpace ℝ (Fin (Module.finrank ℝ V)) → 𝓢(V, ℂ)` to `fun ξ => SchwartzMap.smulLeftCLM ℂ (e ξ) g`.

Establish `hM : ∀ ξ x, M ξ x = e ξ x * g x` using `fun ξ x => by`. Simplify using `only [M, SchwartzMap.smulLeftCLM_apply_apply (he ξ), smul_eq_mul]`. Take `⟨u, hu, hI⟩` from `GlobalTheory.SchwartzPettis.exists_integral (μ := volume) (fun ξ => φ ξ • M ξ) (fun y => by`. Simplify using `only [SchwartzMap.smul_apply, hM, e, hL]`. Use `Continuous.aestronglyMeasurable (φ.continuous.smul ?_)` and prove the remaining obligations.

Use the proof step `fun_prop)`. Use the proof step `(fun k n => by set c : ℝ := |2 * Real.pi| * ‖A.toContinuousLinearMap‖ with hc`. Establish `hc0 : 0 ≤ c` using `by positivity`. Use `set S : ℝ := ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * SchwartzMap.seminorm ℂ k (n - i) g with hS`. Establish `hS0 : 0 ≤ S` using `Finset.sum_nonneg fun i _ => mul_nonneg (Nat.cast_nonneg _) (apply_nonneg _ _)`.

Use `⟨fun ξ => S * 2 ^ (n - 1) * (‖φ ξ‖ + c ^ n * (‖ξ‖ ^ n * ‖φ ξ‖)), ((φ.integrable.norm).add ((φ.integrable_pow_mul volume n).const_mul _)).const_mul _, fun ξ => ?_⟩` and prove the remaining obligations. Establish `h1` using `GlobalTheory.CharModGrowth.seminorm_char_mul_le (L ξ) (2 * Real.pi) g (M ξ) (hM ξ) (R := 1 + c * ‖ξ‖) (le_add_of_nonneg_right (by positivity)) (by`. Establish `h2 : ‖L ξ‖ ≤ ‖ξ‖ * ‖A.toContinuousLinearMap‖`. Use `(ContinuousLinearMap.opNorm_comp_le _ _).trans ?_` and prove the remaining obligations. Rewrite using `[innerSL_apply_norm]`.

Combine the equalities or inequalities in the displayed calculation. Establish `h3` using `add_pow_le (zero_le_one) (show 0 ≤ c * ‖ξ‖ by positivity) n`. Rewrite using `[map_smul_eq_mul]`. Combine the equalities or inequalities in the displayed calculation. Use `mul_le_mul_of_nonneg_left (h1.trans ?_) (norm_nonneg _)` and prove the remaining obligations.

Conclude with `mul_le_mul_of_nonneg_left h3 hS0`. Use `_ = _ := by ring)`. Establish `h0 : T u = 0`. Rewrite using `[(hI T).2]`. Use `integral_eq_zero_of_ae (ae_of_all _ fun ξ => ?_)` and prove the remaining obligations.

Simplify using `only [map_smul, Pi.zero_apply]`. Rewrite using `[hT ((2 * Real.pi) • L ξ) (M ξ) fun x => ?_, smul_zero]`. Rewrite using `[hM]`. Simplify using `only [e, ContinuousLinearMap.smul_apply, smul_eq_mul]`. Use `congr 2`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `h1 : u = h`. Use extensionality with `y`. Establish `h2 : ψ y = (FourierTransform.fourierInv φ : 𝓢(_, ℂ)) (A y)`.

Simplify using `only [φ, FourierTransform.fourierInv_fourier_eq, ψ', SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply, ContinuousLinearEquiv.symm_apply_apply]`. Rewrite using `[hu, hh, h2, SchwartzMap.fourierInv_coe, Real.fourierInv_eq', ← integral_const_mul]`. Use `congr 1`. Use function extensionality and compare the values at `ξ`. Simplify using `only [SchwartzMap.smul_apply, hM, e, hL, smul_eq_mul]`.

Rewrite using `[show Complex.I * ((2 * Real.pi : ℝ) : ℂ) * ((inner ℝ ξ (A y) : ℝ) : ℂ) = ((2 * Real.pi * inner ℝ ξ (A y) : ℝ) : ℂ) * Complex.I by push_cast; ring]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[← h1, h0]`.
-/
theorem map_mul_eq_zero_of_char [FiniteDimensional ℝ V] (T : 𝓢(V, ℂ) →L[ℂ] ℂ) (g : 𝓢(V, ℂ))
    (hT : ∀ (ξ : V →L[ℝ] ℝ) (h : 𝓢(V, ℂ)), (∀ x, h x = Complex.exp ((ξ x : ℂ) * Complex.I) * g x) → T h = 0)
    (ψ h : 𝓢(V, ℂ)) (hh : ∀ x, h x = g x * ψ x) : T h = 0 := by
  let A : V ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ V)) := toEuclidean
  let ψ' := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A.symm ψ
  let φ : 𝓢(EuclideanSpace ℝ (Fin (Module.finrank ℝ V)), ℂ) := FourierTransform.fourier ψ'
  let L : EuclideanSpace ℝ (Fin (Module.finrank ℝ V)) → V →L[ℝ] ℝ := fun ξ => (innerSL ℝ ξ).comp A.toContinuousLinearMap
  have hL : ∀ ξ x, L ξ x = inner ℝ ξ (A x) := fun ξ x => rfl
  let e : EuclideanSpace ℝ (Fin (Module.finrank ℝ V)) → V → ℂ :=
    fun ξ x => Complex.exp ((Complex.I * (2 * Real.pi : ℝ)) * (L ξ x : ℂ))
  have he : ∀ ξ, (e ξ).HasTemperateGrowth := fun ξ =>
    ⟨Complex.contDiff_exp.comp (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp (L ξ).contDiff)),
      fun n => ⟨0, (|2 * Real.pi| * ‖L ξ‖) ^ n, fun x => by
        rw [pow_zero, mul_one]
        exact GlobalTheory.CharModGrowth.norm_iteratedFDeriv_char_le (L ξ) (2 * Real.pi) n x⟩⟩
  let M : EuclideanSpace ℝ (Fin (Module.finrank ℝ V)) → 𝓢(V, ℂ) := fun ξ => SchwartzMap.smulLeftCLM ℂ (e ξ) g
  have hM : ∀ ξ x, M ξ x = e ξ x * g x := fun ξ x => by
    simp only [M, SchwartzMap.smulLeftCLM_apply_apply (he ξ), smul_eq_mul]
  obtain ⟨u, hu, hI⟩ := GlobalTheory.SchwartzPettis.exists_integral (μ := volume) (fun ξ => φ ξ • M ξ)
    (fun y => by
      simp only [SchwartzMap.smul_apply, hM, e, hL]
      refine Continuous.aestronglyMeasurable (φ.continuous.smul ?_)
      fun_prop)
    (fun k n => by
      set c : ℝ := |2 * Real.pi| * ‖A.toContinuousLinearMap‖ with hc
      have hc0 : 0 ≤ c := by positivity
      set S : ℝ := ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * SchwartzMap.seminorm ℂ k (n - i) g with hS
      have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ => mul_nonneg (Nat.cast_nonneg _) (apply_nonneg _ _)
      refine ⟨fun ξ => S * 2 ^ (n - 1) * (‖φ ξ‖ + c ^ n * (‖ξ‖ ^ n * ‖φ ξ‖)),
        ((φ.integrable.norm).add ((φ.integrable_pow_mul volume n).const_mul _)).const_mul _, fun ξ => ?_⟩
      have h1 := GlobalTheory.CharModGrowth.seminorm_char_mul_le (L ξ) (2 * Real.pi) g (M ξ) (hM ξ) (R := 1 + c * ‖ξ‖)
        (le_add_of_nonneg_right (by positivity)) (by
          have h2 : ‖L ξ‖ ≤ ‖ξ‖ * ‖A.toContinuousLinearMap‖ := by
            refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
            rw [innerSL_apply_norm]
          calc |2 * Real.pi| * ‖L ξ‖ ≤ |2 * Real.pi| * (‖ξ‖ * ‖A.toContinuousLinearMap‖) := by gcongr
            _ = c * ‖ξ‖ := by rw [hc]; ring
            _ ≤ _ := le_add_of_nonneg_left zero_le_one) k n
      have h3 := add_pow_le (zero_le_one) (show 0 ≤ c * ‖ξ‖ by positivity) n
      rw [map_smul_eq_mul]
      calc ‖φ ξ‖ * SchwartzMap.seminorm ℂ k n (M ξ) ≤ ‖φ ξ‖ * (S * (2 ^ (n - 1) * (1 ^ n + (c * ‖ξ‖) ^ n))) := by
            refine mul_le_mul_of_nonneg_left (h1.trans ?_) (norm_nonneg _)
            exact mul_le_mul_of_nonneg_left h3 hS0
        _ = _ := by ring)
  have h0 : T u = 0 := by
    rw [(hI T).2]
    refine integral_eq_zero_of_ae (ae_of_all _ fun ξ => ?_)
    simp only [map_smul, Pi.zero_apply]
    rw [hT ((2 * Real.pi) • L ξ) (M ξ) fun x => ?_, smul_zero]
    rw [hM]
    simp only [e, ContinuousLinearMap.smul_apply, smul_eq_mul]
    congr 2
    push_cast
    ring
  have h1 : u = h := by
    ext y
    have h2 : ψ y = (FourierTransform.fourierInv φ : 𝓢(_, ℂ)) (A y) := by
      simp only [φ, FourierTransform.fourierInv_fourier_eq, ψ', SchwartzMap.compCLMOfContinuousLinearEquiv_apply,
        Function.comp_apply, ContinuousLinearEquiv.symm_apply_apply]
    rw [hu, hh, h2, SchwartzMap.fourierInv_coe, Real.fourierInv_eq', ← integral_const_mul]
    congr 1
    funext ξ
    simp only [SchwartzMap.smul_apply, hM, e, hL, smul_eq_mul]
    rw [show Complex.I * ((2 * Real.pi : ℝ) : ℂ) * ((inner ℝ ξ (A y) : ℝ) : ℂ) =
      ((2 * Real.pi * inner ℝ ξ (A y) : ℝ) : ℂ) * Complex.I by push_cast; ring]
    ring
  rw [← h1, h0]

/- English proof (translation)
Set `B : LinearMap.BilinForm ℝ V` to `LinearMap.mk₂ ℝ P h.addL (fun c x y => by simpa [smul_eq_mul] using h.smulL c x y) h.addR (fun c x y => by simpa [smul_eq_mul] using h.smulR c x y)`. Establish `hinj : Function.Injective B.flip`. Rewrite using `[← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']`. Introduce `b hb`. Conclude with `h.nondegR b fun x => LinearMap.congr_fun hb x`.

Establish `hsurj` using `(LinearMap.injective_iff_surjective_of_finrank_eq_finrank (Subspace.dual_finrank_eq (K := ℝ) (V := V)).symm).1 hinj`. Take `⟨b, hb⟩` from `hsurj (L : V →ₗ[ℝ] ℝ)`. Conclude with `⟨b, fun y => LinearMap.congr_fun hb y⟩`.
-/
theorem exists_pairing_right [FiniteDimensional ℝ V] {P : V → V → ℝ} (h : GlobalTheory.ArchUniq.IsPairing P) (L : V →L[ℝ] ℝ) :
    ∃ b, ∀ y, P y b = L y := by
  let B : LinearMap.BilinForm ℝ V :=
    LinearMap.mk₂ ℝ P h.addL (fun c x y => by simpa [smul_eq_mul] using h.smulL c x y) h.addR
      (fun c x y => by simpa [smul_eq_mul] using h.smulR c x y)
  have hinj : Function.Injective B.flip := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro b hb
    exact h.nondegR b fun x => LinearMap.congr_fun hb x
  have hsurj := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (Subspace.dual_finrank_eq (K := ℝ) (V := V)).symm).1 hinj
  obtain ⟨b, hb⟩ := hsurj (L : V →ₗ[ℝ] ℝ)
  exact ⟨b, fun y => LinearMap.congr_fun hb y⟩

/- English proof (translation)
Introduce `V _ _ _ P hP T g hg hT`. Use `eq_zero_of_mul_translates T g hg fun a ψ h hh => ?_` and prove the remaining obligations. Use `map_mul_eq_zero_of_char T (SchwartzMap.compSubConstCLM ℂ a g) (fun ξ h' hh' => ?_) ψ h hh` and prove the remaining obligations. Take `⟨b, hb⟩` from `exists_pairing_right hP ((-(2 * Real.pi)⁻¹ : ℝ) • ξ)`. Establish `h1` using `hT (-a, b) (Complex.exp (-(2 * Real.pi * Complex.I) * ((P (-a) b / 2 : ℝ) : ℂ)) • h') (by`.

Use function extensionality and compare the values at `y`. Rewrite using `[SchwartzMap.smul_apply, smul_eq_mul, hh', SchwartzMap.compSubConstCLM_apply, ← mul_assoc, ← Complex.exp_add]`. Simplify using `only [GlobalTheory.ArchUniq.schrF]`. Rewrite using `[hb y, ← sub_eq_add_neg]`. Use `congr 2`.

Establish `hpi : (Real.pi : ℂ) ≠ 0` using `Complex.ofReal_ne_zero.2 Real.pi_ne_zero`. Simplify using `only [ContinuousLinearMap.smul_apply, smul_eq_mul]`. Use `push_cast`. Clear the denominators using the available nonvanishing facts. Use the proof step `ring)`.

Rewrite `h1` using `[map_smul, smul_eq_mul]`. Conclude with `(mul_eq_zero.1 h1).resolve_left (Complex.exp_ne_zero _)`.
-/
theorem eq_zero_of_schrF : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (P : V → V → ℝ), GlobalTheory.ArchUniq.IsPairing P → ∀ (T : 𝓢(V, ℂ) →L[ℂ] ℂ) (g : 𝓢(V, ℂ)), g ≠ 0 → (∀ (w : V × V) (g₁ : 𝓢(V, ℂ)), ⇑g₁ = GlobalTheory.ArchUniq.schrF P w ⇑g → T g₁ = 0) → T = 0 := by
  intro V _ _ _ P hP T g hg hT
  refine eq_zero_of_mul_translates T g hg fun a ψ h hh => ?_
  refine map_mul_eq_zero_of_char T (SchwartzMap.compSubConstCLM ℂ a g) (fun ξ h' hh' => ?_) ψ h hh
  obtain ⟨b, hb⟩ := exists_pairing_right hP ((-(2 * Real.pi)⁻¹ : ℝ) • ξ)
  have h1 := hT (-a, b) (Complex.exp (-(2 * Real.pi * Complex.I) * ((P (-a) b / 2 : ℝ) : ℂ)) • h') (by
    funext y
    rw [SchwartzMap.smul_apply, smul_eq_mul, hh', SchwartzMap.compSubConstCLM_apply, ← mul_assoc, ← Complex.exp_add]
    simp only [GlobalTheory.ArchUniq.schrF]
    rw [hb y, ← sub_eq_add_neg]
    congr 2
    have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
    simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
    push_cast
    field_simp
    ring)
  rw [map_smul, smul_eq_mul] at h1
  exact (mul_eq_zero.1 h1).resolve_left (Complex.exp_ne_zero _)

end GlobalTheory.SchrIrred

end
