import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LApproxIdS

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField

namespace PositivityTheory.Rg.Rsw.L.LApproxId

/- English proof (translation)
Use `haveI : BorelSpace (AF F) := ⟨rfl⟩`. Use `haveI : SecondCountableTopology (fixE ε) := TopologicalSpace.Subtype.secondCountableTopology _`. Use `haveI : OpensMeasurableSpace (fixE ε × fixE ε) := inferInstance`. Establish `hψn : ∀ x, ‖ψ x‖ = 1` using `hψ.2.1`. Establish `hconj : ∀ x, (starRingEnd ℂ) (ψ x) = ψ (-x)`.

Introduce `x`. Rewrite using `[AddChar.map_neg_eq_inv, Complex.inv_def, Complex.normSq_eq_norm_sq, hψn x]`. Simplify using the standard rewrite rules. Establish `hτC : Integrable (fun h => (τ h : ℂ)) ν` using `hτI.ofReal`. Establish `hA' : ∀ h : fixE ε, (starRingEnd ℂ) (A h) = ∫ h', (τ h' : ℂ) * ψ (h.1 * (-h').1) ∂ν`.

Introduce `h`. Rewrite using `[hA, ← integral_conj]`. Use `congr 1`. Use function extensionality and compare the values at `h'`. Rewrite using `[map_mul, Complex.conj_ofReal, hconj]`.

Use `congr 2`. Express the relevant statement in the definitionally equal form `-(h'.1 * h.1) = h.1 * -h'.1`. Expand and normalize the polynomial expressions, which then agree. Use `set f : fixE ε → fixE ε → ℂ := fun h h' => A h * ((τ h' : ℂ) * ψ (h.1 * (-h').1)) with hf`. Establish `hcont : Continuous fun z : fixE ε × fixE ε => ψ (z.1.1 * (-z.2).1)` using `hψ.1.comp ((continuous_subtype_val.comp continuous_fst).mul (continuous_subtype_val.comp (continuous_neg.comp continuous_snd)))`.

Establish `hfI : Integrable (Function.uncurry f) (ν.prod ν)`. Use `Integrable.mono' (hAI.norm.mul_prod hτI) ?_ (Filter.Eventually.of_forall fun z => ?_)` and prove the remaining obligations. Conclude with `hAI.aestronglyMeasurable.comp_fst.mul (hτC.aestronglyMeasurable.comp_snd.mul hcont.aestronglyMeasurable)`. Simplify using `only [Function.uncurry, hf, norm_mul, hψn, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hτ0 _)]`. Conclude with `le_rfl`.

Establish `hsw` using `integral_integral_swap hfI`. Establish `hL : ∫ h, A h * (starRingEnd ℂ) (A h) ∂ν = ∫ h, ∫ h', f h h' ∂ν ∂ν`. Use `congr 1`. Use function extensionality and compare the values at `h`. Rewrite using `[hA', ← integral_const_mul]`.

Establish `hR : ∫ h', ∫ h, f h h' ∂ν ∂ν = κ * ∫ h', ((τ h' * τ h' : ℝ) : ℂ) ∂ν`. Rewrite using `[← integral_const_mul]`. Use `congr 1`. Use function extensionality and compare the values at `h'`. Establish `h1 : ∫ h, f h h' ∂ν = (τ h' : ℂ) * ∫ h, A h * ψ (h.1 * (-h').1) ∂ν`.

Rewrite using `[← integral_const_mul]`. Use `congr 1`. Use function extensionality and compare the values at `h`. Simplify using `only [hf]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[h1, hκ, neg_neg]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hLr : ∫ h, A h * (starRingEnd ℂ) (A h) ∂ν = ((∫ h, Complex.normSq (A h) ∂ν : ℝ) : ℂ)`. Rewrite using `[← integral_complex_ofReal]`.

Use `congr 1`. Use function extensionality and compare the values at `h`. Conclude with `Complex.mul_conj _`. Establish `hL0 : 0 ≤ ∫ h, Complex.normSq (A h) ∂ν` using `integral_nonneg fun h => Complex.normSq_nonneg _`. Establish `hQI : Integrable (fun h => τ h * τ h) ν`.

Use `Integrable.mono' (hτI.const_mul M) (hτI.aestronglyMeasurable.mul hτI.aestronglyMeasurable) (Filter.Eventually.of_forall fun h => ?_)` and prove the remaining obligations. Rewrite using `[Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hτ0 h) (hτ0 h)), mul_comm M]`. Conclude with `mul_le_mul_of_nonneg_left (hτM h) (hτ0 h)`. Establish `hQ0 : 0 < ∫ h, τ h * τ h ∂ν`. Use `lt_of_le_of_ne (integral_nonneg fun h => mul_nonneg (hτ0 h) (hτ0 h)) fun h0 => ?_` and prove the remaining obligations.

Establish `hz` using `(integral_eq_zero_iff_of_nonneg (fun h => mul_nonneg (hτ0 h) (hτ0 h)) hQI).1 h0.symm`. Establish `hz' : τ =ᵐ[ν] 0` using `hz.mono fun h hh => by`. Simplify using `using (mul_self_eq_zero.1 hh)`. Rewrite `hτpos` using `[integral_congr_ae hz']`. Simplify using `at hτpos`.

Establish `hmain : ((∫ h, Complex.normSq (A h) ∂ν : ℝ) : ℂ) = κ * ((∫ h, τ h * τ h ∂ν : ℝ) : ℂ)`. Rewrite using `[← hLr, hL, hsw, hR, integral_complex_ofReal]`. Establish `hκe : κ = (((∫ h, Complex.normSq (A h) ∂ν) / ∫ h, τ h * τ h ∂ν : ℝ) : ℂ)`. Establish `hq : ((∫ h, τ h * τ h ∂ν : ℝ) : ℂ) ≠ 0` using `by exact_mod_cast hQ0.ne'`. Rewrite using `[Complex.ofReal_div, hmain, mul_div_assoc, div_self hq, mul_one]`.

Rewrite using `[hκe, Complex.ofReal_im, Complex.ofReal_re]`. Conclude with `⟨rfl, div_nonneg hL0 hQ0.le⟩`.
-/
theorem kappa_real {F : Type} [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ) (hψ : IsCharAF F ψ) {ε : AF F}
    (ν : Measure (fixE ε)) [SFinite ν] (τ : fixE ε → ℝ) (hτ0 : ∀ h, 0 ≤ τ h) (hτI : Integrable τ ν)
    (hτpos : 0 < ∫ h, τ h ∂ν) (M : ℝ) (hτM : ∀ h, τ h ≤ M) (A : fixE ε → ℂ)
    (hA : ∀ s, A s = ∫ h, (τ h : ℂ) * ψ (h.1 * s.1) ∂ν) (hAI : Integrable A ν) (κ : ℂ)
    (hκ : ∀ s : fixE ε, ∫ h, A h * ψ (h.1 * s.1) ∂ν = κ * τ (-s)) :
    κ.im = 0 ∧ 0 ≤ κ.re := by
  haveI : BorelSpace (AF F) := ⟨rfl⟩
  haveI : SecondCountableTopology (fixE ε) := TopologicalSpace.Subtype.secondCountableTopology _
  haveI : OpensMeasurableSpace (fixE ε × fixE ε) := inferInstance
  have hψn : ∀ x, ‖ψ x‖ = 1 := hψ.2.1
  have hconj : ∀ x, (starRingEnd ℂ) (ψ x) = ψ (-x) := by
    intro x
    rw [AddChar.map_neg_eq_inv, Complex.inv_def, Complex.normSq_eq_norm_sq, hψn x]
    simp
  have hτC : Integrable (fun h => (τ h : ℂ)) ν := hτI.ofReal

  have hA' : ∀ h : fixE ε, (starRingEnd ℂ) (A h) = ∫ h', (τ h' : ℂ) * ψ (h.1 * (-h').1) ∂ν := by
    intro h
    rw [hA, ← integral_conj]
    congr 1
    funext h'
    rw [map_mul, Complex.conj_ofReal, hconj]
    congr 2
    change -(h'.1 * h.1) = h.1 * -h'.1
    ring

  set f : fixE ε → fixE ε → ℂ := fun h h' => A h * ((τ h' : ℂ) * ψ (h.1 * (-h').1)) with hf
  have hcont : Continuous fun z : fixE ε × fixE ε => ψ (z.1.1 * (-z.2).1) :=
    hψ.1.comp ((continuous_subtype_val.comp continuous_fst).mul (continuous_subtype_val.comp
      (continuous_neg.comp continuous_snd)))
  have hfI : Integrable (Function.uncurry f) (ν.prod ν) := by
    refine Integrable.mono' (hAI.norm.mul_prod hτI) ?_ (Filter.Eventually.of_forall fun z => ?_)
    · exact hAI.aestronglyMeasurable.comp_fst.mul (hτC.aestronglyMeasurable.comp_snd.mul hcont.aestronglyMeasurable)
    · simp only [Function.uncurry, hf, norm_mul, hψn, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (hτ0 _)]
      exact le_rfl
  have hsw := integral_integral_swap hfI
  have hL : ∫ h, A h * (starRingEnd ℂ) (A h) ∂ν = ∫ h, ∫ h', f h h' ∂ν ∂ν := by
    congr 1
    funext h
    rw [hA', ← integral_const_mul]
  have hR : ∫ h', ∫ h, f h h' ∂ν ∂ν = κ * ∫ h', ((τ h' * τ h' : ℝ) : ℂ) ∂ν := by
    rw [← integral_const_mul]
    congr 1
    funext h'
    have h1 : ∫ h, f h h' ∂ν = (τ h' : ℂ) * ∫ h, A h * ψ (h.1 * (-h').1) ∂ν := by
      rw [← integral_const_mul]
      congr 1
      funext h
      simp only [hf]
      ring
    rw [h1, hκ, neg_neg]
    push_cast
    ring

  have hLr : ∫ h, A h * (starRingEnd ℂ) (A h) ∂ν = ((∫ h, Complex.normSq (A h) ∂ν : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    congr 1
    funext h
    exact Complex.mul_conj _
  have hL0 : 0 ≤ ∫ h, Complex.normSq (A h) ∂ν := integral_nonneg fun h => Complex.normSq_nonneg _
  have hQI : Integrable (fun h => τ h * τ h) ν := by
    refine Integrable.mono' (hτI.const_mul M) (hτI.aestronglyMeasurable.mul hτI.aestronglyMeasurable)
      (Filter.Eventually.of_forall fun h => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hτ0 h) (hτ0 h)), mul_comm M]
    exact mul_le_mul_of_nonneg_left (hτM h) (hτ0 h)
  have hQ0 : 0 < ∫ h, τ h * τ h ∂ν := by
    refine lt_of_le_of_ne (integral_nonneg fun h => mul_nonneg (hτ0 h) (hτ0 h)) fun h0 => ?_
    have hz := (integral_eq_zero_iff_of_nonneg (fun h => mul_nonneg (hτ0 h) (hτ0 h)) hQI).1 h0.symm
    have hz' : τ =ᵐ[ν] 0 := hz.mono fun h hh => by
      simpa using (mul_self_eq_zero.1 hh)
    rw [integral_congr_ae hz'] at hτpos
    simp at hτpos
  have hmain : ((∫ h, Complex.normSq (A h) ∂ν : ℝ) : ℂ) = κ * ((∫ h, τ h * τ h ∂ν : ℝ) : ℂ) := by
    rw [← hLr, hL, hsw, hR, integral_complex_ofReal]
  have hκe : κ = (((∫ h, Complex.normSq (A h) ∂ν) / ∫ h, τ h * τ h ∂ν : ℝ) : ℂ) := by
    have hq : ((∫ h, τ h * τ h ∂ν : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hQ0.ne'
    rw [Complex.ofReal_div, hmain, mul_div_assoc, div_self hq, mul_one]
  rw [hκe, Complex.ofReal_im, Complex.ofReal_re]
  exact ⟨rfl, div_nonneg hL0 hQ0.le⟩

end PositivityTheory.Rg.Rsw.L.LApproxId

end
