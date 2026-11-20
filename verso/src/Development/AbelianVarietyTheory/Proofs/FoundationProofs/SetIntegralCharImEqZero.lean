import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsPosHermFormV
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IntMIffInt
open Complex MeasureTheory GlobalTheory.UnitaryTheta
open scoped BigOperators ComplexConjugate Real Classical Pointwise

namespace GlobalTheory.UnitaryTheta

/- English proof (translation)
Establish `hq : MeasurePreserving (fun x => t + x) μ μ` using `measurePreserving_add_left μ t`. Establish `hF' : IsAddFundamentalDomain Λ ((fun x => t + x) ⁻¹' Fd) μ` using `hF.preimage_of_equiv hq.quasiMeasurePreserving (e := id) Function.bijective_id (fun g x => by simp [AddSubgroup.vadd_def, add_left_comm])`. Establish `h1 : ∫ z in (fun x => t + x) ⁻¹' Fd, f z ∂μ = ∫ z in Fd, f z ∂μ` using `hF'.setIntegral_eq hF (fun g x => by simp [AddSubgroup.vadd_def, hf, hΛ g g.2])`. Establish `h2 : ∫ z in (fun x => t + x) ⁻¹' Fd, f (t + z) ∂μ = ∫ z in Fd, f z ∂μ` using `hq.setIntegral_preimage_emb (measurableEmbedding_addLeft t) f Fd`. Establish `h3 : ∫ z in (fun x => t + x) ⁻¹' Fd, f (t + z) ∂μ = - ∫ z in Fd, f z ∂μ`.

Simplify using `only [hf, ht, neg_one_mul, integral_neg, h1]`. Take the linear combination `(h3 - h2) / 2`.
-/
theorem setIntegral_mul_char_eq_zero {V : Type} [NormedAddCommGroup V] [MeasurableSpace V] [BorelSpace V]
    [SecondCountableTopology V]
    (μ : Measure V) [μ.IsAddHaarMeasure] (Λ : AddSubgroup V) [Countable Λ] (Fd : Set V)
    (hF : IsAddFundamentalDomain Λ Fd μ) (f : V → ℂ) (hf : ∀ x y, f (x + y) = f x * f y)
    (hΛ : ∀ y ∈ Λ, f y = 1) (t : V) (ht : f t = -1) : ∫ z in Fd, f z ∂μ = 0 := by
  have hq : MeasurePreserving (fun x => t + x) μ μ := measurePreserving_add_left μ t
  have hF' : IsAddFundamentalDomain Λ ((fun x => t + x) ⁻¹' Fd) μ :=
    hF.preimage_of_equiv hq.quasiMeasurePreserving (e := id) Function.bijective_id
      (fun g x => by simp [AddSubgroup.vadd_def, add_left_comm])
  have h1 : ∫ z in (fun x => t + x) ⁻¹' Fd, f z ∂μ = ∫ z in Fd, f z ∂μ :=
    hF'.setIntegral_eq hF (fun g x => by simp [AddSubgroup.vadd_def, hf, hΛ g g.2])
  have h2 : ∫ z in (fun x => t + x) ⁻¹' Fd, f (t + z) ∂μ = ∫ z in Fd, f z ∂μ :=
    hq.setIntegral_preimage_emb (measurableEmbedding_addLeft t) f Fd
  have h3 : ∫ z in (fun x => t + x) ⁻¹' Fd, f (t + z) ∂μ = - ∫ z in Fd, f z ∂μ := by
    simp only [hf, ht, neg_one_mul, integral_neg, h1]
  linear_combination (h3 - h2) / 2

/- English proof (translation)
Introduce `V _ _ _ _ _ μ _ H hH Λ _ Fd hF v hv hint`. Use `haveI : ProperSpace V := FiniteDimensional.proper ℂ V`. Establish `hpos` using `hH.2 v hv`. Use `set r : ℝ := (H v v).re with hr`. Use `setIntegral_mul_char_eq_zero μ Λ Fd hF (fun z => cexp (2 * π * I * ((H v z).im : ℂ))) (fun x y => ?_) (fun y hy => ?_) (((-(1 / (2 * r)) : ℝ) * I : ℂ) • v) ?_` and prove the remaining obligations.

Simplify using `only [map_add, add_im, ofReal_add, mul_add, Complex.exp_add]`. Take `⟨m, hm⟩` from `hint y hy`. Simplify using `only [hm, ofReal_intCast]`. Rewrite using `[mul_comm]`. Conclude with `Complex.exp_int_mul_two_pi_mul_I m`.

Establish `e : (H v (((-(1 / (2 * r)) : ℝ) * I : ℂ) • v)).im = 1 / 2`. Rewrite using `[LinearMap.map_smulₛₗ, smul_eq_mul, map_mul, conj_ofReal, conj_I]`. Simplify using `only [mul_im, mul_re, ofReal_re, ofReal_im, neg_re, neg_im, I_re, I_im, ← hr]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.

Simplify using `only [e]`. Rewrite using `[← Complex.exp_pi_mul_I]`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem setIntegral_char_im_eq_zero :
    ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] (H : Sesq V), IsPosHerm H → ∀ (Λ : AddSubgroup V) [Countable Λ] (Fd : Set V), IsAddFundamentalDomain Λ Fd μ → ∀ v : V, v ≠ 0 → (∀ y ∈ Λ, ∃ m : ℤ, (H v y).im = m) → ∫ z in Fd, cexp (2 * π * I * ((H v z).im : ℂ)) ∂μ = 0 := by
  intro V _ _ _ _ _ μ _ H hH Λ _ Fd hF v hv hint
  haveI : ProperSpace V := FiniteDimensional.proper ℂ V
  have hpos := hH.2 v hv
  set r : ℝ := (H v v).re with hr
  refine setIntegral_mul_char_eq_zero μ Λ Fd hF (fun z => cexp (2 * π * I * ((H v z).im : ℂ)))
    (fun x y => ?_) (fun y hy => ?_) (((-(1 / (2 * r)) : ℝ) * I : ℂ) • v) ?_
  · simp only [map_add, add_im, ofReal_add, mul_add, Complex.exp_add]
  · obtain ⟨m, hm⟩ := hint y hy
    simp only [hm, ofReal_intCast]
    rw [mul_comm]
    exact Complex.exp_int_mul_two_pi_mul_I m
  · have e : (H v (((-(1 / (2 * r)) : ℝ) * I : ℂ) • v)).im = 1 / 2 := by
      rw [LinearMap.map_smulₛₗ, smul_eq_mul, map_mul, conj_ofReal, conj_I]
      simp only [mul_im, mul_re, ofReal_re, ofReal_im, neg_re, neg_im, I_re, I_im, ← hr]
      field_simp
      ring
    simp only [e]
    rw [← Complex.exp_pi_mul_I]
    congr 1
    push_cast
    ring

end GlobalTheory.UnitaryTheta
