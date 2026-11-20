import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzIntegralSuperpositionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzFamilyPhaseBoundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzFourierRepresentationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzInnerProductContinuousStatement

open MeasureTheory

namespace GlobalTheory.CharMult

/- English proof (translation)
Introduce `V _ _ _ μ hμ T hT m f f' g g' hf' hg'`. Use `letI : MeasurableSpace V := borel V`. Use `haveI : BorelSpace V := ⟨rfl⟩`. Take `⟨d, A, h, hm⟩` from `GlobalTheory.T.schwartz_fourier_representation V m`. Take `⟨Φf, hΦf, cΦf, bΦf⟩` from `GlobalTheory.T.schwartz_family_phase_bound V _ A f`.

Take `⟨Φg, hΦg, cΦg, bΦg⟩` from `GlobalTheory.T.schwartz_family_phase_bound V _ (-A) g`. Take `⟨Λ1, hΛ1⟩` from `GlobalTheory.T.schwartz_inner_product_continuous V μ hμ (T g)`. Take `⟨Λ2, hΛ2⟩` from `GlobalTheory.T.schwartz_inner_product_continuous V μ hμ (T f)`. Establish `hint : ∀ (Φ : EuclideanSpace ℝ (Fin d) → SchwartzMap V ℂ), Continuous Φ → (∀ k n : ℕ, ∃ C : ℝ, ∀ ξ, SchwartzMap.seminorm ℂ k n (Φ ξ) ≤ C * (1 + ‖ξ‖ ^ n)) → ∀ (c : EuclideanSpace ℝ (Fin d) → ℂ), (∀ ξ, ‖c ξ‖ = ‖h ξ‖) → ∀ k n : ℕ, Integrable (fun ξ => ‖c ξ‖ * SchwartzMap.seminorm ℂ …`. Introduce `Φ hΦ hb c hc k n`.

Take `⟨C, hC⟩` from `hb k n`. Establish `hcont : Continuous (fun ξ => SchwartzMap.seminorm ℂ k n (Φ ξ))` using `((schwartz_withSeminorms ℂ V ℂ).continuous_seminorm (k, n)).comp hΦ`. Establish `i1 : Integrable (fun ξ => ‖h ξ‖)` using `h.integrable.norm`. Establish `i2 : Integrable (fun ξ => ‖ξ‖ ^ n * ‖h ξ‖)` using `h.integrable_pow_mul volume n`. Use `Integrable.mono' ((i1.add i2).const_mul C) ?_ ?_` and prove the remaining obligations.

Repeatedly rewrite using `[hc]`. Conclude with `(h.continuous.norm.mul hcont).aestronglyMeasurable`. Use `filter_upwards with ξ`. Rewrite using `[hc, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (norm_nonneg _) (apply_nonneg _ _))]`. Combine the equalities or inequalities in the displayed calculation.

Establish `hkey : ∀ ξ, Λ1 (T (Φf ξ)) = ∫ x, T f x * starRingEnd ℂ (T (Φg ξ) x) ∂μ`. Introduce `ξ`. Rewrite using `[hΛ1]`. Use `hT (A ξ) f (Φf ξ) (Φg ξ) g (hΦf ξ) (fun x => ?_)` and prove the remaining obligations. Rewrite using `[hΦg, ← mul_assoc, ← Complex.exp_add]`.

Simplify using `[ContinuousLinearMap.neg_apply]`. Establish `lhs : ∫ x, T f' x * starRingEnd ℂ (T g x) ∂μ = ∫ ξ, h ξ * ∫ x, T f x * starRingEnd ℂ (T (Φg ξ) x) ∂μ`. Rewrite using `[← hΛ1]`. Use `GlobalTheory.T.schwartz_integral_superposition V (EuclideanSpace ℝ (Fin d)) volume Φf cΦf h h.continuous.aestronglyMeasurable (hint Φf cΦf bΦf h (fun _ => rfl)) f' (fun x => by` as an intermediate fact. Rewrite using `[hf', hm, ← integral_mul_const]`.

Use `congr 1`. Use function extensionality and compare the values at `ξ`. Rewrite using `[hΦf]`. Use the proof step `ring) (Λ1.comp T)`. Simplify using `only [ContinuousLinearMap.comp_apply] at this`.

Rewrite using `[this]`. Repeatedly rewrite using `[hkey]`. Establish `rhs : ∫ x, T f x * starRingEnd ℂ (T g' x) ∂μ = ∫ ξ, h ξ * ∫ x, T f x * starRingEnd ℂ (T (Φg ξ) x) ∂μ`. Establish `e1 : ∫ x, T f x * starRingEnd ℂ (T g' x) ∂μ = starRingEnd ℂ (Λ2 (T g'))`. Rewrite using `[hΛ2, ← integral_conj]`.

Use `congr 1`. Use function extensionality and compare the values at `x`. Simplify using `[mul_comm]`. Use `GlobalTheory.T.schwartz_integral_superposition V (EuclideanSpace ℝ (Fin d)) volume Φg cΦg (fun ξ => starRingEnd ℂ (h ξ)) (Complex.continuous_conj.comp h.continuous).aestronglyMeasurable (hint Φg cΦg bΦg _ (fun _ => Complex.norm_conj _)) g' (fun x => by` as an intermediate fact. Rewrite using `[hg', hm, ← integral_conj, ← integral_mul_const]`.

Use `congr 1`. Use function extensionality and compare the values at `ξ`. Rewrite using `[hΦg]`. Simplify using `only [map_mul, ContinuousLinearMap.neg_apply, ← Complex.exp_conj]`. Simplify using `[Complex.ofReal_neg]`.

Use the proof step `ring) (Λ2.comp T)`. Simplify using `only [ContinuousLinearMap.comp_apply] at this`. Rewrite using `[e1, this, ← integral_conj]`. Use `congr 1`. Use function extensionality and compare the values at `ξ`.

Rewrite using `[map_mul, Complex.conj_conj, hΛ2, ← integral_conj]`. Use `congr 2`. Use function extensionality and compare the values at `x`. Simplify using `[mul_comm]`. Rewrite using `[lhs, rhs]`.
-/
theorem multiplier_symm : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (μ : @MeasureTheory.Measure V (borel V)), @MeasureTheory.Measure.IsAddHaarMeasure V _ _ (borel V) μ →
    ∀ (T : SchwartzMap V ℂ →L[ℂ] SchwartzMap V ℂ),
    (∀ (L : V →L[ℝ] ℝ) (f f' g g' : SchwartzMap V ℂ),
      (∀ x, f' x = Complex.exp (Complex.I * (L x : ℂ)) * f x) →
      (∀ x, g' x = Complex.exp (Complex.I * (L x : ℂ)) * g x) →
      @MeasureTheory.integral V ℂ _ _ (borel V) μ (fun x => T f' x * starRingEnd ℂ (T g' x)) =
        @MeasureTheory.integral V ℂ _ _ (borel V) μ (fun x => T f x * starRingEnd ℂ (T g x))) →
    ∀ (m f f' g g' : SchwartzMap V ℂ), (∀ x, f' x = m x * f x) → (∀ x, g' x = starRingEnd ℂ (m x) * g x) →
      @MeasureTheory.integral V ℂ _ _ (borel V) μ (fun x => T f' x * starRingEnd ℂ (T g x)) =
        @MeasureTheory.integral V ℂ _ _ (borel V) μ (fun x => T f x * starRingEnd ℂ (T g' x)) := by
  intro V _ _ _ μ hμ T hT m f f' g g' hf' hg'
  letI : MeasurableSpace V := borel V
  haveI : BorelSpace V := ⟨rfl⟩
  obtain ⟨d, A, h, hm⟩ := GlobalTheory.T.schwartz_fourier_representation V m
  obtain ⟨Φf, hΦf, cΦf, bΦf⟩ := GlobalTheory.T.schwartz_family_phase_bound V _ A f
  obtain ⟨Φg, hΦg, cΦg, bΦg⟩ := GlobalTheory.T.schwartz_family_phase_bound V _ (-A) g
  obtain ⟨Λ1, hΛ1⟩ := GlobalTheory.T.schwartz_inner_product_continuous V μ hμ (T g)
  obtain ⟨Λ2, hΛ2⟩ := GlobalTheory.T.schwartz_inner_product_continuous V μ hμ (T f)
  have hint : ∀ (Φ : EuclideanSpace ℝ (Fin d) → SchwartzMap V ℂ), Continuous Φ →
      (∀ k n : ℕ, ∃ C : ℝ, ∀ ξ, SchwartzMap.seminorm ℂ k n (Φ ξ) ≤ C * (1 + ‖ξ‖ ^ n)) →
      ∀ (c : EuclideanSpace ℝ (Fin d) → ℂ), (∀ ξ, ‖c ξ‖ = ‖h ξ‖) →
      ∀ k n : ℕ, Integrable (fun ξ => ‖c ξ‖ * SchwartzMap.seminorm ℂ k n (Φ ξ)) := by
    intro Φ hΦ hb c hc k n
    obtain ⟨C, hC⟩ := hb k n
    have hcont : Continuous (fun ξ => SchwartzMap.seminorm ℂ k n (Φ ξ)) :=
      ((schwartz_withSeminorms ℂ V ℂ).continuous_seminorm (k, n)).comp hΦ
    have i1 : Integrable (fun ξ => ‖h ξ‖) := h.integrable.norm
    have i2 : Integrable (fun ξ => ‖ξ‖ ^ n * ‖h ξ‖) := h.integrable_pow_mul volume n
    refine Integrable.mono' ((i1.add i2).const_mul C) ?_ ?_
    · simp_rw [hc]
      exact (h.continuous.norm.mul hcont).aestronglyMeasurable
    · filter_upwards with ξ
      rw [hc, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (norm_nonneg _) (apply_nonneg _ _))]
      calc ‖h ξ‖ * SchwartzMap.seminorm ℂ k n (Φ ξ) ≤ ‖h ξ‖ * (C * (1 + ‖ξ‖ ^ n)) :=
            mul_le_mul_of_nonneg_left (hC ξ) (norm_nonneg _)
        _ = C * (‖h ξ‖ + ‖ξ‖ ^ n * ‖h ξ‖) := by ring

  have hkey : ∀ ξ, Λ1 (T (Φf ξ)) = ∫ x, T f x * starRingEnd ℂ (T (Φg ξ) x) ∂μ := by
    intro ξ
    rw [hΛ1]
    refine hT (A ξ) f (Φf ξ) (Φg ξ) g (hΦf ξ) (fun x => ?_)
    rw [hΦg, ← mul_assoc, ← Complex.exp_add]
    simp [ContinuousLinearMap.neg_apply]
  have lhs : ∫ x, T f' x * starRingEnd ℂ (T g x) ∂μ = ∫ ξ, h ξ * ∫ x, T f x * starRingEnd ℂ (T (Φg ξ) x) ∂μ := by
    rw [← hΛ1]
    have := GlobalTheory.T.schwartz_integral_superposition V (EuclideanSpace ℝ (Fin d)) volume Φf cΦf h h.continuous.aestronglyMeasurable
      (hint Φf cΦf bΦf h (fun _ => rfl)) f' (fun x => by
        rw [hf', hm, ← integral_mul_const]
        congr 1; funext ξ; rw [hΦf]; ring) (Λ1.comp T)
    simp only [ContinuousLinearMap.comp_apply] at this
    rw [this]; simp_rw [hkey]
  have rhs : ∫ x, T f x * starRingEnd ℂ (T g' x) ∂μ = ∫ ξ, h ξ * ∫ x, T f x * starRingEnd ℂ (T (Φg ξ) x) ∂μ := by
    have e1 : ∫ x, T f x * starRingEnd ℂ (T g' x) ∂μ = starRingEnd ℂ (Λ2 (T g')) := by
      rw [hΛ2, ← integral_conj]; congr 1; funext x; simp [mul_comm]
    have := GlobalTheory.T.schwartz_integral_superposition V (EuclideanSpace ℝ (Fin d)) volume Φg cΦg (fun ξ => starRingEnd ℂ (h ξ))
      (Complex.continuous_conj.comp h.continuous).aestronglyMeasurable
      (hint Φg cΦg bΦg _ (fun _ => Complex.norm_conj _)) g' (fun x => by
        rw [hg', hm, ← integral_conj, ← integral_mul_const]
        congr 1; funext ξ; rw [hΦg]
        simp only [map_mul, ContinuousLinearMap.neg_apply, ← Complex.exp_conj]
        simp [Complex.ofReal_neg]; ring) (Λ2.comp T)
    simp only [ContinuousLinearMap.comp_apply] at this
    rw [e1, this, ← integral_conj]
    congr 1; funext ξ
    rw [map_mul, Complex.conj_conj, hΛ2, ← integral_conj]
    congr 2; funext x; simp [mul_comm]
  rw [lhs, rhs]

end GlobalTheory.CharMult
