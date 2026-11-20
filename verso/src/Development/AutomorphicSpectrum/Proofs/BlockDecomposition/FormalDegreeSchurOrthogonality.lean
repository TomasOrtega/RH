import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegrableMulInner

noncomputable section

open MeasureTheory GlobalTheory.CompanionTheory.UnitaryFramesMetricPeriods GlobalTheory.CompanionTheory.RgHeA
open scoped InnerProductSpace ComplexConjugate

namespace GlobalTheory.CompanionTheory.RgHeA

/- English proof (translation)
The claim follows from `(⟨(ρ g : B →ₗ[ℂ] B), hρ.norm g⟩ : B →ₗᵢ[ℂ] B).inner_map_map x y`.
-/
private theorem avg_conj_coef_ge_lemma {Γ : Type} [Group Γ] [TopologicalSpace Γ] {B : Type}
    [NormedAddCommGroup B] [InnerProductSpace ℂ B] {ρ : Γ → (B →L[ℂ] B)} (hρ : IsU ρ)
    (g : Γ) (x y : B) : ⟪ρ g x, ρ g y⟫_ℂ = ⟪x, y⟫_ℂ :=
  (⟨(ρ g : B →ₗ[ℂ] B), hρ.norm g⟩ : B →ₗᵢ[ℂ] B).inner_map_map x y

/- English proof (translation)
Rewrite using `[hρ.mul]`. Both sides reduce to the same expression.
-/
private theorem avg_conj_coef_ge_lemma_2 {Γ : Type} [Group Γ] [TopologicalSpace Γ] {B : Type}
    [NormedAddCommGroup B] [InnerProductSpace ℂ B] {ρ : Γ → (B →L[ℂ] B)} (hρ : IsU ρ)
    (g h : Γ) (x : B) : ρ g (ρ h x) = ρ (g * h) x := by
  rw [hρ.mul]; rfl

/- English proof (translation)
Establish `e : y = ρ g (ρ g⁻¹ y)`. Rewrite using `[avg_conj_coef_ge_lemma_2 hρ, mul_inv_cancel, hρ.one]`. Both sides reduce to the same expression. Use `conv_lhs => rw [e]`. Conclude with `avg_conj_coef_ge_lemma hρ g x _`.
-/
private theorem avg_conj_coef_ge_lemma_3 {Γ : Type} [Group Γ] [TopologicalSpace Γ] {B : Type}
    [NormedAddCommGroup B] [InnerProductSpace ℂ B] {ρ : Γ → (B →L[ℂ] B)} (hρ : IsU ρ)
    (g : Γ) (x y : B) : ⟪ρ g x, y⟫_ℂ = ⟪x, ρ g⁻¹ y⟫_ℂ := by
  have e : y = ρ g (ρ g⁻¹ y) := by
    rw [avg_conj_coef_ge_lemma_2 hρ, mul_inv_cancel, hρ.one]; rfl
  conv_lhs => rw [e]
  exact avg_conj_coef_ge_lemma hρ g x _

/- English proof (translation)
Introduce `Γ _ _ _ _ _ _ _ ν _ _ A B _ _ _ _ _ _ σ ρ d hσ hρ hFd w₀ hw₀ hc i hi z`. Take `⟨hd, hFd'⟩` from `hFd`. Establish `hmap : ∀ g x, i (σ g x) = ρ g (i x)` using `hi.1`. Establish `hiso : ∀ x, ‖i x‖ = ‖x‖` using `hi.2`. Use `set f : Γ → ℂ := fun g => star ⟪w₀, σ g w₀⟫_ℂ with hf`.

Use `set T := coefOp ν ρ hρ f hc with hT`. Establish `hw1 : ⟪w₀, w₀⟫_ℂ = 1`. Rewrite using `[inner_self_eq_norm_sq_to_K, hw₀]`. Simplify using the standard rewrite rules. Use `set a := ContinuousLinearMap.adjoint i z with ha`.

Establish `hA : ⟪i w₀, T z⟫_ℂ = ⟪i w₀, z⟫_ℂ / (d : ℂ)`. Rewrite using `[hT, inner_coefOp]`. Establish `hpt : ∀ g, f g * ⟪i w₀, ρ g z⟫_ℂ = ⟪w₀, σ g a⟫_ℂ * star ⟪w₀, σ g w₀⟫_ℂ`. Introduce `g`. Establish `e1 : ⟪i w₀, ρ g z⟫_ℂ = ⟪w₀, σ g a⟫_ℂ`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[avg_conj_coef_ge_lemma_3 hρ, inv_inv]`. Use `_ = ⟪i (σ g⁻¹ w₀), z⟫_ℂ := by rw [hmap]`. Use `_ = ⟪σ g⁻¹ w₀, a⟫_ℂ := by rw [ha, ContinuousLinearMap.adjoint_inner_right]`. Use `_ = ⟪w₀, σ g a⟫_ℂ := by rw [avg_conj_coef_ge_lemma_3 hσ, inv_inv]`.

Rewrite using `[e1, hf, mul_comm]`. Repeatedly rewrite using `[hpt]`. Rewrite using `[(hFd' a w₀ w₀ w₀).2, hw1, mul_one, ha, ContinuousLinearMap.adjoint_inner_right]`. Establish `hB1 : ∀ g, ⟪ρ g z, T z⟫_ℂ = ∫ k, f (g * k) * ⟪z, ρ k z⟫_ℂ ∂ν`. Introduce `g`.

Rewrite using `[hT, inner_coefOp]`. Establish `e : ∀ h, f h * ⟪ρ g z, ρ h z⟫_ℂ = f (g * (g⁻¹ * h)) * ⟪z, ρ (g⁻¹ * h) z⟫_ℂ`. Introduce `h`. Rewrite using `[mul_inv_cancel_left, avg_conj_coef_ge_lemma_3 hρ, avg_conj_coef_ge_lemma_2 hρ]`. Repeatedly rewrite using `[e]`.

Conclude with `integral_mul_left_eq_self (fun k => f (g * k) * ⟪z, ρ k z⟫_ℂ) g⁻¹`. Use `set φ : Γ → ℂ := fun k => ⟪z, ρ k z⟫_ℂ with hφ`. Establish `hfc : Continuous f` using `(continuous_const.inner (hσ.cont w₀)).star`. Establish `hφc : Continuous φ` using `continuous_const.inner (hρ.cont z)`. Establish `hφb : ∀ k, ‖φ k‖ ≤ ‖z‖ ^ 2`.

Introduce `k`. Combine the equalities or inequalities in the displayed calculation. Establish `hcs : Integrable (fun g => star (f g)) ν` using `hc.mono (hfc.star.aestronglyMeasurable) (ae_of_all _ fun g => by rw [norm_star])`. Establish `hG : Integrable (fun p : Γ × Γ => f p.1 * star (f (p.1 * p.2))) (ν.prod ν)`. Establish `h0 : Integrable (fun p : Γ × Γ => f p.1 * star (f p.2)) (ν.prod ν)` using `hc.mul_prod hcs`.

Conclude with `(measurePreserving_prod_mul ν ν).integrable_comp_of_integrable h0`. Establish `hF : Integrable (Function.uncurry fun g k => f g * (star (f (g * k)) * star (φ k))) (ν.prod ν)`. Use `Integrable.mono' (hG.norm.mul_const (‖z‖ ^ 2)) ?_ (ae_of_all _ fun p => ?_)` and prove the remaining obligations. Conclude with `(show Continuous (fun p : Γ × Γ => f p.1 * (star (f (p.1 * p.2)) * star (φ p.2))) from (hfc.comp continuous_fst).mul (((hfc.comp (continuous_fst.mul continuous_snd)).star).mul ((hφc.comp continuous_snd).star))).aestronglyMeasurable`. Use `show ‖f p.1 * (star (f (p.1 * p.2)) * star (φ p.2))‖ ≤ ‖f p.1 * star (f (p.1 * p.2))‖ * ‖z‖ ^ 2`.

Simplify using `only [norm_mul, norm_star]`. Rewrite using `[mul_assoc]`. Conclude with `mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hφb _) (norm_nonneg _)) (norm_nonneg _)`. Establish `hinner : ∀ k, ∫ g, f g * star (f (g * k)) ∂ν = star (f k) / (d : ℂ)`. Introduce `k`.

Establish `e : ∀ g, f g * star (f (g * k)) = ⟪w₀, σ g (σ k w₀)⟫_ℂ * star ⟪w₀, σ g w₀⟫_ℂ`. Introduce `g`. Simplify using `only [hf, star_star]`. Rewrite using `[← avg_conj_coef_ge_lemma_2 hσ]`. Expand and normalize the polynomial expressions, which then agree.

Repeatedly rewrite using `[e]`. Rewrite using `[(hFd' (σ k w₀) w₀ w₀ w₀).2, hw1, mul_one]`. Simplify using `only [hf, star_star]`. Establish `hB2 : ⟪T z, T z⟫_ℂ = star ⟪z, T z⟫_ℂ / (d : ℂ)`. Establish `s1 : ⟪T z, T z⟫_ℂ = ∫ g, f g * ⟪T z, ρ g z⟫_ℂ ∂ν` using `inner_coefOp ν ρ hρ f hc (T z) z`.

Establish `s2 : ∀ g, f g * ⟪T z, ρ g z⟫_ℂ = ∫ k, f g * (star (f (g * k)) * star (φ k)) ∂ν`. Introduce `g`. Rewrite using `[← inner_conj_symm, hB1 g, ← integral_conj, ← integral_const_mul]`. Simplify using `only [map_mul, starRingEnd_apply, hφ]`. Establish `s3 : ∀ k, ∫ g, f g * (star (f (g * k)) * star (φ k)) ∂ν = star (f k) / (d : ℂ) * star (φ k)`.

Introduce `k`. Repeatedly rewrite using `[← mul_assoc]`. Rewrite using `[integral_mul_const, hinner k]`. Establish `s4 : ⟪z, T z⟫_ℂ = ∫ k, f k * φ k ∂ν` using `inner_coefOp ν ρ hρ f hc z z`. Establish `s5 : ∀ k, star (f k) / (d : ℂ) * star (φ k) = (starRingEnd ℂ) (f k * φ k) / (d : ℂ)`.

Introduce `k`. Rewrite using `[map_mul, starRingEnd_apply, starRingEnd_apply]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[s1]`. Repeatedly rewrite using `[s2]`.

Rewrite using `[integral_integral_swap hF]`. Repeatedly rewrite using `[s3, s5]`. Rewrite using `[integral_div, integral_conj, ← s4, starRingEnd_apply]`. Establish `hTn : ⟪T z, T z⟫_ℂ = ((‖T z‖ ^ 2 : ℝ) : ℂ)`. Rewrite using `[inner_self_eq_norm_sq_to_K]`.

Use `push_cast`. Both sides reduce to the same expression. Establish `hdC : (d : ℂ) ≠ 0` using `by exact_mod_cast hd.ne'`. Establish `hX : star ⟪z, T z⟫_ℂ = ((d * ‖T z‖ ^ 2 : ℝ) : ℂ)`. Establish `h` using `hB2.symm.trans hTn`.

Rewrite `h` using `[div_eq_iff hdC]`. Rewrite using `[h]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hre : (⟪z, T z⟫_ℂ).re = d * ‖T z‖ ^ 2`.

Establish `h` using `congrArg Complex.re hX`. Rewrite `h` using `[Complex.ofReal_re]`. Rewrite using `[← h]`. Conclude with `(Complex.conj_re _).symm`. Establish `hle : ‖⟪z, i w₀⟫_ℂ‖ ≤ d * ‖T z‖`.

Establish `h1' : ‖⟪i w₀, T z⟫_ℂ‖ ≤ ‖T z‖`. Combine the equalities or inequalities in the displayed calculation. Establish `h2' : ‖⟪z, i w₀⟫_ℂ‖ = d * ‖⟪i w₀, T z⟫_ℂ‖`. Rewrite using `[hA, norm_div, norm_inner_symm, Complex.norm_real, Real.norm_of_nonneg hd.le]`. Clear the denominators using the available nonvanishing facts.

Rewrite using `[h2']`. Conclude with `mul_le_mul_of_nonneg_left h1' hd.le`. Rewrite using `[hre, div_le_iff₀ hd]`. Establish `hsq : ‖⟪z, i w₀⟫_ℂ‖ ^ 2 ≤ (d * ‖T z‖) ^ 2` using `pow_le_pow_left₀ (norm_nonneg _) hle 2`. Use polynomial arithmetic with `[hsq]`.
-/
theorem avg_conj_coef_ge : ∀ {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [LocallyCompactSpace Γ]
    [SecondCountableTopology Γ] [MeasurableSpace Γ] [BorelSpace Γ] (ν : Measure Γ) [ν.IsHaarMeasure] [ν.IsMulRightInvariant] {A B : Type} [NormedAddCommGroup A] [InnerProductSpace ℂ A] [CompleteSpace A] [NormedAddCommGroup B]
    [InnerProductSpace ℂ B] [CompleteSpace B] (σ : Γ → (A →L[ℂ] A)) (ρ : Γ → (B →L[ℂ] B)) (d : ℝ) (hσ : IsU σ) (hρ : IsU ρ), IsFd ν σ d →
    ∀ w₀ : A, ‖w₀‖ = 1 → ∀ (hc : Integrable (fun g => star ⟪w₀, σ g w₀⟫_ℂ) ν) (i : A →L[ℂ] B), IsIsoMap σ ρ i → ∀ z : B,
    ‖⟪z, i w₀⟫_ℂ‖ ^ 2 / d ≤ (⟪z, coefOp ν ρ hρ (fun g => star ⟪w₀, σ g w₀⟫_ℂ) hc z⟫_ℂ).re := by
  intro Γ _ _ _ _ _ _ _ ν _ _ A B _ _ _ _ _ _ σ ρ d hσ hρ hFd w₀ hw₀ hc i hi z
  obtain ⟨hd, hFd'⟩ := hFd
  have hmap : ∀ g x, i (σ g x) = ρ g (i x) := hi.1
  have hiso : ∀ x, ‖i x‖ = ‖x‖ := hi.2
  set f : Γ → ℂ := fun g => star ⟪w₀, σ g w₀⟫_ℂ with hf
  set T := coefOp ν ρ hρ f hc with hT
  have hw1 : ⟪w₀, w₀⟫_ℂ = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hw₀]; simp
  set a := ContinuousLinearMap.adjoint i z with ha
  have hA : ⟪i w₀, T z⟫_ℂ = ⟪i w₀, z⟫_ℂ / (d : ℂ) := by
    rw [hT, inner_coefOp]
    have hpt : ∀ g, f g * ⟪i w₀, ρ g z⟫_ℂ = ⟪w₀, σ g a⟫_ℂ * star ⟪w₀, σ g w₀⟫_ℂ := by
      intro g
      have e1 : ⟪i w₀, ρ g z⟫_ℂ = ⟪w₀, σ g a⟫_ℂ := by
        calc ⟪i w₀, ρ g z⟫_ℂ = ⟪ρ g⁻¹ (i w₀), z⟫_ℂ := by
              rw [avg_conj_coef_ge_lemma_3 hρ, inv_inv]
          _ = ⟪i (σ g⁻¹ w₀), z⟫_ℂ := by rw [hmap]
          _ = ⟪σ g⁻¹ w₀, a⟫_ℂ := by rw [ha, ContinuousLinearMap.adjoint_inner_right]
          _ = ⟪w₀, σ g a⟫_ℂ := by rw [avg_conj_coef_ge_lemma_3 hσ, inv_inv]
      rw [e1, hf, mul_comm]
    simp_rw [hpt]
    rw [(hFd' a w₀ w₀ w₀).2, hw1, mul_one, ha, ContinuousLinearMap.adjoint_inner_right]
  have hB1 : ∀ g, ⟪ρ g z, T z⟫_ℂ = ∫ k, f (g * k) * ⟪z, ρ k z⟫_ℂ ∂ν := by
    intro g
    rw [hT, inner_coefOp]
    have e : ∀ h, f h * ⟪ρ g z, ρ h z⟫_ℂ = f (g * (g⁻¹ * h)) * ⟪z, ρ (g⁻¹ * h) z⟫_ℂ := by
      intro h
      rw [mul_inv_cancel_left, avg_conj_coef_ge_lemma_3 hρ, avg_conj_coef_ge_lemma_2 hρ]
    simp_rw [e]
    exact integral_mul_left_eq_self (fun k => f (g * k) * ⟪z, ρ k z⟫_ℂ) g⁻¹
  set φ : Γ → ℂ := fun k => ⟪z, ρ k z⟫_ℂ with hφ
  have hfc : Continuous f := (continuous_const.inner (hσ.cont w₀)).star
  have hφc : Continuous φ := continuous_const.inner (hρ.cont z)
  have hφb : ∀ k, ‖φ k‖ ≤ ‖z‖ ^ 2 := by
    intro k
    calc ‖φ k‖ ≤ ‖z‖ * ‖ρ k z‖ := norm_inner_le_norm _ _
      _ = ‖z‖ ^ 2 := by rw [hρ.norm, sq]
  have hcs : Integrable (fun g => star (f g)) ν :=
    hc.mono (hfc.star.aestronglyMeasurable) (ae_of_all _ fun g => by rw [norm_star])
  have hG : Integrable (fun p : Γ × Γ => f p.1 * star (f (p.1 * p.2))) (ν.prod ν) := by
    have h0 : Integrable (fun p : Γ × Γ => f p.1 * star (f p.2)) (ν.prod ν) := hc.mul_prod hcs
    exact (measurePreserving_prod_mul ν ν).integrable_comp_of_integrable h0
  have hF : Integrable (Function.uncurry fun g k => f g * (star (f (g * k)) * star (φ k))) (ν.prod ν) := by
    refine Integrable.mono' (hG.norm.mul_const (‖z‖ ^ 2)) ?_ (ae_of_all _ fun p => ?_)
    · exact (show Continuous (fun p : Γ × Γ => f p.1 * (star (f (p.1 * p.2)) * star (φ p.2))) from
        (hfc.comp continuous_fst).mul (((hfc.comp (continuous_fst.mul continuous_snd)).star).mul
          ((hφc.comp continuous_snd).star))).aestronglyMeasurable
    · show ‖f p.1 * (star (f (p.1 * p.2)) * star (φ p.2))‖ ≤ ‖f p.1 * star (f (p.1 * p.2))‖ * ‖z‖ ^ 2
      simp only [norm_mul, norm_star]
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hφb _) (norm_nonneg _)) (norm_nonneg _)
  have hinner : ∀ k, ∫ g, f g * star (f (g * k)) ∂ν = star (f k) / (d : ℂ) := by
    intro k
    have e : ∀ g, f g * star (f (g * k)) = ⟪w₀, σ g (σ k w₀)⟫_ℂ * star ⟪w₀, σ g w₀⟫_ℂ := by
      intro g
      simp only [hf, star_star]
      rw [← avg_conj_coef_ge_lemma_2 hσ]
      ring
    simp_rw [e]
    rw [(hFd' (σ k w₀) w₀ w₀ w₀).2, hw1, mul_one]
    simp only [hf, star_star]
  have hB2 : ⟪T z, T z⟫_ℂ = star ⟪z, T z⟫_ℂ / (d : ℂ) := by
    have s1 : ⟪T z, T z⟫_ℂ = ∫ g, f g * ⟪T z, ρ g z⟫_ℂ ∂ν := inner_coefOp ν ρ hρ f hc (T z) z
    have s2 : ∀ g, f g * ⟪T z, ρ g z⟫_ℂ = ∫ k, f g * (star (f (g * k)) * star (φ k)) ∂ν := by
      intro g
      rw [← inner_conj_symm, hB1 g, ← integral_conj, ← integral_const_mul]
      simp only [map_mul, starRingEnd_apply, hφ]
    have s3 : ∀ k, ∫ g, f g * (star (f (g * k)) * star (φ k)) ∂ν = star (f k) / (d : ℂ) * star (φ k) := by
      intro k
      simp_rw [← mul_assoc]
      rw [integral_mul_const, hinner k]
    have s4 : ⟪z, T z⟫_ℂ = ∫ k, f k * φ k ∂ν := inner_coefOp ν ρ hρ f hc z z
    have s5 : ∀ k, star (f k) / (d : ℂ) * star (φ k) = (starRingEnd ℂ) (f k * φ k) / (d : ℂ) := by
      intro k
      rw [map_mul, starRingEnd_apply, starRingEnd_apply]
      ring
    rw [s1]
    simp_rw [s2]
    rw [integral_integral_swap hF]
    simp_rw [s3, s5]
    rw [integral_div, integral_conj, ← s4, starRingEnd_apply]
  have hTn : ⟪T z, T z⟫_ℂ = ((‖T z‖ ^ 2 : ℝ) : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K]
    push_cast
    rfl
  have hdC : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  have hX : star ⟪z, T z⟫_ℂ = ((d * ‖T z‖ ^ 2 : ℝ) : ℂ) := by
    have h := hB2.symm.trans hTn
    rw [div_eq_iff hdC] at h
    rw [h]
    push_cast
    ring
  have hre : (⟪z, T z⟫_ℂ).re = d * ‖T z‖ ^ 2 := by
    have h := congrArg Complex.re hX
    rw [Complex.ofReal_re] at h
    rw [← h]
    exact (Complex.conj_re _).symm
  have hle : ‖⟪z, i w₀⟫_ℂ‖ ≤ d * ‖T z‖ := by
    have h1' : ‖⟪i w₀, T z⟫_ℂ‖ ≤ ‖T z‖ := by
      calc ‖⟪i w₀, T z⟫_ℂ‖ ≤ ‖i w₀‖ * ‖T z‖ := norm_inner_le_norm _ _
        _ = ‖T z‖ := by rw [hiso, hw₀, one_mul]
    have h2' : ‖⟪z, i w₀⟫_ℂ‖ = d * ‖⟪i w₀, T z⟫_ℂ‖ := by
      rw [hA, norm_div, norm_inner_symm, Complex.norm_real, Real.norm_of_nonneg hd.le]
      field_simp
    rw [h2']
    exact mul_le_mul_of_nonneg_left h1' hd.le
  rw [hre, div_le_iff₀ hd]
  have hsq : ‖⟪z, i w₀⟫_ℂ‖ ^ 2 ≤ (d * ‖T z‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hle 2
  nlinarith [hsq]

end GlobalTheory.CompanionTheory.RgHeA
