import Mathlib

open MeasureTheory
open scoped InnerProductSpace

namespace GlobalTheory

/- English proof (translation)
Set `L : Hp →ₗᵢ[ℂ] Hp` to `{ toLinearMap := (π a : Hp →ₗ[ℂ] Hp), norm_map' := hiso a }`. Establish `hback : π a (π a⁻¹ w) = w`. Rewrite using `[← ContinuousLinearMap.mul_apply, ← map_mul, mul_inv_cancel, map_one, ContinuousLinearMap.one_apply]`. Establish `hL : ⟪L u, L (π a⁻¹ w)⟫_ℂ = ⟪u, π a⁻¹ w⟫_ℂ` using `L.inner_map_map _ _`. Rewrite using `[← hL]`.

Use `show ⟪π a u, w⟫_ℂ = ⟪π a u, π a (π a⁻¹ w)⟫_ℂ`. Rewrite using `[hback]`.
-/
private lemma inner_apply_eq_inner_apply_inv_of_isometric {G : Type} [Group G] {Hp : Type} [NormedAddCommGroup Hp]
    [InnerProductSpace ℂ Hp] (π : G →* (Hp →L[ℂ] Hp)) (hiso : ∀ g x, ‖π g x‖ = ‖x‖)
    (a : G) (u w : Hp) : ⟪π a u, w⟫_ℂ = ⟪u, π a⁻¹ w⟫_ℂ := by

  let L : Hp →ₗᵢ[ℂ] Hp := { toLinearMap := (π a : Hp →ₗ[ℂ] Hp), norm_map' := hiso a }
  have hback : π a (π a⁻¹ w) = w := by
    rw [← ContinuousLinearMap.mul_apply, ← map_mul, mul_inv_cancel, map_one,
      ContinuousLinearMap.one_apply]
  have hL : ⟪L u, L (π a⁻¹ w)⟫_ℂ = ⟪u, π a⁻¹ w⟫_ℂ := L.inner_map_map _ _
  rw [← hL]
  show ⟪π a u, w⟫_ℂ = ⟪π a u, π a (π a⁻¹ w)⟫_ℂ
  rw [hback]

/- English proof (translation)
Introduce `G _ _ _ _ _ _ μ _ _ _ _ Hp _ _ _ π hiso hcont φ m hφ hstar hconv hm1 P hP`. Establish `hsand : ∀ x : G, P ∘L π x ∘L P = m x • P`. Introduce `x`. Use `ext1 v`. Use `ext_inner_left ℂ fun u => ?_` and prove the remaining obligations.

Rewrite using `[ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply, inner_smul_right, hP, hP]`. Establish `step : ∀ g : G, ⟪u, π g (π x (P v))⟫_ℂ = ∫ k, φ (x⁻¹ * g⁻¹ * k) * ⟪u, π k v⟫_ℂ ∂μ`. Introduce `g`. Establish `e1 : ⟪u, π g (π x (P v))⟫_ℂ = ⟪π (g * x)⁻¹ u, P v⟫_ℂ`. Rewrite using `[inner_apply_eq_inner_apply_inv_of_isometric π hiso, inv_inv]`.

Simplify using `only [map_mul, ContinuousLinearMap.mul_apply]`. Establish `e2 : ∀ h : G, ⟪π (g * x)⁻¹ u, π h v⟫_ℂ = ⟪u, π (g * x * h) v⟫_ℂ`. Introduce `h`. Rewrite using `[inner_apply_eq_inner_apply_inv_of_isometric π hiso, inv_inv]`. Simplify using `only [map_mul, ContinuousLinearMap.mul_apply]`.

Rewrite using `[e1, hP]`. Repeatedly rewrite using `[e2]`. Establish `htr` using `integral_mul_left_eq_self (μ := μ) (fun h => φ h * ⟪u, π (g * x * h) v⟫_ℂ) (g * x)⁻¹`. Rewrite using `[← htr]`. Use `congr 1`.

Use function extensionality and compare the values at `k`. Rewrite using `[mul_inv_cancel_left, mul_inv_rev]`. Repeatedly rewrite using `[step]`. Establish `hshift : Integrable (fun k => φ (x⁻¹ * k)) μ` using `hφ.comp_mul_left x⁻¹`. Establish `hprod : Integrable (fun z : G × G => φ z.1 * φ (x⁻¹ * z.2)) (μ.prod μ)` using `hφ.mul_prod hshift`.

Establish `hsheared : Integrable (fun z : G × G => φ z.1 * φ (x⁻¹ * z.1⁻¹ * z.2)) (μ.prod μ)`. Establish `h` using `(measurePreserving_prod_inv_mul μ μ).integrable_comp_of_integrable hprod`. Use `h.congr (Filter.Eventually.of_forall fun z => ?_)` and prove the remaining obligations. Simplify using `only [Function.comp, mul_assoc]`. Establish `hcoef : Continuous fun k : G => ⟪u, π k v⟫_ℂ` using `continuous_const.inner (hcont v)`.

Establish `hbound : ∀ᵐ z ∂(μ.prod μ), ‖⟪u, π z.2 v⟫_ℂ‖ ≤ ‖u‖ * ‖v‖`. Use `Filter.Eventually.of_forall fun z => ?_` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Establish `hint : Integrable (Function.uncurry fun g k => φ g * (φ (x⁻¹ * g⁻¹ * k) * ⟪u, π k v⟫_ℂ)) (μ.prod μ)`. Establish `h` using `hsheared.mul_bdd (hcoef.comp continuous_snd).aestronglyMeasurable hbound`.

Use `h.congr (Filter.Eventually.of_forall fun z => ?_)` and prove the remaining obligations. Break down `z with ⟨g, k⟩` into its components or cases. Simplify using `only [Function.uncurry_apply_pair, Function.comp]`. Expand and normalize the polynomial expressions, which then agree. Combine the equalities or inequalities in the displayed calculation.

Use `congr 1`. Use function extensionality and compare the values at `g`. Rewrite using `[integral_const_mul]`. Use `_ = ∫ k, ∫ g, φ g * (φ (x⁻¹ * g⁻¹ * k) * ⟪u, π k v⟫_ℂ) ∂μ ∂μ := integral_integral_swap hint`. Use `_ = ∫ k, (m x * φ k) * ⟪u, π k v⟫_ℂ ∂μ := by`.

Use `congr 1`. Use function extensionality and compare the values at `k`. Rewrite using `[← hconv x k, ← integral_mul_const]`. Use `congr 1`. Use function extensionality and compare the values at `g`.

Expand and normalize the polynomial expressions, which then agree. Use `_ = m x * ∫ k, φ k * ⟪u, π k v⟫_ℂ ∂μ := by`. Rewrite using `[← integral_const_mul]`. Use `congr 1`. Use function extensionality and compare the values at `k`.

Expand and normalize the polynomial expressions, which then agree. Establish `hsa : IsSelfAdjoint P`. Rewrite using `[ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]`. Introduce `a b`. Use `show ⟪P a, b⟫_ℂ = ⟪a, P b⟫_ℂ`.

Rewrite using `[← inner_conj_symm (P a) b, hP b a, hP a b, ← integral_conj]`. Combine the equalities or inequalities in the displayed calculation. Use `congr 1`. Use function extensionality and compare the values at `g`. Rewrite using `[map_mul, inner_conj_symm, inner_apply_eq_inner_apply_inv_of_isometric π hiso]`.

Use `_ = ∫ g, (starRingEnd ℂ) (φ g⁻¹) * ⟪a, π g⁻¹⁻¹ b⟫_ℂ ∂μ := (integral_inv_eq_self (fun g => (starRingEnd ℂ) (φ g) * ⟪a, π g⁻¹ b⟫_ℂ) μ).symm`. Use `_ = ∫ g, φ g * ⟪a, π g b⟫_ℂ ∂μ := by`. Use `congr 1`. Use function extensionality and compare the values at `g`. Rewrite using `[inv_inv, starRingEnd_apply, hstar]`.

Establish `hidem : IsIdempotentElem P`. Establish `h` using `hsand 1`. Rewrite `h` using `[map_one, hm1, one_smul]`. Use `show P * P = P`. Use extensionality with `v`.

Establish `hv` using `DFunLike.congr_fun h v`. Simplify using `using hv`. Conclude with `⟨⟨hidem, hsa⟩, hsand⟩`.
-/
theorem integratedOperator_isStarProjection_and_sandwich :
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] [SigmaFinite μ] [μ.IsInvInvariant] (Hp : Type) [NormedAddCommGroup Hp] [InnerProductSpace ℂ Hp] [CompleteSpace Hp] (π : G →* (Hp →L[ℂ] Hp)), (∀ g x, ‖π g x‖ = ‖x‖) → (∀ x, Continuous fun g => π g x) → ∀ (φ m : G → ℂ), Integrable φ μ → (∀ g, star (φ g⁻¹) = φ g) → (∀ x y : G, ∫ g, φ g * φ (x⁻¹ * g⁻¹ * y) ∂μ = m x * φ y) → m 1 = 1 → ∀ P : Hp →L[ℂ] Hp, (∀ x y : Hp, ⟪x, P y⟫_ℂ = ∫ g, φ g * ⟪x, π g y⟫_ℂ ∂μ) → IsStarProjection P ∧ ∀ x : G, P ∘L π x ∘L P = m x • P := by
  intro G _ _ _ _ _ _ μ _ _ _ _ Hp _ _ _ π hiso hcont φ m hφ hstar hconv hm1 P hP

  have hsand : ∀ x : G, P ∘L π x ∘L P = m x • P := by
    intro x
    ext1 v
    refine ext_inner_left ℂ fun u => ?_
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.smul_apply, inner_smul_right, hP, hP]

    have step : ∀ g : G, ⟪u, π g (π x (P v))⟫_ℂ
        = ∫ k, φ (x⁻¹ * g⁻¹ * k) * ⟪u, π k v⟫_ℂ ∂μ := by
      intro g
      have e1 : ⟪u, π g (π x (P v))⟫_ℂ = ⟪π (g * x)⁻¹ u, P v⟫_ℂ := by
        rw [inner_apply_eq_inner_apply_inv_of_isometric π hiso, inv_inv]
        simp only [map_mul, ContinuousLinearMap.mul_apply]
      have e2 : ∀ h : G, ⟪π (g * x)⁻¹ u, π h v⟫_ℂ = ⟪u, π (g * x * h) v⟫_ℂ := by
        intro h
        rw [inner_apply_eq_inner_apply_inv_of_isometric π hiso, inv_inv]
        simp only [map_mul, ContinuousLinearMap.mul_apply]
      rw [e1, hP]
      simp_rw [e2]
      have htr := integral_mul_left_eq_self (μ := μ)
        (fun h => φ h * ⟪u, π (g * x * h) v⟫_ℂ) (g * x)⁻¹
      rw [← htr]
      congr 1
      funext k
      rw [mul_inv_cancel_left, mul_inv_rev]
    simp_rw [step]

    have hshift : Integrable (fun k => φ (x⁻¹ * k)) μ := hφ.comp_mul_left x⁻¹
    have hprod : Integrable (fun z : G × G => φ z.1 * φ (x⁻¹ * z.2)) (μ.prod μ) :=
      hφ.mul_prod hshift
    have hsheared : Integrable (fun z : G × G => φ z.1 * φ (x⁻¹ * z.1⁻¹ * z.2)) (μ.prod μ) := by
      have h := (measurePreserving_prod_inv_mul μ μ).integrable_comp_of_integrable hprod
      refine h.congr (Filter.Eventually.of_forall fun z => ?_)
      simp only [Function.comp, mul_assoc]
    have hcoef : Continuous fun k : G => ⟪u, π k v⟫_ℂ := continuous_const.inner (hcont v)
    have hbound : ∀ᵐ z ∂(μ.prod μ), ‖⟪u, π z.2 v⟫_ℂ‖ ≤ ‖u‖ * ‖v‖ := by
      refine Filter.Eventually.of_forall fun z => ?_
      calc ‖⟪u, π z.2 v⟫_ℂ‖ ≤ ‖u‖ * ‖π z.2 v‖ := norm_inner_le_norm _ _
        _ = ‖u‖ * ‖v‖ := by rw [hiso]
    have hint : Integrable (Function.uncurry fun g k =>
        φ g * (φ (x⁻¹ * g⁻¹ * k) * ⟪u, π k v⟫_ℂ)) (μ.prod μ) := by
      have h := hsheared.mul_bdd (hcoef.comp continuous_snd).aestronglyMeasurable hbound
      refine h.congr (Filter.Eventually.of_forall fun z => ?_)
      rcases z with ⟨g, k⟩
      simp only [Function.uncurry_apply_pair, Function.comp]
      ring
    calc ∫ g, φ g * ∫ k, φ (x⁻¹ * g⁻¹ * k) * ⟪u, π k v⟫_ℂ ∂μ ∂μ
        = ∫ g, ∫ k, φ g * (φ (x⁻¹ * g⁻¹ * k) * ⟪u, π k v⟫_ℂ) ∂μ ∂μ := by
          congr 1; funext g; rw [integral_const_mul]
      _ = ∫ k, ∫ g, φ g * (φ (x⁻¹ * g⁻¹ * k) * ⟪u, π k v⟫_ℂ) ∂μ ∂μ :=
          integral_integral_swap hint
      _ = ∫ k, (m x * φ k) * ⟪u, π k v⟫_ℂ ∂μ := by
          congr 1; funext k
          rw [← hconv x k, ← integral_mul_const]
          congr 1; funext g; ring
      _ = m x * ∫ k, φ k * ⟪u, π k v⟫_ℂ ∂μ := by
          rw [← integral_const_mul]
          congr 1; funext k; ring

  have hsa : IsSelfAdjoint P := by
    rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
    intro a b
    show ⟪P a, b⟫_ℂ = ⟪a, P b⟫_ℂ
    rw [← inner_conj_symm (P a) b, hP b a, hP a b, ← integral_conj]
    calc ∫ g, (starRingEnd ℂ) (φ g * ⟪b, π g a⟫_ℂ) ∂μ
        = ∫ g, (starRingEnd ℂ) (φ g) * ⟪a, π g⁻¹ b⟫_ℂ ∂μ := by
          congr 1; funext g; rw [map_mul, inner_conj_symm, inner_apply_eq_inner_apply_inv_of_isometric π hiso]
      _ = ∫ g, (starRingEnd ℂ) (φ g⁻¹) * ⟪a, π g⁻¹⁻¹ b⟫_ℂ ∂μ :=
          (integral_inv_eq_self (fun g => (starRingEnd ℂ) (φ g) * ⟪a, π g⁻¹ b⟫_ℂ) μ).symm
      _ = ∫ g, φ g * ⟪a, π g b⟫_ℂ ∂μ := by
          congr 1; funext g; rw [inv_inv, starRingEnd_apply, hstar]

  have hidem : IsIdempotentElem P := by
    have h := hsand 1
    rw [map_one, hm1, one_smul] at h
    show P * P = P
    ext v
    have hv := DFunLike.congr_fun h v
    simpa using hv
  exact ⟨⟨hidem, hsa⟩, hsand⟩

end GlobalTheory
