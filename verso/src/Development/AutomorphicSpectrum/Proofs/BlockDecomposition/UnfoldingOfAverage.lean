import Mathlib
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.MirabolicGenerators.SideUnfold

noncomputable section

open MeasureTheory Filter Topology
open PositivityTheory.RgEis PositivityTheory.RgEis.MG

namespace GlobalTheory.CompanionTheory.RgEisUnfold

section SlopeTestRemainingChoices

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]
  {K : Subgroup G} [CompactSpace K] [MeasurableSpace K] [BorelSpace K]

/- English proof (translation)
The claim follows from `hF.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)`.
-/
theorem integrable_of_continuous (μ : Measure K) [IsProbabilityMeasure μ] {F : K → (W →L[ℂ] W)}
    (hF : Continuous F) : Integrable F μ :=
  hF.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/- English proof (translation)
Use `haveI : CompleteSpace W := FiniteDimensional.complete ℂ W`. Take `⟨C, hC⟩` from `isCompact_univ.exists_bound_of_continuousOn hρ.continuousOn`. Establish `hint : ∀ f : C(K, ℂ), Integrable (fun κ => f κ • ρ κ) μ` using `fun f => integrable_of_continuous μ (f.continuous.smul hρ)`. Set `A₀ : C(K, ℂ) →ₗ[ℂ] (W →L[ℂ] W)` to `{ toFun := fun f => avg μ ρ f map_add' := fun f g => by`. Simplify using `only [avg, ContinuousMap.coe_add, Pi.add_apply, add_smul]`.

Conclude with `integral_add (hint f) (hint g)`. Use the proof step `map_smul' := fun a f => by`. Simplify using `only [avg, ContinuousMap.coe_smul, Pi.smul_apply, smul_eq_mul, mul_smul, RingHom.id_apply]`. Conclude with `integral_smul a _ }`. Use `⟨A₀.mkContinuous C fun f => ?_, fun f => rfl⟩` and prove the remaining obligations.

Establish `h : ∀ᵐ κ ∂μ, ‖f κ • ρ κ‖ ≤ C * ‖f‖` using `Eventually.of_forall fun κ => by`. Rewrite using `[norm_smul, mul_comm]`. Conclude with `mul_le_mul (hC κ (Set.mem_univ _)) (f.norm_coe_le_norm κ) (norm_nonneg _) ((norm_nonneg _).trans (hC κ (Set.mem_univ _)))`. Use `norm_integral_le_of_norm_le_const h` as an intermediate fact. Simplify `this` using `[avg, A₀]`.
-/
theorem exists_avgCLM (μ : Measure K) [IsProbabilityMeasure μ] {ρ : K →* (W →L[ℂ] W)}
    (hρ : Continuous ρ) :
    ∃ A : C(K, ℂ) →L[ℂ] (W →L[ℂ] W), ∀ f : C(K, ℂ), A f = avg μ ρ f := by
  haveI : CompleteSpace W := FiniteDimensional.complete ℂ W
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hρ.continuousOn
  have hint : ∀ f : C(K, ℂ), Integrable (fun κ => f κ • ρ κ) μ := fun f =>
    integrable_of_continuous μ (f.continuous.smul hρ)
  let A₀ : C(K, ℂ) →ₗ[ℂ] (W →L[ℂ] W) :=
    { toFun := fun f => avg μ ρ f
      map_add' := fun f g => by
        simp only [avg, ContinuousMap.coe_add, Pi.add_apply, add_smul]
        exact integral_add (hint f) (hint g)
      map_smul' := fun a f => by
        simp only [avg, ContinuousMap.coe_smul, Pi.smul_apply, smul_eq_mul, mul_smul,
          RingHom.id_apply]
        exact integral_smul a _ }
  refine ⟨A₀.mkContinuous C fun f => ?_, fun f => rfl⟩
  have h : ∀ᵐ κ ∂μ, ‖f κ • ρ κ‖ ≤ C * ‖f‖ := Eventually.of_forall fun κ => by
    rw [norm_smul, mul_comm]
    exact mul_le_mul (hC κ (Set.mem_univ _)) (f.norm_coe_le_norm κ) (norm_nonneg _)
      ((norm_nonneg _).trans (hC κ (Set.mem_univ _)))
  have := norm_integral_le_of_norm_le_const h
  simpa [avg, A₀] using this

/- English proof (translation)
Use `haveI : CompleteSpace W := FiniteDimensional.complete ℂ W`. Establish `hc : Continuous fun κ : K => κ₁ * κ` using `continuous_const.mul continuous_id`. Establish `hI : Integrable (fun κ => φ (κ₁ * κ) • ρ (κ₁ * κ)) μ` using `integrable_of_continuous μ ((hφ.comp hc).smul (hρ.comp hc))`. Establish `h1 : avg μ ρ φ = ∫ κ, φ (κ₁ * κ) • ρ (κ₁ * κ) ∂μ` using `(integral_mul_left_eq_self (fun κ => φ κ • ρ κ) κ₁).symm`. Establish `h2` using `ContinuousLinearMap.integral_comp_comm (ContinuousLinearMap.compL ℂ W W W (ρ κ₁⁻¹)) hI`.

Rewrite using `[h1]`. Use `Eq.trans ?_ h2` and prove the remaining obligations. Unfold `avg`. Use `integral_congr_ae (Eventually.of_forall fun κ => ?_)` and prove the remaining obligations. Establish `h3 : (ρ κ₁⁻¹).comp (ρ (κ₁ * κ)) = ρ κ`.

Express the relevant statement in the definitionally equal form `ρ κ₁⁻¹ * ρ (κ₁ * κ) = ρ κ`. Rewrite using `[← map_mul, inv_mul_cancel_left]`. Express the relevant statement in the definitionally equal form `φ (κ₁ * κ) • ρ κ = ContinuousLinearMap.compL ℂ W W W (ρ κ₁⁻¹) (φ (κ₁ * κ) • ρ (κ₁ * κ))`. Rewrite using `[map_smul, ContinuousLinearMap.compL_apply, h3]`.
-/
theorem avg_translate (μ : Measure K) [μ.IsHaarMeasure] [IsProbabilityMeasure μ]
    {ρ : K →* (W →L[ℂ] W)} (hρ : Continuous ρ) {φ : K → ℂ} (hφ : Continuous φ) (κ₁ : K) :
    avg μ ρ (fun κ => φ (κ₁ * κ)) = ρ κ₁⁻¹ * avg μ ρ φ := by
  haveI : CompleteSpace W := FiniteDimensional.complete ℂ W
  have hc : Continuous fun κ : K => κ₁ * κ := continuous_const.mul continuous_id
  have hI : Integrable (fun κ => φ (κ₁ * κ) • ρ (κ₁ * κ)) μ :=
    integrable_of_continuous μ ((hφ.comp hc).smul (hρ.comp hc))
  have h1 : avg μ ρ φ = ∫ κ, φ (κ₁ * κ) • ρ (κ₁ * κ) ∂μ :=
    (integral_mul_left_eq_self (fun κ => φ κ • ρ κ) κ₁).symm
  have h2 := ContinuousLinearMap.integral_comp_comm
    (ContinuousLinearMap.compL ℂ W W W (ρ κ₁⁻¹)) hI
  rw [h1]
  refine Eq.trans ?_ h2
  unfold avg
  refine integral_congr_ae (Eventually.of_forall fun κ => ?_)
  have h3 : (ρ κ₁⁻¹).comp (ρ (κ₁ * κ)) = ρ κ := by
    change ρ κ₁⁻¹ * ρ (κ₁ * κ) = ρ κ
    rw [← map_mul, inv_mul_cancel_left]
  change φ (κ₁ * κ) • ρ κ = ContinuousLinearMap.compL ℂ W W W (ρ κ₁⁻¹) (φ (κ₁ * κ) • ρ (κ₁ * κ))
  rw [map_smul, ContinuousLinearMap.compL_apply, h3]

end SlopeTestRemainingChoices

/- English proof (translation)
Introduce `hSec hAvg G _ _ _ _ _ W _ _ _ K ρ hK hρ _ _ μ hμ hpr Γ P c hpar φ Λ T hφ hLaw hΛ hT g u hu hb w`. Use `haveI : CompactSpace K := isCompact_iff_compactSpace.mp hK`. Use `haveI : CompleteSpace W := FiniteDimensional.complete ℂ W`. Establish `hsec` using `(hSec G W K ρ hK hρ Γ P c hpar).1`. Establish `hmem` using `hAvg G W K ρ hK hρ μ hμ hpr Γ P c hpar φ hφ hLaw w`.

Establish `key : ∀ q : Cos P Γ, ∃ (p : G) (κ₁ : K), p ∈ P ∧ rep q * g = p * κ₁` using `fun q => by`. Take `⟨p, hp, k, hk, e⟩` from `hpar.iwa (rep q * g)`. Conclude with `⟨p, ⟨k, hk⟩, hp, e⟩`. Use `choose p κ₁ hp hpk using key`. Establish `hterm : ∀ q (κ : K), T (rep q * (g * κ)) = (c (p q) * Complex.exp (Λ (p q))) * φ (κ₁ q * κ)` using `fun q κ => by`.

Establish `e : rep q * (g * (κ : G)) = p q * ((κ₁ q * κ : K) : G)`. Rewrite using `[← mul_assoc, hpk q, Subgroup.coe_mul, mul_assoc]`. Rewrite using `[e]`. Conclude with `hT _ (hp q) _`. Establish `hc : ∀ q, Continuous fun κ : K => φ (κ₁ q * κ)` using `fun q => hφ.comp (continuous_const.mul continuous_id)`.

Set `f' : Cos P Γ → C(K, ℂ)` to `fun q => ⟨fun κ => φ (κ₁ q * κ), hc q⟩`. Set `f : Cos P Γ → C(K, ℂ)` to `fun q => (c (p q) * Complex.exp (Λ (p q))) • f' q`. Establish `hfa : ∀ q κ, f q κ = T (rep q * (g * κ))` using `fun q κ => by`. Rewrite using `[hterm]`. Simplify using `[f, f']`.

Establish `hu0 : ∀ q, 0 ≤ u q` using `fun q => (norm_nonneg _).trans (hb q 1)`. Establish `hsum : Summable f` using `Summable.of_norm_bounded hu fun q => (ContinuousMap.norm_le _ (hu0 q)).2 fun κ => by`. Rewrite using `[hfa]`. Conclude with `hb q κ`. Take `⟨A, hA⟩` from `exists_avgCLM μ hρ`.

Establish `hF : (fun κ : K => ∑' q : Cos P Γ, T (rep q * (g * κ))) = ⇑(∑' q, f q)`. Use function extensionality and compare the values at `κ`. Rewrite using `[← ContinuousMap.tsum_apply hsum]`. Conclude with `tsum_congr fun q => (hfa q κ).symm`. Rewrite using `[hF, ← hA]`.

Establish `hL` using `((ContinuousLinearMap.apply ℂ W w).comp A).map_tsum hsum`. Simplify using `only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply] at hL`. Rewrite using `[hL]`. Unfold `eis`. Use `tsum_congr fun q => ?_` and prove the remaining obligations.

Establish `e1 : A (f q) w = (c (p q) * Complex.exp (Λ (p q))) • (ρ (κ₁ q)⁻¹ (avg μ ρ φ w))`. Establish `: A (f' q) = ρ (κ₁ q)⁻¹ * avg μ ρ φ`. Rewrite using `[hA]`. Conclude with `avg_translate μ hρ hφ (κ₁ q)`. Establish `e2 : A (f q) = (c (p q) * Complex.exp (Λ (p q))) • A (f' q)` using `map_smul A _ _`.

Rewrite using `[e2, this]`. Both sides reduce to the same expression. Rewrite using `[e1, hpk q, hΛ _ _ (κ₁ q).2, hsec _ hmem _ (hp q), smul_smul, mul_comm]`.
-/
theorem unfold : SecLaw → AvgMem → Unfold := by
  intro hSec hAvg G _ _ _ _ _ W _ _ _ K ρ hK hρ _ _ μ hμ hpr Γ P c hpar φ Λ T hφ hLaw hΛ hT g u hu
    hb w
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  haveI : CompleteSpace W := FiniteDimensional.complete ℂ W
  have hsec := (hSec G W K ρ hK hρ Γ P c hpar).1
  have hmem := hAvg G W K ρ hK hρ μ hμ hpr Γ P c hpar φ hφ hLaw w
  have key : ∀ q : Cos P Γ, ∃ (p : G) (κ₁ : K), p ∈ P ∧ rep q * g = p * κ₁ := fun q => by
    obtain ⟨p, hp, k, hk, e⟩ := hpar.iwa (rep q * g)
    exact ⟨p, ⟨k, hk⟩, hp, e⟩
  choose p κ₁ hp hpk using key
  have hterm : ∀ q (κ : K), T (rep q * (g * κ)) =
      (c (p q) * Complex.exp (Λ (p q))) * φ (κ₁ q * κ) := fun q κ => by
    have e : rep q * (g * (κ : G)) = p q * ((κ₁ q * κ : K) : G) := by
      rw [← mul_assoc, hpk q, Subgroup.coe_mul, mul_assoc]
    rw [e]
    exact hT _ (hp q) _
  have hc : ∀ q, Continuous fun κ : K => φ (κ₁ q * κ) := fun q =>
    hφ.comp (continuous_const.mul continuous_id)
  let f' : Cos P Γ → C(K, ℂ) := fun q => ⟨fun κ => φ (κ₁ q * κ), hc q⟩
  let f : Cos P Γ → C(K, ℂ) := fun q => (c (p q) * Complex.exp (Λ (p q))) • f' q
  have hfa : ∀ q κ, f q κ = T (rep q * (g * κ)) := fun q κ => by
    rw [hterm]
    simp [f, f']
  have hu0 : ∀ q, 0 ≤ u q := fun q => (norm_nonneg _).trans (hb q 1)
  have hsum : Summable f := Summable.of_norm_bounded hu fun q =>
    (ContinuousMap.norm_le _ (hu0 q)).2 fun κ => by
      rw [hfa]
      exact hb q κ
  obtain ⟨A, hA⟩ := exists_avgCLM μ hρ
  have hF : (fun κ : K => ∑' q : Cos P Γ, T (rep q * (g * κ))) = ⇑(∑' q, f q) := by
    funext κ
    rw [← ContinuousMap.tsum_apply hsum]
    exact tsum_congr fun q => (hfa q κ).symm
  rw [hF, ← hA]
  have hL := ((ContinuousLinearMap.apply ℂ W w).comp A).map_tsum hsum
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply] at hL
  rw [hL]
  unfold eis
  refine tsum_congr fun q => ?_
  have e1 : A (f q) w = (c (p q) * Complex.exp (Λ (p q))) • (ρ (κ₁ q)⁻¹ (avg μ ρ φ w)) := by
    have : A (f' q) = ρ (κ₁ q)⁻¹ * avg μ ρ φ := by
      rw [hA]
      exact avg_translate μ hρ hφ (κ₁ q)
    have e2 : A (f q) = (c (p q) * Complex.exp (Λ (p q))) • A (f' q) := map_smul A _ _
    rw [e2, this]
    rfl
  rw [e1, hpk q, hΛ _ _ (κ₁ q).2, hsec _ hmem _ (hp q), smul_smul, mul_comm]

end GlobalTheory.CompanionTheory.RgEisUnfold
