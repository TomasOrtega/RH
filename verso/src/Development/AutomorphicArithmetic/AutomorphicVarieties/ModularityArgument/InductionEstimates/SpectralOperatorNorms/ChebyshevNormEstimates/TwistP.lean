import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SpectralOperatorNorms.KillExempt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.TruncEq
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.LintegralInvUniqueHaar
import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.TwistUnitary

open MeasureTheory NumberField IsDedekindDomain MvPolynomial Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Ci PositivityTheory.Rg.Fx
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq UpperTheory.V.Z.IntegralApplyAeEq UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial
open scoped InnerProductSpace

section Abstract

variable {H V W : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [NormedAddCommGroup W] [InnerProductSpace ℂ W]

/- English proof (translation)
Establish `hQ : ∀ x, Q (Q x) = Q x` using `fun x => by`. Use `congrArg (fun A : H →L[ℂ] H => A x) hi` as an intermediate fact. Simplify using `using this`. Establish `hsym : ∀ x y, ⟪Q x, y⟫_ℂ = ⟪x, Q y⟫_ℂ` using `fun x y => hs.isSymmetric x y`. Establish `h1 : Q (U (h - Q h)) = 0` using `(hk _).2 (by rw [map_sub, hQ, sub_self])`.

Rewrite `h1` using `[map_sub, map_sub, sub_eq_zero]`. Rewrite using `[h1]`. Use `set w := U (Q h) - Q (U (Q h)) with hw`. Establish `hw0 : Q w = 0` using `by rw [hw, map_sub, hQ, sub_self]`. Establish `hw1 : Q (U.symm w) = 0` using `(hk _).1 (by simpa using hw0)`.

Establish `h2 : ⟪w, U (Q h)⟫_ℂ = 0`. Use `U.inner_map_map (U.symm w) (Q h)` as an intermediate fact. Rewrite `this` using `[U.apply_symm_apply]`. Rewrite using `[this, ← hsym, hw1, inner_zero_left]`. Establish `h3 : ⟪w, w⟫_ℂ = 0` using `by conv_lhs => rw [hw, inner_sub_right, ← hw]`.

Rewrite using `[h2, ← hsym, hw0, inner_zero_left, sub_self]`. Conclude with `sub_eq_zero.1 (inner_self_eq_zero.1 h3)`.
-/
private theorem comm_of_ker (U : H ≃ₗᵢ[ℂ] H) (Q : H →L[ℂ] H) (hs : IsSelfAdjoint Q) (hi : Q ∘L Q = Q)
    (hk : ∀ h, Q (U h) = 0 ↔ Q h = 0) (h : H) : U (Q h) = Q (U h) := by
  have hQ : ∀ x, Q (Q x) = Q x := fun x => by
    have := congrArg (fun A : H →L[ℂ] H => A x) hi
    simpa using this
  have hsym : ∀ x y, ⟪Q x, y⟫_ℂ = ⟪x, Q y⟫_ℂ := fun x y => hs.isSymmetric x y
  have h1 : Q (U (h - Q h)) = 0 := (hk _).2 (by rw [map_sub, hQ, sub_self])
  rw [map_sub, map_sub, sub_eq_zero] at h1
  rw [h1]
  set w := U (Q h) - Q (U (Q h)) with hw
  have hw0 : Q w = 0 := by rw [hw, map_sub, hQ, sub_self]
  have hw1 : Q (U.symm w) = 0 := (hk _).1 (by simpa using hw0)
  have h2 : ⟪w, U (Q h)⟫_ℂ = 0 := by
    have := U.inner_map_map (U.symm w) (Q h)
    rw [U.apply_symm_apply] at this
    rw [this, ← hsym, hw1, inner_zero_left]
  have h3 : ⟪w, w⟫_ℂ = 0 := by
    conv_lhs => rw [hw, inner_sub_right, ← hw]
    rw [h2, ← hsym, hw0, inner_zero_left, sub_self]
  exact sub_eq_zero.1 (inner_self_eq_zero.1 h3)

/- English proof (translation)
Assemble the required witnesses or components as `⟨(s.toContinuousLinearEquiv : V →L[ℂ] W).compLp u, (s.toContinuousLinearEquiv : V →L[ℂ] W).coeFn_compLp u⟩`.
-/
private theorem lift_ex (s : V ≃ₗᵢ[ℂ] W) (u : L V) : ∃ v : L W, ∀ᵐ x : ℝ, v x = s (u x) :=
  ⟨(s.toContinuousLinearEquiv : V →L[ℂ] W).compLp u, (s.toContinuousLinearEquiv : V →L[ℂ] W).coeFn_compLp u⟩

/- English proof (translation)
Take `⟨u, hu⟩` from `lift_ex s.symm v`. Conclude with `⟨u, hu.mono fun x hx => by rw [hx, s.apply_symm_apply]⟩`.
-/
private theorem lift_ex' (s : V ≃ₗᵢ[ℂ] W) (v : L W) : ∃ u : L V, ∀ᵐ x : ℝ, v x = s (u x) := by
  obtain ⟨u, hu⟩ := lift_ex s.symm v
  exact ⟨u, hu.mono fun x hx => by rw [hx, s.apply_symm_apply]⟩

/- English proof (translation)
Use `⟨fun P ⟨h1, h2, h3⟩ => comm_of_ker U P h1 h2 fun h => ?_, fun T Λ ⟨h1, h2, h3⟩ => comm_of_ker U Λ h1 h2 fun h => ?_⟩` and prove the remaining obligations. Rewrite using `[h3, h3]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨a, b⟩`. Use `⟨fun u => ?_, fun v => ?_⟩` and prove the remaining obligations.

Take `⟨v, hv⟩` from `lift_ex s u`. Rewrite using `[← U.inner_map_map, hs u v hv, b]`. Take `⟨u, hu⟩` from `lift_ex t v`. Rewrite using `[← U.inner_map_map, ht v u hu, a]`. Introduce and unpack `⟨a, b⟩`.

Use `⟨fun u => ?_, fun v => ?_⟩` and prove the remaining obligations. Take `⟨v, hv⟩` from `lift_ex' t u`. Rewrite using `[← ht v u hv, U.inner_map_map, b]`. Take `⟨u, hu⟩` from `lift_ex' s v`. Rewrite using `[← hs u v hu, U.inner_map_map, a]`.

Rewrite using `[h3, h3]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨u, v, hu, hv, e⟩`. Take `⟨v', hv'⟩` from `lift_ex' t u`. Take `⟨u', hu'⟩` from `lift_ex' s v`.

Use `⟨u', v', ?_, ?_, ?_⟩` and prove the remaining obligations. Use `filter_upwards [hv, hu'] with x a b hx`. Conclude with `s.injective (by rw [← b, a hx, map_zero])`. Use `filter_upwards [hu, hv'] with x a b hx`. Conclude with `t.injective (by rw [← b, a hx, map_zero])`.

Apply `U.injective` to reduce the goal to its premises. Rewrite using `[e, map_add, hs u' v hu', ht v' u hv', add_comm]`. Introduce and unpack `⟨u, v, hu, hv, e⟩`. Take `⟨v', hv'⟩` from `lift_ex s u`. Take `⟨u', hu'⟩` from `lift_ex t v`.

Use `⟨u', v', ?_, ?_, ?_⟩` and prove the remaining obligations. Use `filter_upwards [hv, hu'] with x a b hx`. Rewrite using `[b, a hx, map_zero]`. Use `filter_upwards [hu, hv'] with x a b hx`. Rewrite using `[b, a hx, map_zero]`.

Rewrite using `[e, map_add, hs u v' hv', ht v u' hu', add_comm]`.
-/
private theorem abs_main (J : L V →ₗᵢ[ℂ] H) (J' : L W →ₗᵢ[ℂ] H) (U : H ≃ₗᵢ[ℂ] H) (s : V ≃ₗᵢ[ℂ] W) (t : W ≃ₗᵢ[ℂ] V)
    (hs : ∀ (u : L V) (v : L W), (∀ᵐ x : ℝ, v x = s (u x)) → U (J u) = J' v)
    (ht : ∀ (v : L W) (u : L V), (∀ᵐ x : ℝ, u x = t (v x)) → U (J' v) = J u) :
    (∀ P : H →L[ℂ] H, IsOrthogonalProjectionTwoLines J J' P → ∀ h, U (P h) = P (U h)) ∧
    ∀ (T : ℝ) (Λ : H →L[ℂ] H), (IsSelfAdjoint Λ ∧ Λ ∘L Λ = Λ ∧ ∀ h : H, Λ h = 0 ↔
      ∃ (u : L V) (v : L W), (∀ᵐ x : ℝ, x ≤ T → u x = 0) ∧ (∀ᵐ x : ℝ, x ≤ T → v x = 0) ∧ h = J u + J' v) →
      ∀ h, U (Λ h) = Λ (U h) := by
  refine ⟨fun P ⟨h1, h2, h3⟩ => comm_of_ker U P h1 h2 fun h => ?_,
    fun T Λ ⟨h1, h2, h3⟩ => comm_of_ker U Λ h1 h2 fun h => ?_⟩
  · rw [h3, h3]
    constructor
    · rintro ⟨a, b⟩
      refine ⟨fun u => ?_, fun v => ?_⟩
      · obtain ⟨v, hv⟩ := lift_ex s u
        rw [← U.inner_map_map, hs u v hv, b]
      · obtain ⟨u, hu⟩ := lift_ex t v
        rw [← U.inner_map_map, ht v u hu, a]
    · rintro ⟨a, b⟩
      refine ⟨fun u => ?_, fun v => ?_⟩
      · obtain ⟨v, hv⟩ := lift_ex' t u
        rw [← ht v u hv, U.inner_map_map, b]
      · obtain ⟨u, hu⟩ := lift_ex' s v
        rw [← hs u v hu, U.inner_map_map, a]
  · rw [h3, h3]
    constructor
    · rintro ⟨u, v, hu, hv, e⟩
      obtain ⟨v', hv'⟩ := lift_ex' t u
      obtain ⟨u', hu'⟩ := lift_ex' s v
      refine ⟨u', v', ?_, ?_, ?_⟩
      · filter_upwards [hv, hu'] with x a b hx
        exact s.injective (by rw [← b, a hx, map_zero])
      · filter_upwards [hu, hv'] with x a b hx
        exact t.injective (by rw [← b, a hx, map_zero])
      · apply U.injective
        rw [e, map_add, hs u' v hu', ht v' u hv', add_comm]
    · rintro ⟨u, v, hu, hv, e⟩
      obtain ⟨v', hv'⟩ := lift_ex s u
      obtain ⟨u', hu'⟩ := lift_ex t v
      refine ⟨u', v', ?_, ?_, ?_⟩
      · filter_upwards [hv, hu'] with x a b hx
        rw [b, a hx, map_zero]
      · filter_upwards [hu, hv'] with x a b hx
        rw [b, a hx, map_zero]
      · rw [e, map_add, hs u v' hv', ht v u' hu', add_comm]

end Abstract

/- English proof (translation)
Introduce `E _ _ _ μ _ θ 𝔢 𝔵`. Take `⟨U, hU, -, -⟩` from `UpperTheory.ConvolutionTheory.C.twistUnitary E (2 + 2) μ θ`. Establish `hU' : ∀ h, θ.U h = U h` using `fun h => by rw [← hU]; rfl`. Take `⟨t, -, ht⟩` from `UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.convU E μ (BW.mu1 E 2) 𝔵.τ₂ 𝔵.τ₁ ⟨𝔵.pair.irr₂, 𝔵.pair.irr₁, 𝔵.pair.orth.symm⟩ 𝔵.D 𝔵.d' 𝔵.d 𝔵.A' 𝔵.A 𝔵.σ θ 𝔵.θ₂ 𝔵.gal 𝔵.gal₂ 𝔵.stable 𝔵.swap₂ 𝔵.swap₁`. Take `⟨a, b⟩` from `abs_main 𝔵.A.J 𝔵.A'.J U 𝔵.s t (fun u v h => by rw [← hU']; exact 𝔵.s_op u v h) (fun v u h => by rw [← hU']; exact ht v u h)`.

Use `⟨ContinuousLinearMap.ext fun h => ?_, fun T Λ hΛ => ContinuousLinearMap.ext fun h => ?_⟩` and prove the remaining obligations. Simplify using `only [ContinuousLinearMap.comp_apply, hU']`. Conclude with `a _ 𝔵.isP h`. Simplify using `only [ContinuousLinearMap.comp_apply, hU']`. Conclude with `b T Λ hΛ h`.
-/
theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.twistP :
    ∀ {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {μ : Measure (normOneGL E (2 + 2))} [μ.IsHaarMeasure] {θ : Twist μ} {𝔢 : Side θ 2} (𝔵 : Fam 𝔢), θ.U ∘L 𝔵.P = 𝔵.P ∘L θ.U ∧
      ∀ (T : ℝ) (Λ : L2 μ →L[ℂ] L2 μ), IsTrunc 𝔵.A.J 𝔵.A'.J T Λ → θ.U ∘L Λ = Λ ∘L θ.U := by
  intro E _ _ _ μ _ θ 𝔢 𝔵
  obtain ⟨U, hU, -, -⟩ := UpperTheory.ConvolutionTheory.C.twistUnitary E (2 + 2) μ θ
  have hU' : ∀ h, θ.U h = U h := fun h => by rw [← hU]; rfl
  obtain ⟨t, -, ht⟩ := UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.convU E μ (BW.mu1 E 2) 𝔵.τ₂ 𝔵.τ₁ ⟨𝔵.pair.irr₂, 𝔵.pair.irr₁, 𝔵.pair.orth.symm⟩
    𝔵.D 𝔵.d' 𝔵.d 𝔵.A' 𝔵.A 𝔵.σ θ 𝔵.θ₂ 𝔵.gal 𝔵.gal₂ 𝔵.stable 𝔵.swap₂ 𝔵.swap₁
  obtain ⟨a, b⟩ := abs_main 𝔵.A.J 𝔵.A'.J U 𝔵.s t (fun u v h => by rw [← hU']; exact 𝔵.s_op u v h)
    (fun v u h => by rw [← hU']; exact ht v u h)
  refine ⟨ContinuousLinearMap.ext fun h => ?_, fun T Λ hΛ => ContinuousLinearMap.ext fun h => ?_⟩
  · simp only [ContinuousLinearMap.comp_apply, hU']
    exact a _ 𝔵.isP h
  · simp only [ContinuousLinearMap.comp_apply, hU']
    exact b T Λ hΛ h
