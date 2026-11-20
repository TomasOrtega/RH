import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.Carries
import GroundTheory.AutomorphicForms.TraceNormComp
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.CutLaws

open MeasureTheory GroundTheory.Automorphic PositivityTheory.Rg.Tf.IntegralApplyAeEq Set Filter Topology UpperTheory.V.Z.IntegralApplyAeEq
open scoped InnerProductSpace FourierTransform ComplexConjugate

/- English proof (translation)
Introduce `P`. Take `⟨c1, c2, -, -, -, -, -, c8, -⟩` from `cutLaws (V := V) (Ioi T) (Ioi T) measurableSet_Ioi measurableSet_Ioi`. Rewrite `c1` using `[inter_self]`. Establish `cc : ∀ u, cut V (Ioi T) (cut V (Ioi T) u) = cut V (Ioi T) u` using `fun u => DFunLike.congr_fun c1 u`. Establish `jj : ∀ u, ContinuousLinearMap.adjoint J.toContinuousLinearMap (J u) = u` using `fun u => ext_inner_left ℂ fun v => by`.

Rewrite using `[ContinuousLinearMap.adjoint_inner_right]`. Conclude with `J.inner_map_map v u`. Establish `pa : ∀ h, P h = J (cut V (Ioi T) (ContinuousLinearMap.adjoint J.toContinuousLinearMap h))` using `fun _ => rfl`. Use `⟨?_, ?_, fun h => ⟨_, ?_, pa h⟩, fun u hu => ?_⟩` and prove the remaining obligations. Use extensionality with `h`.

Rewrite using `[ContinuousLinearMap.mul_apply, pa h, pa, jj, cc]`. Use `show ContinuousLinearMap.adjoint P = P`. Simplify using `only [P, ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint, c2.adjoint_eq, ContinuousLinearMap.comp_assoc]`. Conclude with `((c8 _).1 (cc _)).mono fun x hx h => hx (by simpa using h)`. Rewrite using `[pa, jj, (c8 u).2 (hu.mono fun x hx h => hx (by simpa using h))]`.
-/
private theorem prj {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {V : Type} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V] (J : L V →ₗᵢ[ℂ] H) (T : ℝ) :
    let P := J.toContinuousLinearMap ∘L cut V (Ioi T) ∘L ContinuousLinearMap.adjoint J.toContinuousLinearMap
    P * P = P ∧ IsSelfAdjoint P ∧ (∀ h, ∃ u : L V, (∀ᵐ x : ℝ, x ≤ T → u x = 0) ∧ P h = J u) ∧
      ∀ u : L V, (∀ᵐ x : ℝ, x ≤ T → u x = 0) → P (J u) = J u := by
  intro P
  obtain ⟨c1, c2, -, -, -, -, -, c8, -⟩ := cutLaws (V := V) (Ioi T) (Ioi T) measurableSet_Ioi measurableSet_Ioi
  rw [inter_self] at c1
  have cc : ∀ u, cut V (Ioi T) (cut V (Ioi T) u) = cut V (Ioi T) u := fun u => DFunLike.congr_fun c1 u
  have jj : ∀ u, ContinuousLinearMap.adjoint J.toContinuousLinearMap (J u) = u := fun u => ext_inner_left ℂ fun v => by
    rw [ContinuousLinearMap.adjoint_inner_right]; exact J.inner_map_map v u
  have pa : ∀ h, P h = J (cut V (Ioi T) (ContinuousLinearMap.adjoint J.toContinuousLinearMap h)) := fun _ => rfl
  refine ⟨?_, ?_, fun h => ⟨_, ?_, pa h⟩, fun u hu => ?_⟩
  · ext h
    rw [ContinuousLinearMap.mul_apply, pa h, pa, jj, cc]
  · show ContinuousLinearMap.adjoint P = P
    simp only [P, ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint, c2.adjoint_eq, ContinuousLinearMap.comp_assoc]
  · exact ((c8 _).1 (cc _)).mono fun x hx h => hx (by simpa using h)
  · rw [pa, jj, (c8 u).2 (hu.mono fun x hx h => hx (by simpa using h))]

/- English proof (translation)
Introduce `H _ _ _ V _ _ _ _ W _ _ _ _ J J' T Λ ho`. Take `⟨a1, a2, a3, a4⟩` from `prj J T`. Take `⟨b1, b2, b3, b4⟩` from `prj J' T`. Use `set P := J.toContinuousLinearMap ∘L cut V (Ioi T) ∘L ContinuousLinearMap.adjoint J.toContinuousLinearMap`. Use `set P' := J'.toContinuousLinearMap ∘L cut W (Ioi T) ∘L ContinuousLinearMap.adjoint J'.toContinuousLinearMap`.

Establish `o1 : P * P' = 0`. Use extensionality with `h`. Use `ext_inner_left ℂ fun y => ?_` and prove the remaining obligations. Rewrite using `[ContinuousLinearMap.mul_apply, ← a2.isSymmetric.apply_clm, ContinuousLinearMap.zero_apply, inner_zero_right]`. Conclude with `ho _ _`.

Establish `o2 : P' * P = 0`. Use `congrArg star o1` as an intermediate fact. Rewrite `this` using `[star_mul, a2.star_eq, b2.star_eq, star_zero]`. Then use the resulting hypothesis. Establish `t0 : IsTrunc J J' T (1 - P - P')`. Use `⟨((IsSelfAdjoint.one _).sub a2).sub b2, ?_, fun h => ⟨fun hh => ?_, ?_⟩⟩` and prove the remaining obligations.

Use `show (1 - P - P') * (1 - P - P') = _`. Simplify using `only [mul_sub, sub_mul, a1, b1, o1, o2, mul_one, one_mul]`. Normalize the expressions using the abelian group laws. Take `⟨u, hu, eu⟩` from `a3 h`. Take `⟨v, hv, ev⟩` from `b3 h`.

Use `⟨u, v, hu, hv, ?_⟩` and prove the remaining obligations. Rewrite using `[← eu, ← ev]`. Simplify using `only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply] at hh`. Rewrite `hh` using `[sub_sub, sub_eq_zero]`. Conclude with `hh`.

Introduce and unpack `⟨u, v, hu, hv, rfl⟩`. Establish `e1 : P (J' v) = 0` using `by rw [← b4 v hv]; exact DFunLike.congr_fun o1 _`. Establish `e2 : P' (J u) = 0` using `by rw [← a4 u hu]; exact DFunLike.congr_fun o2 _`. Simplify using `[a4 u hu, b4 v hv, e1, e2]`. Use `⟨fun t1 => ?_, fun h => h ▸ t0⟩` and prove the remaining obligations.

Establish `key : ∀ A B : H →L[ℂ] H, IsTrunc J J' T A → IsTrunc J J' T B → A * B = A` using `fun A B hA hB => by`. Use extensionality with `h`. Establish `h1 : B (h - B h) = 0` using `by rw [map_sub, sub_eq_zero]; exact (DFunLike.congr_fun hB.2.1 h).symm`. Establish `h2` using `(hA.2.2 _).2 ((hB.2.2 _).1 h1)`. Rewrite `h2` using `[map_sub, sub_eq_zero]`.

Conclude with `h2.symm`. Establish `h1` using `congrArg star (key _ _ t1 t0)`. Rewrite `h1` using `[star_mul, t1.1.star_eq, t0.1.star_eq, key _ _ t0 t1]`. Conclude with `h1.symm`.
-/
theorem UpperTheory.V.Z.IntegralApplyAeEq.truncEq :
    ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V] {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] [CompleteSpace W] (J : L V →ₗᵢ[ℂ] H) (J' : L W →ₗᵢ[ℂ] H) (T : ℝ) (Λ : H →L[ℂ] H),
      (∀ u v, ⟪J (cut V (Ioi T) u), J' (cut W (Ioi T) v)⟫_ℂ = 0) → (IsTrunc J J' T Λ ↔
        Λ = 1 - J.toContinuousLinearMap ∘L cut V (Ioi T) ∘L ContinuousLinearMap.adjoint J.toContinuousLinearMap -
          J'.toContinuousLinearMap ∘L cut W (Ioi T) ∘L ContinuousLinearMap.adjoint J'.toContinuousLinearMap) := by
  intro H _ _ _ V _ _ _ _ W _ _ _ _ J J' T Λ ho
  obtain ⟨a1, a2, a3, a4⟩ := prj J T
  obtain ⟨b1, b2, b3, b4⟩ := prj J' T
  set P := J.toContinuousLinearMap ∘L cut V (Ioi T) ∘L ContinuousLinearMap.adjoint J.toContinuousLinearMap
  set P' := J'.toContinuousLinearMap ∘L cut W (Ioi T) ∘L ContinuousLinearMap.adjoint J'.toContinuousLinearMap
  have o1 : P * P' = 0 := by
    ext h
    refine ext_inner_left ℂ fun y => ?_
    rw [ContinuousLinearMap.mul_apply, ← a2.isSymmetric.apply_clm, ContinuousLinearMap.zero_apply, inner_zero_right]
    exact ho _ _
  have o2 : P' * P = 0 := by
    have := congrArg star o1
    rwa [star_mul, a2.star_eq, b2.star_eq, star_zero] at this
  have t0 : IsTrunc J J' T (1 - P - P') := by
    refine ⟨((IsSelfAdjoint.one _).sub a2).sub b2, ?_, fun h => ⟨fun hh => ?_, ?_⟩⟩
    · show (1 - P - P') * (1 - P - P') = _
      simp only [mul_sub, sub_mul, a1, b1, o1, o2, mul_one, one_mul]; abel
    · obtain ⟨u, hu, eu⟩ := a3 h
      obtain ⟨v, hv, ev⟩ := b3 h
      refine ⟨u, v, hu, hv, ?_⟩
      rw [← eu, ← ev]
      simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply] at hh
      rw [sub_sub, sub_eq_zero] at hh
      exact hh
    · rintro ⟨u, v, hu, hv, rfl⟩
      have e1 : P (J' v) = 0 := by rw [← b4 v hv]; exact DFunLike.congr_fun o1 _
      have e2 : P' (J u) = 0 := by rw [← a4 u hu]; exact DFunLike.congr_fun o2 _
      simp [a4 u hu, b4 v hv, e1, e2]
  refine ⟨fun t1 => ?_, fun h => h ▸ t0⟩
  have key : ∀ A B : H →L[ℂ] H, IsTrunc J J' T A → IsTrunc J J' T B → A * B = A := fun A B hA hB => by
    ext h
    have h1 : B (h - B h) = 0 := by rw [map_sub, sub_eq_zero]; exact (DFunLike.congr_fun hB.2.1 h).symm
    have h2 := (hA.2.2 _).2 ((hB.2.2 _).1 h1)
    rw [map_sub, sub_eq_zero] at h2
    exact h2.symm
  have h1 := congrArg star (key _ _ t1 t0)
  rw [star_mul, t1.1.star_eq, t0.1.star_eq, key _ _ t0 t1] at h1
  exact h1.symm
