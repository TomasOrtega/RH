import ReciprocityTheory.L2DbarEstimates.MinimalSolutions.MinimalSolutionStatement

namespace ReciprocityTheory.L2DbarEstimates

open scoped InnerProductSpace

/- English proof (translation)
Introduce `θ ℓ A hA hbd`. Establish `hker : LinearMap.ker θ ≤ LinearMap.ker ℓ`. Introduce `e he`. Rewrite `he`, the goal using `[LinearMap.mem_ker]`. Establish `h` using `hbd e`.

Rewrite `h` using `[he, norm_zero]`. Establish `: ‖ℓ e‖ ^ 2 ≤ 0` using `by simpa using h`. Establish `h0 : ‖ℓ e‖ = 0` using `by nlinarith [norm_nonneg (ℓ e)]`. Conclude with `norm_eq_zero.mp h0`. Use `set R := LinearMap.range θ with hR`.

Set `φ : R →ₗ[ℂ] ℂ` to `(LinearMap.ker θ).liftQ ℓ hker ∘ₗ θ.quotKerEquivRange.symm.toLinearMap`. Establish `hφ : ∀ e : E, φ ⟨θ e, LinearMap.mem_range_self θ e⟩ = ℓ e`. Introduce `e`. Establish `hmk : (⟨θ e, LinearMap.mem_range_self θ e⟩ : R) = θ.quotKerEquivRange (Submodule.Quotient.mk e)` using `rfl`. Simplify using `only [φ, LinearMap.comp_apply, LinearEquiv.coe_coe]`.

Rewrite using `[hmk, LinearEquiv.symm_apply_apply, Submodule.liftQ_apply]`. Establish `hsq : ∀ e : E, ‖ℓ e‖ ≤ Real.sqrt A * ‖θ e‖`. Introduce `e`. Establish `h1` using `Real.sqrt_le_sqrt (hbd e)`. Rewrite `h1` using `[Real.sqrt_sq (norm_nonneg _), Real.sqrt_mul hA, Real.sqrt_sq (norm_nonneg _)]`. Then use the resulting hypothesis.

Establish `hφb : ∀ y : R, ‖φ y‖ ≤ Real.sqrt A * ‖y‖`. Introduce and unpack `⟨y, e, rfl⟩`. Rewrite using `[hφ e]`. Conclude with `hsq e`. Set `φc : R →L[ℂ] ℂ` to `φ.mkContinuous (Real.sqrt A) hφb`.

Take `⟨f, hf, hfn⟩` from `exists_extension_norm_eq R φc`. Use `set v := (InnerProductSpace.toDual ℂ H).symm f with hv`. Establish `hvnorm : ‖v‖ ≤ Real.sqrt A`. Rewrite using `[hv, LinearIsometryEquiv.norm_map, hfn]`. Conclude with `LinearMap.mkContinuous_norm_le _ (Real.sqrt_nonneg A) _`.

Establish `hvin : ∀ e : E, ⟪v, θ e⟫_ℂ = ℓ e`. Introduce `e`. Rewrite using `[hv, InnerProductSpace.toDual_symm_apply]`. Use `hf ⟨θ e, LinearMap.mem_range_self θ e⟩` as an intermediate fact. Simplify `this` using `[φc, hφ e]`.

Use `set K := R.topologicalClosure with hK`. Use `haveI : CompleteSpace K := R.isClosed_topologicalClosure.completeSpace_coe`. Use `⟨K.starProjection v, K.starProjection_apply_mem v, ?_, ?_⟩` and prove the remaining obligations. Establish `h3 : ‖K.starProjection v‖ ≤ Real.sqrt A` using `(K.norm_starProjection_apply_le v).trans hvnorm`. Combine the equalities or inequalities in the displayed calculation.

Introduce `e`. Establish `hmem : θ e ∈ K` using `R.le_topologicalClosure (LinearMap.mem_range_self θ e)`. Rewrite using `[K.inner_starProjection_left_eq_right, Submodule.starProjection_eq_self_iff.mpr hmem]`. Conclude with `hvin e`.
-/
theorem rieszOnRange (E H : Type*) [AddCommGroup E] [Module ℂ E]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] :
    RieszOnRangeStatement E H := by
  intro θ ℓ A hA hbd

  have hker : LinearMap.ker θ ≤ LinearMap.ker ℓ := by
    intro e he
    rw [LinearMap.mem_ker] at he ⊢
    have h := hbd e
    rw [he, norm_zero] at h
    have : ‖ℓ e‖ ^ 2 ≤ 0 := by simpa using h
    have h0 : ‖ℓ e‖ = 0 := by nlinarith [norm_nonneg (ℓ e)]
    exact norm_eq_zero.mp h0
  set R := LinearMap.range θ with hR
  let φ : R →ₗ[ℂ] ℂ := (LinearMap.ker θ).liftQ ℓ hker ∘ₗ θ.quotKerEquivRange.symm.toLinearMap
  have hφ : ∀ e : E, φ ⟨θ e, LinearMap.mem_range_self θ e⟩ = ℓ e := by
    intro e
    have hmk : (⟨θ e, LinearMap.mem_range_self θ e⟩ : R) =
        θ.quotKerEquivRange (Submodule.Quotient.mk e) := rfl
    simp only [φ, LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [hmk, LinearEquiv.symm_apply_apply, Submodule.liftQ_apply]
  have hsq : ∀ e : E, ‖ℓ e‖ ≤ Real.sqrt A * ‖θ e‖ := by
    intro e
    have h1 := Real.sqrt_le_sqrt (hbd e)
    rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_mul hA, Real.sqrt_sq (norm_nonneg _)] at h1
  have hφb : ∀ y : R, ‖φ y‖ ≤ Real.sqrt A * ‖y‖ := by
    rintro ⟨y, e, rfl⟩
    rw [hφ e]
    exact hsq e
  let φc : R →L[ℂ] ℂ := φ.mkContinuous (Real.sqrt A) hφb
  obtain ⟨f, hf, hfn⟩ := exists_extension_norm_eq R φc
  set v := (InnerProductSpace.toDual ℂ H).symm f with hv
  have hvnorm : ‖v‖ ≤ Real.sqrt A := by
    rw [hv, LinearIsometryEquiv.norm_map, hfn]
    exact LinearMap.mkContinuous_norm_le _ (Real.sqrt_nonneg A) _
  have hvin : ∀ e : E, ⟪v, θ e⟫_ℂ = ℓ e := by
    intro e
    rw [hv, InnerProductSpace.toDual_symm_apply]
    have := hf ⟨θ e, LinearMap.mem_range_self θ e⟩
    simpa [φc, hφ e] using this
  set K := R.topologicalClosure with hK
  haveI : CompleteSpace K := R.isClosed_topologicalClosure.completeSpace_coe
  refine ⟨K.starProjection v, K.starProjection_apply_mem v, ?_, ?_⟩
  · have h3 : ‖K.starProjection v‖ ≤ Real.sqrt A := (K.norm_starProjection_apply_le v).trans hvnorm
    calc ‖K.starProjection v‖ ^ 2 ≤ Real.sqrt A ^ 2 := by gcongr
      _ = A := Real.sq_sqrt hA
  · intro e
    have hmem : θ e ∈ K := R.le_topologicalClosure (LinearMap.mem_range_self θ e)
    rw [K.inner_starProjection_left_eq_right, Submodule.starProjection_eq_self_iff.mpr hmem]
    exact hvin e

/- English proof (translation)
Introduce `θ ℓ u u' hu h h'`. Use `set R := LinearMap.range θ with hR`. Establish `hw : u' - u ∈ Rᗮ`. Rewrite using `[Submodule.mem_orthogonal]`. Introduce and unpack `y ⟨e, rfl⟩`.

Rewrite using `[inner_sub_right, ← inner_conj_symm, h', ← inner_conj_symm, h, sub_self]`. Establish `hcl : R.topologicalClosure ≤ Rᗮᗮ` using `R.topologicalClosure_minimal R.le_orthogonal_orthogonal Rᗮ.isClosed_orthogonal`. Establish `hperp : ∀ z ∈ R.topologicalClosure, ⟪u' - u, z⟫_ℂ = 0`. Introduce `z hz`. Conclude with `(Submodule.mem_orthogonal _ _).mp (hcl hz) _ hw`.

Use `⟨hw, ?_, ?_⟩` and prove the remaining obligations. Establish `h0 : ⟪u, u' - u⟫_ℂ = 0`. Rewrite using `[← inner_conj_symm, hperp u hu, map_zero]`. Establish `hsq : ‖u'‖ ^ 2 = ‖u‖ ^ 2 + ‖u' - u‖ ^ 2`. Use `@norm_add_sq ℂ H _ _ _ u (u' - u)` as an intermediate fact.

Rewrite `this` using `[add_sub_cancel]`. Rewrite using `[this, h0]`. Simplify using the standard rewrite rules. Establish `: ‖u‖ ^ 2 ≤ ‖u'‖ ^ 2`. Rewrite using `[hsq]`.

Use polynomial arithmetic with `[sq_nonneg ‖u' - u‖]`. Conclude with `(pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp this`. Introduce `hu'`. Establish `hz : u' - u ∈ R.topologicalClosure` using `Submodule.sub_mem _ hu' hu`. Use `hperp _ hz` as an intermediate fact.

Rewrite `this` using `[inner_self_eq_zero, sub_eq_zero]`. Conclude with `this`.
-/
theorem minimalSolution (E H : Type*) [AddCommGroup E] [Module ℂ E]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] : MinimalSolutionStatement E H := by
  intro θ ℓ u u' hu h h'
  set R := LinearMap.range θ with hR
  have hw : u' - u ∈ Rᗮ := by
    rw [Submodule.mem_orthogonal]
    rintro y ⟨e, rfl⟩
    rw [inner_sub_right, ← inner_conj_symm, h', ← inner_conj_symm, h, sub_self]
  have hcl : R.topologicalClosure ≤ Rᗮᗮ :=
    R.topologicalClosure_minimal R.le_orthogonal_orthogonal Rᗮ.isClosed_orthogonal
  have hperp : ∀ z ∈ R.topologicalClosure, ⟪u' - u, z⟫_ℂ = 0 := by
    intro z hz
    exact (Submodule.mem_orthogonal _ _).mp (hcl hz) _ hw
  refine ⟨hw, ?_, ?_⟩
  · have h0 : ⟪u, u' - u⟫_ℂ = 0 := by
      rw [← inner_conj_symm, hperp u hu, map_zero]
    have hsq : ‖u'‖ ^ 2 = ‖u‖ ^ 2 + ‖u' - u‖ ^ 2 := by
      have := @norm_add_sq ℂ H _ _ _ u (u' - u)
      rw [add_sub_cancel] at this
      rw [this, h0]
      simp
    have : ‖u‖ ^ 2 ≤ ‖u'‖ ^ 2 := by
      rw [hsq]; nlinarith [sq_nonneg ‖u' - u‖]
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp this
  · intro hu'
    have hz : u' - u ∈ R.topologicalClosure := Submodule.sub_mem _ hu' hu
    have := hperp _ hz
    rw [inner_self_eq_zero, sub_eq_zero] at this
    exact this

end ReciprocityTheory.L2DbarEstimates
