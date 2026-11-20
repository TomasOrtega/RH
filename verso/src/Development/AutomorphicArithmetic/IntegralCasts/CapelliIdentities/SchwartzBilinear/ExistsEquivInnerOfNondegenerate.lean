import Mathlib

namespace UpperTheory.Reformulated.B.P6.r12b
open FourierTransform MeasureTheory Complex Real Module

/- English proof (translation)
Use `haveI : (μ.map e).IsAddHaarMeasure := e.isAddHaarMeasure_map μ`. Take `⟨c, hc⟩ : ∃ c : NNReal, μ.map e = c • (volume : Measure E)` from `⟨_, Measure.isAddLeftInvariant_eq_smul _ _⟩`. Use `⟨c, fun F => ?_⟩` and prove the remaining obligations. Establish `h1 : ∫ v, F (e v) ∂μ = ∫ w, F w ∂(μ.map e)`. Use `integral_map_equiv (μ := μ) e.toHomeomorph.toMeasurableEquiv F` as an intermediate fact.

Simplify using `using this.symm`. Rewrite using `[h1, hc, integral_smul_nnreal_measure]`.
-/
theorem integral_comp_linearEquiv_eq_smul {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure]
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (e : V ≃L[ℝ] E) :
    ∃ c : NNReal, ∀ F : E → ℂ, ∫ v, F (e v) ∂μ = c • ∫ w, F w := by
  haveI : (μ.map e).IsAddHaarMeasure := e.isAddHaarMeasure_map μ
  obtain ⟨c, hc⟩ : ∃ c : NNReal, μ.map e = c • (volume : Measure E) :=
    ⟨_, Measure.isAddLeftInvariant_eq_smul _ _⟩
  refine ⟨c, fun F => ?_⟩
  have h1 : ∫ v, F (e v) ∂μ = ∫ w, F w ∂(μ.map e) := by
    have := integral_map_equiv (μ := μ) e.toHomeomorph.toMeasurableEquiv F
    simpa using this.symm
  rw [h1, hc, integral_smul_nnreal_measure]

/- English proof (translation)
Set `L : V →ₗ[ℝ] E →ₗ[ℝ] ℝ` to `B.compl₂ (e.symm : E →ₗ[ℝ] V)`. Set `Φ : E →ₗ[ℝ] E →ₗ[ℝ] ℝ` to `innerₗ E`. Establish `hΦ : ∀ x y, Φ x y = inner ℝ x y` using `fun x y => by simp [Φ]`. Establish `hΦi : Function.Injective Φ`. Rewrite using `[← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']`.

Introduce `x hx`. Establish `h0 : inner ℝ x x = (0 : ℝ)` using `by rw [← hΦ, hx]; rfl`. Conclude with `inner_self_eq_zero.mp h0`. Establish `hdim : finrank ℝ E = finrank ℝ (E →ₗ[ℝ] ℝ)` using `(Subspace.dual_finrank_eq).symm`. Establish `hΦs : Function.Surjective Φ` using `(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hΦi`.

Set `Φe : E ≃ₗ[ℝ] (E →ₗ[ℝ] ℝ)` to `LinearEquiv.ofBijective Φ ⟨hΦi, hΦs⟩`. Establish `hΦe : ∀ x, Φe x = Φ x` using `fun x => rfl`. Set `a : V →ₗ[ℝ] E` to `Φe.symm.toLinearMap ∘ₗ L`. Establish `ha : ∀ u w, inner ℝ (a u) w = B u (e.symm w)`. Introduce `u w`.

Rewrite using `[← hΦ, ← hΦe]`. Simplify using `[a, L]`. Establish `hai : Function.Injective a`. Rewrite using `[← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']`. Introduce `u hu`.

Apply `hB u` to reduce the goal to its premises. Introduce `v`. Use `ha u (e v)` as an intermediate fact. Rewrite `this` using `[hu, inner_zero_left, e.symm_apply_apply]`. Conclude with `this.symm`.

Establish `hdim2 : finrank ℝ V = finrank ℝ E` using `e.toLinearEquiv.finrank_eq`. Establish `has : Function.Surjective a` using `(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim2).mp hai`. Set `A : V ≃L[ℝ] E` to `(LinearEquiv.ofBijective a ⟨hai, has⟩).toContinuousLinearEquiv`. Use `⟨A, fun u v => ?_⟩` and prove the remaining obligations. Establish `hA : A u = a u` using `rfl`.

Rewrite using `[hA, ha, e.symm_apply_apply]`.
-/
theorem exists_equiv_inner_of_nondegenerate {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (hB : ∀ u, (∀ v, B u v = 0) → u = 0) (e : V ≃L[ℝ] E) :
    ∃ A : V ≃L[ℝ] E, ∀ u v, B u v = inner ℝ (A u) (e v) := by
  let L : V →ₗ[ℝ] E →ₗ[ℝ] ℝ := B.compl₂ (e.symm : E →ₗ[ℝ] V)
  let Φ : E →ₗ[ℝ] E →ₗ[ℝ] ℝ := innerₗ E
  have hΦ : ∀ x y, Φ x y = inner ℝ x y := fun x y => by simp [Φ]
  have hΦi : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    have h0 : inner ℝ x x = (0 : ℝ) := by rw [← hΦ, hx]; rfl
    exact inner_self_eq_zero.mp h0
  have hdim : finrank ℝ E = finrank ℝ (E →ₗ[ℝ] ℝ) := (Subspace.dual_finrank_eq).symm
  have hΦs : Function.Surjective Φ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hΦi
  let Φe : E ≃ₗ[ℝ] (E →ₗ[ℝ] ℝ) := LinearEquiv.ofBijective Φ ⟨hΦi, hΦs⟩
  have hΦe : ∀ x, Φe x = Φ x := fun x => rfl
  let a : V →ₗ[ℝ] E := Φe.symm.toLinearMap ∘ₗ L
  have ha : ∀ u w, inner ℝ (a u) w = B u (e.symm w) := by
    intro u w
    rw [← hΦ, ← hΦe]
    simp [a, L]
  have hai : Function.Injective a := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro u hu
    apply hB u
    intro v
    have := ha u (e v)
    rw [hu, inner_zero_left, e.symm_apply_apply] at this
    exact this.symm
  have hdim2 : finrank ℝ V = finrank ℝ E := e.toLinearEquiv.finrank_eq
  have has : Function.Surjective a :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim2).mp hai
  let A : V ≃L[ℝ] E := (LinearEquiv.ofBijective a ⟨hai, has⟩).toContinuousLinearEquiv
  refine ⟨A, fun u v => ?_⟩
  have hA : A u = a u := rfl
  rw [hA, ha, e.symm_apply_apply]

/- English proof (translation)
Introduce `V _ _ _ _ _ μ _ B hB φ`. Set `E` to `EuclideanSpace ℝ (Fin (finrank ℝ V))`. Set `e : V ≃L[ℝ] E` to `ContinuousLinearEquiv.ofFinrankEq (by simp [E])`. Take `⟨A, hA⟩` from `exists_equiv_inner_of_nondegenerate B hB e`. Take `⟨c, hc⟩` from `integral_comp_linearEquiv_eq_smul μ e`.

Set `g : SchwartzMap E ℂ` to `SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e.symm φ`. Establish `hg : ∀ w, g w = φ (e.symm w)` using `fun w => rfl`. Set `N : V ≃L[ℝ] E` to `A.trans (ContinuousLinearEquiv.neg ℝ)`. Set `h : SchwartzMap V ℂ` to `SchwartzMap.compCLMOfContinuousLinearEquiv ℂ N (𝓕 g)`. Establish `hh : ∀ u, h u = (𝓕 g) (-(A u))` using `fun u => rfl`.

Use `⟨((c : ℝ) : ℂ) • h, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `u`. Establish `hF : ∀ w : E, (𝓕 g) w = ∫ x, Complex.exp (-(2 * π * I * (inner ℝ x w : ℝ))) * g x`. Introduce `w`. Rewrite using `[SchwartzMap.fourier_coe, Real.fourier_eq]`.

Use `congr 1`. Use extensionality with `x`. Rewrite using `[Circle.smul_def, Real.fourierChar_apply, smul_eq_mul]`. Use `congr 1`. Use `push_cast`.

Put the polynomial expressions in normal form. Set `F : E → ℂ` to `fun w => Complex.exp (2 * π * I * (inner ℝ (A u) w : ℝ)) * φ (e.symm w)`. Establish `hint : (fun v => Complex.exp (2 * π * I * ((B u v : ℝ) : ℂ)) * φ v) = fun v => F (e v)`. Use function extensionality and compare the values at `v`. Simplify using `only [F, hA, e.symm_apply_apply]`.

Establish `hL : (((c : ℝ) : ℂ) • h) u = ((c : ℝ) : ℂ) * ∫ w, F w`. Rewrite using `[SchwartzMap.smul_apply, hh, hF, smul_eq_mul]`. Use `congr 1`. Use `congr 1`. Use extensionality with `x`.

Rewrite using `[hg, inner_neg_right, real_inner_comm]`. Use `congr 2`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hL]`.

Use `show _ = ∫ v, Complex.exp (2 * π * I * ((B u v : ℝ) : ℂ)) * φ v ∂μ`. Rewrite using `[hint, hc F, NNReal.smul_def, Complex.real_smul]`.
-/
theorem GlobalTheory.CompanionTheory.FourierMatrix.exists_schwartz_bilinear_transform.{u_1} :
    ∀ {V : Type u_1} [inst : NormedAddCommGroup V] [inst_1 : NormedSpace ℝ V] [FiniteDimensional ℝ V] [inst_3 : MeasurableSpace V] [BorelSpace V] (μ : MeasureTheory.Measure V) [μ.IsAddHaarMeasure] (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ), (∀ (u : V), (∀ (v : V), DFunLike.coe (DFunLike.coe B u) v = OfNat.ofNat (nat_lit 0)) → u = OfNat.ofNat (nat_lit 0)) → ∀ (φ : SchwartzMap V ℂ), ∃ (ψ : SchwartzMap V ℂ), DFunLike.coe ψ = fun (u : V) ↦ ∫ (v : V), Complex.exp (OfNat.ofNat (nat_lit 2) * Complex.ofReal Real.pi * Complex.I * Complex.ofReal (DFunLike.coe (DFunLike.coe B u) v)) * DFunLike.coe φ v ∂μ := by
  intro V _ _ _ _ _ μ _ B hB φ
  let E := EuclideanSpace ℝ (Fin (finrank ℝ V))
  let e : V ≃L[ℝ] E := ContinuousLinearEquiv.ofFinrankEq (by simp [E])
  obtain ⟨A, hA⟩ := exists_equiv_inner_of_nondegenerate B hB e
  obtain ⟨c, hc⟩ := integral_comp_linearEquiv_eq_smul μ e
  let g : SchwartzMap E ℂ := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e.symm φ
  have hg : ∀ w, g w = φ (e.symm w) := fun w => rfl
  let N : V ≃L[ℝ] E := A.trans (ContinuousLinearEquiv.neg ℝ)
  let h : SchwartzMap V ℂ := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ N (𝓕 g)
  have hh : ∀ u, h u = (𝓕 g) (-(A u)) := fun u => rfl
  refine ⟨((c : ℝ) : ℂ) • h, ?_⟩
  funext u
  have hF : ∀ w : E, (𝓕 g) w = ∫ x, Complex.exp (-(2 * π * I * (inner ℝ x w : ℝ))) * g x := by
    intro w
    rw [SchwartzMap.fourier_coe, Real.fourier_eq]
    congr 1; ext x
    rw [Circle.smul_def, Real.fourierChar_apply, smul_eq_mul]
    congr 1; push_cast; ring_nf
  let F : E → ℂ := fun w => Complex.exp (2 * π * I * (inner ℝ (A u) w : ℝ)) * φ (e.symm w)
  have hint : (fun v => Complex.exp (2 * π * I * ((B u v : ℝ) : ℂ)) * φ v) = fun v => F (e v) := by
    funext v
    simp only [F, hA, e.symm_apply_apply]
  have hL : (((c : ℝ) : ℂ) • h) u = ((c : ℝ) : ℂ) * ∫ w, F w := by
    rw [SchwartzMap.smul_apply, hh, hF, smul_eq_mul]
    congr 1
    congr 1; ext x
    rw [hg, inner_neg_right, real_inner_comm]
    congr 2
    push_cast; ring
  rw [hL]
  show _ = ∫ v, Complex.exp (2 * π * I * ((B u v : ℝ) : ℂ)) * φ v ∂μ
  rw [hint, hc F, NNReal.smul_def, Complex.real_smul]

end UpperTheory.Reformulated.B.P6.r12b
