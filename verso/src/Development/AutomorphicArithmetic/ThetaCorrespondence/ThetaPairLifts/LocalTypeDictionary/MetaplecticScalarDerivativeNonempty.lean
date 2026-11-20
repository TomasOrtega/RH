import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchwartzOneParameterGroupFormula
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.RealWeilRepresentationSchurScalar
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchwartzOneParameterGroupFormulaStatement

section
open scoped Matrix
noncomputable section
namespace GlobalTheory.MetaplecticScalarDeriv
open MeasureTheory Filter Topology GlobalTheory.RealWeil
/- English proof (translation)
Take `⟨G, _, _, _, pr, om, omS, -, -, h3, h4, -, h6⟩` from `hP.realMetaplecticRepresentation l`. Take `⟨γ, -, hγ0, hγadd, hγpr, hγd⟩` from `h6 Z hZ`. Establish `hmul : ∀ s t (f : Sch l), omS (γ s) (omS (γ t) f) = omS (γ (s + t)) f`. Introduce `s t f`. Rewrite using `[hγadd, map_mul]`.

Both sides reduce to the same expression. Establish `hS1 : ∀ t (f : Sch l), omS (γ (-t)) (omS (γ t) f) = f`. Introduce `t f`. Rewrite using `[hmul, neg_add_cancel, hγ0, map_one]`. Both sides reduce to the same expression.

Establish `hS2 : ∀ t (f : Sch l), omS (γ t) (omS (γ (-t)) f) = f`. Introduce `t f`. Rewrite using `[hmul, add_neg_cancel, hγ0, map_one]`. Both sides reduce to the same expression. Establish `hmat : ∀ t (w : l ⊕ l → ℝ), NormedSpace.exp (t • Z) *ᵥ ((pr (γ (-t)) : Matrix (l ⊕ l) (l ⊕ l) ℝ) *ᵥ w) = w`.

Introduce `t w`. Establish `e : pr (γ t) * pr (γ (-t)) = 1` using `by rw [← map_mul, ← hγadd, add_neg_cancel, hγ0, map_one]`. Establish `e' : (pr (γ t) : Matrix (l ⊕ l) (l ⊕ l) ℝ) * (pr (γ (-t)) : Matrix (l ⊕ l) (l ⊕ l) ℝ) = 1` using `congrArg (fun g : Matrix.symplecticGroup l ℝ => (g : Matrix (l ⊕ l) (l ⊕ l) ℝ)) e`. Rewrite using `[← hγpr t, Matrix.mulVec_mulVec, e', Matrix.one_mulVec]`. Establish `hU : ∀ t, ∃ a : ℂ, ‖a‖ = 1 ∧ ∀ h, (T t ∘ₗ (omS (γ (-t)) : Sch l →ₗ[ℂ] Sch l)) h = a • h`.

Introduce `t`. Use `_root_.GlobalTheory.T.real_weil_representation_schur_scalar hP l _ (fun w h h₁ hh => ?_) (fun h => ?_)` and prove the remaining obligations. Simplify using `only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe]`. Rewrite using `[hTrho t _ _ _ (intertwine_fun l _ (om (γ (-t))) (omS (γ (-t))) (h3 _) (h4 _) w h h₁ hh), hmat]`. Simplify using `only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe]`.

Rewrite using `[hTiso, lintegral_iso l (om (γ (-t))) (omS (γ (-t))) (h4 _)]`. Use `choose ν _hνn hν using hU`. Establish `hTν : ∀ t (f : Sch l), T t f = ν t • omS (γ t) f`. Introduce `t f`. Use `hν t (omS (γ t) f)` as an intermediate fact.

Simplify `this` using `only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe, hS1]`. Take `⟨f0, hf0⟩` from `exists_schwartz_one l`. Establish `hν0 : ν 0 = 1`. Establish `e` using `congrArg (fun g : Sch l => g 0) (hTν 0 f0)`. Simplify using `only [hT0, LinearMap.id_apply, hγ0, map_one, SchwartzMap.smul_apply, smul_eq_mul, hf0] at e`.

Express the relevant statement in the definitionally equal form `1 = ν 0 * (1 : Sch l →L[ℂ] Sch l) f0 0 at e`. Rewrite `e` using `[ContinuousLinearMap.one_apply, hf0, mul_one]`. Conclude with `e.symm`. Establish `hνmul : ∀ s t, ν (s + t) = ν s * ν t`. Introduce `s t`.

Use `set f := omS (γ (-(s + t))) f0`. Establish `e1 : T (s + t) f = ν (s + t) • f0` using `by rw [hTν, hS2]`. Establish `e2 : T (s + t) f = (ν s * ν t) • f0`. Rewrite using `[hTadd, LinearMap.comp_apply, hTν t, map_smul, hTν s, hmul, hS2, smul_smul, mul_comm]`. Establish `e` using `congrArg (fun g : Sch l => g 0) (e1.symm.trans e2)`.

Simplify `e` using `[hf0]`. Establish `hcontS : ContinuousAt (fun t => omS (γ t) f0) 0`. Establish `hd` using `GlobalTheory.T.tendsto_slope_metaplecticLift_schwartz l G pr om omS h3 h4 Z hZ γ hγ0 hγpr hγd f0`. Establish `h1 : Tendsto (fun t : ℝ => t • (t⁻¹ • (omS (γ t) f0 - f0))) (𝓝[≠] 0) (𝓝 ((0 : ℝ) • quad Z f0))` using `(tendsto_nhdsWithin_of_tendsto_nhds tendsto_id).smul hd`. Rewrite `h1` using `[zero_smul]`.

Establish `h2 : Tendsto (fun t : ℝ => omS (γ t) f0) (𝓝[≠] 0) (𝓝 f0)`. Establish `h1'` using `h1.add_const f0`. Rewrite `h1'` using `[zero_add]`. Use `h1'.congr' (eventually_nhdsWithin_of_forall fun t ht => ?_)` and prove the remaining obligations. Rewrite using `[smul_smul, mul_inv_cancel₀ ht, one_smul, sub_add_cancel]`.

Rewrite using `[← continuousWithinAt_compl_self, ContinuousWithinAt, hγ0, map_one]`. Conclude with `h2`. Establish `hcontS0 : ContinuousAt (fun t => omS (γ t) f0 0) 0` using `(continuous_eval l 0).continuousAt.comp hcontS`. Establish `hS00 : omS (γ 0) f0 0 ≠ 0`. Rewrite using `[hγ0, map_one, ContinuousLinearMap.one_apply, hf0]`.

Conclude with `one_ne_zero`. Establish `hνc : ContinuousAt ν 0`. Establish `hq : ContinuousAt (fun t => T t f0 0 / omS (γ t) f0 0) 0` using `(hTcont f0 0).continuousAt.div hcontS0 hS00`. Use `hq.congr ?_` and prove the remaining obligations. Use `filter_upwards [hcontS0.eventually_ne hS00] with t ht`.

Rewrite using `[hTν, SchwartzMap.smul_apply, smul_eq_mul, mul_div_cancel_right₀ _ ht]`. Take `⟨a, ha⟩` from `GlobalTheory.T.exists_hasDerivAt_zero_of_map_add_mul' ν hν0 hνmul hνc`. Use `⟨a, fun f => ?_⟩` and prove the remaining obligations. Establish `hslope` using `hasDerivAt_iff_tendsto_slope_zero.1 ha`. Simplify using `only [zero_add, hν0] at hslope`.

Establish `hd` using `GlobalTheory.T.tendsto_slope_metaplecticLift_schwartz l G pr om omS h3 h4 Z hZ γ hγ0 hγpr hγd f`. Establish `hν1 : Tendsto ν (𝓝[≠] 0) (𝓝 1)`. Rewrite using `[← hν0]`. Conclude with `hνc.tendsto.mono_left nhdsWithin_le_nhds`. Establish `hlim` using `(hν1.smul hd).add (hslope.smul_const f)`.

Rewrite `hlim` using `[one_smul, add_comm]`. Use `hlim.congr fun t => ?_` and prove the remaining obligations. Rewrite using `[hTν]`. Use extensionality with `x`. Simplify using `only [SchwartzMap.add_apply, SchwartzMap.smul_apply, SchwartzMap.sub_apply, smul_eq_mul, Complex.real_smul]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem metaplectic_scalar_derivative_nonempty (hP : _root_.GlobalTheory.FunPr.ThetaLocalInputs) (l : Type) [Fintype l] [DecidableEq l] [Nonempty l]
    (Z : Matrix (l ⊕ l) (l ⊕ l) ℝ) (hZ : Z ∈ LieAlgebra.Symplectic.sp l ℝ)
    (T : ℝ → Sch l →ₗ[ℂ] Sch l) (hT0 : T 0 = LinearMap.id) (hTadd : ∀ s t, T (s + t) = T s ∘ₗ T t)
    (hTrho : ∀ (t : ℝ) (w : l ⊕ l → ℝ) (h h₁ : Sch l), ⇑h₁ = rhoFun w ⇑h →
      ⇑(T t h₁) = rhoFun (NormedSpace.exp (t • Z) *ᵥ w) ⇑(T t h))
    (hTiso : ∀ (t : ℝ) (h : Sch l), ∫⁻ x, ‖T t h x‖ₑ ^ 2 = ∫⁻ x, ‖h x‖ₑ ^ 2)
    (hTcont : ∀ (h : Sch l) (x : EuclideanSpace ℝ l), Continuous fun t => T t h x) :
    ∃ a : ℂ, ∀ f : Sch l,
      Tendsto (fun t : ℝ => t⁻¹ • (T t f - f)) (𝓝[≠] 0) (𝓝 (a • f + quad Z f)) := by
  obtain ⟨G, _, _, _, pr, om, omS, -, -, h3, h4, -, h6⟩ := hP.realMetaplecticRepresentation l
  obtain ⟨γ, -, hγ0, hγadd, hγpr, hγd⟩ := h6 Z hZ
  have hmul : ∀ s t (f : Sch l), omS (γ s) (omS (γ t) f) = omS (γ (s + t)) f := by
    intro s t f
    rw [hγadd, map_mul]
    rfl
  have hS1 : ∀ t (f : Sch l), omS (γ (-t)) (omS (γ t) f) = f := by
    intro t f
    rw [hmul, neg_add_cancel, hγ0, map_one]
    rfl
  have hS2 : ∀ t (f : Sch l), omS (γ t) (omS (γ (-t)) f) = f := by
    intro t f
    rw [hmul, add_neg_cancel, hγ0, map_one]
    rfl
  have hmat : ∀ t (w : l ⊕ l → ℝ), NormedSpace.exp (t • Z) *ᵥ ((pr (γ (-t)) : Matrix (l ⊕ l) (l ⊕ l) ℝ) *ᵥ w) = w := by
    intro t w
    have e : pr (γ t) * pr (γ (-t)) = 1 := by rw [← map_mul, ← hγadd, add_neg_cancel, hγ0, map_one]
    have e' : (pr (γ t) : Matrix (l ⊕ l) (l ⊕ l) ℝ) * (pr (γ (-t)) : Matrix (l ⊕ l) (l ⊕ l) ℝ) = 1 :=
      congrArg (fun g : Matrix.symplecticGroup l ℝ => (g : Matrix (l ⊕ l) (l ⊕ l) ℝ)) e
    rw [← hγpr t, Matrix.mulVec_mulVec, e', Matrix.one_mulVec]
  have hU : ∀ t, ∃ a : ℂ, ‖a‖ = 1 ∧ ∀ h, (T t ∘ₗ (omS (γ (-t)) : Sch l →ₗ[ℂ] Sch l)) h = a • h := by
    intro t
    refine _root_.GlobalTheory.T.real_weil_representation_schur_scalar hP l _ (fun w h h₁ hh => ?_) (fun h => ?_)
    · simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe]
      rw [hTrho t _ _ _ (intertwine_fun l _ (om (γ (-t))) (omS (γ (-t))) (h3 _) (h4 _) w h h₁ hh), hmat]
    · simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe]
      rw [hTiso, lintegral_iso l (om (γ (-t))) (omS (γ (-t))) (h4 _)]
  choose ν _hνn hν using hU
  have hTν : ∀ t (f : Sch l), T t f = ν t • omS (γ t) f := by
    intro t f
    have := hν t (omS (γ t) f)
    simpa only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe, hS1] using this
  obtain ⟨f0, hf0⟩ := exists_schwartz_one l
  have hν0 : ν 0 = 1 := by
    have e := congrArg (fun g : Sch l => g 0) (hTν 0 f0)
    simp only [hT0, LinearMap.id_apply, hγ0, map_one, SchwartzMap.smul_apply, smul_eq_mul, hf0] at e
    change 1 = ν 0 * (1 : Sch l →L[ℂ] Sch l) f0 0 at e
    rw [ContinuousLinearMap.one_apply, hf0, mul_one] at e
    exact e.symm
  have hνmul : ∀ s t, ν (s + t) = ν s * ν t := by
    intro s t
    set f := omS (γ (-(s + t))) f0
    have e1 : T (s + t) f = ν (s + t) • f0 := by rw [hTν, hS2]
    have e2 : T (s + t) f = (ν s * ν t) • f0 := by
      rw [hTadd, LinearMap.comp_apply, hTν t, map_smul, hTν s, hmul, hS2, smul_smul, mul_comm]
    have e := congrArg (fun g : Sch l => g 0) (e1.symm.trans e2)
    simpa [hf0] using e
  have hcontS : ContinuousAt (fun t => omS (γ t) f0) 0 := by
    have hd := GlobalTheory.T.tendsto_slope_metaplecticLift_schwartz l G pr om omS h3 h4 Z hZ γ hγ0 hγpr hγd f0
    have h1 : Tendsto (fun t : ℝ => t • (t⁻¹ • (omS (γ t) f0 - f0))) (𝓝[≠] 0) (𝓝 ((0 : ℝ) • quad Z f0)) :=
      (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id).smul hd
    rw [zero_smul] at h1
    have h2 : Tendsto (fun t : ℝ => omS (γ t) f0) (𝓝[≠] 0) (𝓝 f0) := by
      have h1' := h1.add_const f0
      rw [zero_add] at h1'
      refine h1'.congr' (eventually_nhdsWithin_of_forall fun t ht => ?_)
      rw [smul_smul, mul_inv_cancel₀ ht, one_smul, sub_add_cancel]
    rw [← continuousWithinAt_compl_self, ContinuousWithinAt, hγ0, map_one]
    exact h2
  have hcontS0 : ContinuousAt (fun t => omS (γ t) f0 0) 0 := (continuous_eval l 0).continuousAt.comp hcontS
  have hS00 : omS (γ 0) f0 0 ≠ 0 := by
    rw [hγ0, map_one, ContinuousLinearMap.one_apply, hf0]
    exact one_ne_zero
  have hνc : ContinuousAt ν 0 := by
    have hq : ContinuousAt (fun t => T t f0 0 / omS (γ t) f0 0) 0 :=
      (hTcont f0 0).continuousAt.div hcontS0 hS00
    refine hq.congr ?_
    filter_upwards [hcontS0.eventually_ne hS00] with t ht
    rw [hTν, SchwartzMap.smul_apply, smul_eq_mul, mul_div_cancel_right₀ _ ht]
  obtain ⟨a, ha⟩ := GlobalTheory.T.exists_hasDerivAt_zero_of_map_add_mul' ν hν0 hνmul hνc
  refine ⟨a, fun f => ?_⟩
  have hslope := hasDerivAt_iff_tendsto_slope_zero.1 ha
  simp only [zero_add, hν0] at hslope
  have hd := GlobalTheory.T.tendsto_slope_metaplecticLift_schwartz l G pr om omS h3 h4 Z hZ γ hγ0 hγpr hγd f
  have hν1 : Tendsto ν (𝓝[≠] 0) (𝓝 1) := by
    rw [← hν0]
    exact hνc.tendsto.mono_left nhdsWithin_le_nhds
  have hlim := (hν1.smul hd).add (hslope.smul_const f)
  rw [one_smul, add_comm] at hlim
  refine hlim.congr fun t => ?_
  rw [hTν]
  ext x
  simp only [SchwartzMap.add_apply, SchwartzMap.smul_apply, SchwartzMap.sub_apply, smul_eq_mul, Complex.real_smul]
  ring
/- English proof (translation)
Introduce `hP l _ _ Z hZ T hT0 hTadd hTrho hTiso hTcont`. Break down `isEmpty_or_nonempty l with hl | hl` into its components or cases. Conclude with `main_empty l Z T hT0 hTadd hTcont`. Conclude with `_root_.GlobalTheory.MetaplecticScalarDeriv.metaplectic_scalar_derivative_nonempty hP l Z hZ T hT0 hTadd hTrho hTiso hTcont`.
-/
theorem lift_splits_locally : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (l : Type) [Fintype l] [DecidableEq l]
    (Z : Matrix (l ⊕ l) (l ⊕ l) ℝ), Z ∈ LieAlgebra.Symplectic.sp l ℝ →
    ∀ T : ℝ → GlobalTheory.RealWeil.Sch l →ₗ[ℂ] GlobalTheory.RealWeil.Sch l, T 0 = LinearMap.id → (∀ s t, T (s + t) = T s ∘ₗ T t) →
    (∀ (t : ℝ) (w : l ⊕ l → ℝ) (h h₁ : GlobalTheory.RealWeil.Sch l), ⇑h₁ = GlobalTheory.RealWeil.rhoFun w ⇑h →
      ⇑(T t h₁) = GlobalTheory.RealWeil.rhoFun (NormedSpace.exp (t • Z) *ᵥ w) ⇑(T t h)) →
    (∀ (t : ℝ) (h : GlobalTheory.RealWeil.Sch l), ∫⁻ x, ‖T t h x‖ₑ ^ 2 = ∫⁻ x, ‖h x‖ₑ ^ 2) →
    (∀ (h : GlobalTheory.RealWeil.Sch l) (x : EuclideanSpace ℝ l), Continuous fun t => T t h x) →
    ∃ a : ℂ, ∀ f : GlobalTheory.RealWeil.Sch l,
      Filter.Tendsto (fun t : ℝ => t⁻¹ • (T t f - f)) (nhdsWithin 0 {0}ᶜ) (nhds (a • f + GlobalTheory.RealWeil.quad Z f)) := by
  intro hP l _ _ Z hZ T hT0 hTadd hTrho hTiso hTcont
  rcases isEmpty_or_nonempty l with hl | hl
  · exact main_empty l Z T hT0 hTadd hTcont
  · exact _root_.GlobalTheory.MetaplecticScalarDeriv.metaplectic_scalar_derivative_nonempty hP l Z hZ T hT0 hTadd hTrho hTiso hTcont
end GlobalTheory.MetaplecticScalarDeriv
end
end

section
open scoped Matrix
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @_root_.GlobalTheory.MetaplecticScalarDeriv.lift_splits_locally | exact _root_.GlobalTheory.MetaplecticScalarDeriv.lift_splits_locally | (intros; apply _root_.GlobalTheory.MetaplecticScalarDeriv.lift_splits_locally <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.metaplectic_lift_scalar_derivative_eq : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (l : Type) [Fintype l] [DecidableEq l]
    (Z : Matrix (l ⊕ l) (l ⊕ l) ℝ), Z ∈ LieAlgebra.Symplectic.sp l ℝ →
    ∀ T : ℝ → GlobalTheory.RealWeil.Sch l →ₗ[ℂ] GlobalTheory.RealWeil.Sch l, T 0 = LinearMap.id → (∀ s t, T (s + t) = T s ∘ₗ T t) →
    (∀ (t : ℝ) (w : l ⊕ l → ℝ) (h h₁ : GlobalTheory.RealWeil.Sch l), ⇑h₁ = GlobalTheory.RealWeil.rhoFun w ⇑h →
      ⇑(T t h₁) = GlobalTheory.RealWeil.rhoFun (NormedSpace.exp (t • Z) *ᵥ w) ⇑(T t h)) →
    (∀ (t : ℝ) (h : GlobalTheory.RealWeil.Sch l), ∫⁻ x, ‖T t h x‖ₑ ^ 2 = ∫⁻ x, ‖h x‖ₑ ^ 2) →
    (∀ (h : GlobalTheory.RealWeil.Sch l) (x : EuclideanSpace ℝ l), Continuous fun t => T t h x) →
    ∃ a : ℂ, ∀ f : GlobalTheory.RealWeil.Sch l,
      Filter.Tendsto (fun t : ℝ => t⁻¹ • (T t f - f)) (nhdsWithin 0 {0}ᶜ) (nhds (a • f + GlobalTheory.RealWeil.quad Z f)) := by
  first | exact @_root_.GlobalTheory.MetaplecticScalarDeriv.lift_splits_locally | exact _root_.GlobalTheory.MetaplecticScalarDeriv.lift_splits_locally | (intros; apply _root_.GlobalTheory.MetaplecticScalarDeriv.lift_splits_locally <;> assumption)
end
