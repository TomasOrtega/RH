import Development.WeilBound.ThetaLifts.FrameEstimates.TowerRallisLemma

noncomputable section

namespace PositivityTheory.ThKEst

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace ExponentialLineGeneration

set_option linter.unusedSectionVars false

section Banach

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

/- English proof (translation)
Set `G : ℝ → A` to `fun t => ∫ s in (0 : ℝ)..t, g s`. Establish `hG : ∀ t, HasDerivAt G (g t) t` using `fun t => (hc.integral_hasStrictDerivAt 0 t).hasDerivAt`. Establish `hG0 : G 0 = 0` using `intervalIntegral.integral_same`. Establish `h1 : Tendsto (slope G 0) (𝓝[≠] 0) (𝓝 1)`. Use `hasDerivAt_iff_tendsto_slope.1 (hG 0)` as an intermediate fact.

Rewrite `this` using `[h0]`. Then use the resulting hypothesis. Establish `h2 : ∀ᶠ h in 𝓝[≠] (0 : ℝ), IsUnit (slope G 0 h)` using `h1 (Units.isOpen.mem_nhds isUnit_one)`. Take `⟨h, hu, hne⟩` from `(h2.and self_mem_nhdsWithin).exists`. Establish `hne' : h ≠ 0` using `hne`. Take `⟨v, hv⟩` from `hu.exists_right_inv`.

Rewrite `hv` using `[slope_def_module, hG0, sub_zero, sub_zero]`. Establish `hv' : G h * (h⁻¹ • v) = 1` using `by rw [mul_smul_comm, ← smul_mul_assoc, hv]`. Use `set u := h⁻¹ • v`. Establish `key : ∀ t, g t * G h = G (t + h) - G t`. Introduce `t`.

Establish `e1 : g t * G h = ∫ s in (0 : ℝ)..h, g (t + s)`. Simplify using `only [ha]`. Conclude with `((ContinuousLinearMap.mul ℝ A (g t)).intervalIntegral_comp_comm (hc.intervalIntegrable 0 h)).symm`. Rewrite using `[e1, intervalIntegral.integral_comp_add_left, add_zero]`. Conclude with `(intervalIntegral.integral_interval_sub_left (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _)).symm`.

Establish `e : g = fun t => (G (t + h) - G t) * u`. Use function extensionality and compare the values at `t`. Rewrite using `[← key, mul_assoc, hv', mul_one]`. Use `⟨(g h - 1) * u, fun t => ?_⟩` and prove the remaining obligations. Establish `d` using `(((hG (t + h)).comp_add_const t h).sub (hG t)).mul_const u`.

Establish `e2 : g t * ((g h - 1) * u) = (g (t + h) - g t) * u`. Rewrite using `[← mul_assoc, mul_sub, mul_one, ha]`. Rewrite using `[e2]`. Conclude with `d.congr_of_eventuallyEq (Eventually.of_forall fun s => congrFun e s)`.
-/
theorem exists_deriv {g : ℝ → A} (hc : Continuous g) (h0 : g 0 = 1) (ha : ∀ s t, g (s + t) = g s * g t) :
    ∃ Y : A, ∀ t, HasDerivAt g (g t * Y) t := by
  let G : ℝ → A := fun t => ∫ s in (0 : ℝ)..t, g s
  have hG : ∀ t, HasDerivAt G (g t) t := fun t => (hc.integral_hasStrictDerivAt 0 t).hasDerivAt
  have hG0 : G 0 = 0 := intervalIntegral.integral_same
  have h1 : Tendsto (slope G 0) (𝓝[≠] 0) (𝓝 1) := by
    have := hasDerivAt_iff_tendsto_slope.1 (hG 0)
    rwa [h0] at this
  have h2 : ∀ᶠ h in 𝓝[≠] (0 : ℝ), IsUnit (slope G 0 h) := h1 (Units.isOpen.mem_nhds isUnit_one)
  obtain ⟨h, hu, hne⟩ := (h2.and self_mem_nhdsWithin).exists
  have hne' : h ≠ 0 := hne
  obtain ⟨v, hv⟩ := hu.exists_right_inv
  rw [slope_def_module, hG0, sub_zero, sub_zero] at hv
  have hv' : G h * (h⁻¹ • v) = 1 := by rw [mul_smul_comm, ← smul_mul_assoc, hv]
  set u := h⁻¹ • v
  have key : ∀ t, g t * G h = G (t + h) - G t := by
    intro t
    have e1 : g t * G h = ∫ s in (0 : ℝ)..h, g (t + s) := by
      simp only [ha]
      exact ((ContinuousLinearMap.mul ℝ A (g t)).intervalIntegral_comp_comm (hc.intervalIntegrable 0 h)).symm
    rw [e1, intervalIntegral.integral_comp_add_left, add_zero]
    exact (intervalIntegral.integral_interval_sub_left (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _)).symm
  have e : g = fun t => (G (t + h) - G t) * u := by
    funext t
    rw [← key, mul_assoc, hv', mul_one]
  refine ⟨(g h - 1) * u, fun t => ?_⟩
  have d := (((hG (t + h)).comp_add_const t h).sub (hG t)).mul_const u
  have e2 : g t * ((g h - 1) * u) = (g (t + h) - g t) * u := by
    rw [← mul_assoc, mul_sub, mul_one, ha]
  rw [e2]
  exact d.congr_of_eventuallyEq (Eventually.of_forall fun s => congrFun e s)

/- English proof (translation)
Take `⟨Y, hY⟩` from `exists_deriv hc h0 ha`. Use `⟨Y, by simpa [h0] using hY 0, fun t => ?_⟩` and prove the remaining obligations. Establish `d : ∀ s : ℝ, HasDerivAt (fun s : ℝ => g s * NormedSpace.exp ((t - s) • Y)) 0 s`. Introduce `s`. Establish `d1` using `(hasDerivAt_exp_smul_const' (𝕂 := ℝ) Y (t - s)).scomp s ((hasDerivAt_id s).const_sub t)`.

Establish `d2` using `(hY s).mul d1`. Use `d2.congr_deriv ?_` and prove the remaining obligations. Simplify using `[mul_assoc]`. Establish `c` using `is_const_of_deriv_eq_zero (fun s => (d s).differentiableAt) (fun s => (d s).deriv) t 0`. Simplify `c` using `[h0]`.
-/
theorem exists_exp {g : ℝ → A} (hc : Continuous g) (h0 : g 0 = 1) (ha : ∀ s t, g (s + t) = g s * g t) :
    ∃ Y : A, HasDerivAt g Y 0 ∧ ∀ t, g t = NormedSpace.exp (t • Y) := by
  obtain ⟨Y, hY⟩ := exists_deriv hc h0 ha
  refine ⟨Y, by simpa [h0] using hY 0, fun t => ?_⟩
  have d : ∀ s : ℝ, HasDerivAt (fun s : ℝ => g s * NormedSpace.exp ((t - s) • Y)) 0 s := by
    intro s
    have d1 := (hasDerivAt_exp_smul_const' (𝕂 := ℝ) Y (t - s)).scomp s ((hasDerivAt_id s).const_sub t)
    have d2 := (hY s).mul d1
    refine d2.congr_deriv ?_
    simp [mul_assoc]
  have c := is_const_of_deriv_eq_zero (fun s => (d s).differentiableAt) (fun s => (d s).deriv) t 0
  simpa [h0] using c

end Banach

set_option backward.isDefEq.respectTransparency false in
/- English proof (translation)
Use `open scoped Matrix.Norms.Operator in`. Take `⟨Y, h1, h2⟩` from `exists_exp (A := Matrix (Fin d) (Fin d) ℂ) hc h0 ha`. Use `⟨Y, fun i j => ?_, fun t => ?_⟩` and prove the remaining obligations. Conclude with `(LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℝ ℂ i j : Matrix (Fin d) (Fin d) ℂ →ₗ[ℝ] ℂ)).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h1`. Rewrite using `[h2 t, Complex.coe_smul]`.
-/
theorem mat_exp {d : ℕ} {g : ℝ → Matrix (Fin d) (Fin d) ℂ} (hc : Continuous g) (h0 : g 0 = 1)
    (ha : ∀ s t, g (s + t) = g s * g t) :
    ∃ Y : Matrix (Fin d) (Fin d) ℂ, (∀ i j, HasDerivAt (fun t => g t i j) (Y i j) 0) ∧
      ∀ t : ℝ, g t = NormedSpace.exp ((t : ℂ) • Y) := by
  open scoped Matrix.Norms.Operator in
  obtain ⟨Y, h1, h2⟩ := exists_exp (A := Matrix (Fin d) (Fin d) ℂ) hc h0 ha
  refine ⟨Y, fun i j => ?_, fun t => ?_⟩
  · exact (LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℝ ℂ i j :
      Matrix (Fin d) (Fin d) ℂ →ₗ[ℝ] ℂ)).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h1
  · rw [h2 t, Complex.coe_smul]

/- English proof (translation)
Use extensionality with `i j`. Establish `d1 : HasDerivAt (fun t => ∑ l, (∑ k, g t k i * J k l) * star (g t l j)) (∑ l, ((∑ k, Y k i * J k l) * star (g 0 l j) + (∑ k, g 0 k i * J k l) * star (Y l j))) 0` using `HasDerivAt.fun_sum fun l _ => (HasDerivAt.fun_sum fun k _ => (hd k i).mul_const (J k l)).fun_mul (hd l j).star`. Establish `e : (fun t => ∑ l, (∑ k, g t k i * J k l) * star (g t l j)) = fun _ => J i j`. Use function extensionality and compare the values at `t`. Rewrite using `[← congrFun (congrFun (hu t) i) j]`.

Simplify using `only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply]`. Rewrite `d1` using `[e]`. Establish `z` using `d1.unique (hasDerivAt_const (0 : ℝ) (J i j))`. Establish `e1 : (Yᵀ * J * (g 0).map star + (g 0)ᵀ * J * Y.map star) i j = 0`. Rewrite using `[← z, Finset.sum_add_distrib]`.

Simplify using `only [Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply]`. Rewrite `e1` using `[h0, Matrix.map_one _ (star_zero _) (star_one _), Matrix.mul_one, Matrix.transpose_one, Matrix.one_mul]`. Then use the resulting hypothesis.
-/
theorem lie_of_unitary {d : ℕ} {g : ℝ → Matrix (Fin d) (Fin d) ℂ} {J Y : Matrix (Fin d) (Fin d) ℂ} (h0 : g 0 = 1)
    (hd : ∀ i j, HasDerivAt (fun t => g t i j) (Y i j) 0) (hu : ∀ t, (g t)ᵀ * J * (g t).map star = J) :
    Yᵀ * J + J * Y.map star = 0 := by
  ext i j
  have d1 : HasDerivAt (fun t => ∑ l, (∑ k, g t k i * J k l) * star (g t l j))
      (∑ l, ((∑ k, Y k i * J k l) * star (g 0 l j) + (∑ k, g 0 k i * J k l) * star (Y l j))) 0 :=
    HasDerivAt.fun_sum fun l _ => (HasDerivAt.fun_sum fun k _ => (hd k i).mul_const (J k l)).fun_mul (hd l j).star
  have e : (fun t => ∑ l, (∑ k, g t k i * J k l) * star (g t l j)) = fun _ => J i j := by
    funext t
    rw [← congrFun (congrFun (hu t) i) j]
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply]
  rw [e] at d1
  have z := d1.unique (hasDerivAt_const (0 : ℝ) (J i j))
  have e1 : (Yᵀ * J * (g 0).map star + (g 0)ᵀ * J * Y.map star) i j = 0 := by
    rw [← z, Finset.sum_add_distrib]
    simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply]
  rwa [h0, Matrix.map_one _ (star_zero _) (star_one _), Matrix.mul_one, Matrix.transpose_one, Matrix.one_mul] at e1

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

/- English proof (translation)
Express the relevant statement in the definitionally equal form `infEmb τ (evInf F w a ⊗ₜ[F] x) = _`. Rewrite using `[infEmb_tmul]`. Both sides reduce to the same expression.
-/
theorem piInf_tmul' {w : InfinitePlace F} (τ : EmbOver E w) (a : AF F) (x : E) :
    piInf τ (a ⊗ₜ[F] x) = InfinitePlace.Completion.extensionEmbedding w (a.1 w) * τ.1 x := by
  change infEmb τ (evInf F w a ⊗ₜ[F] x) = _
  rw [infEmb_tmul]
  rfl

/- English proof (translation)
Use `IsModuleTopology.continuous_of_ringHom (R := AF F) (piInf τ) ?_` and prove the remaining obligations. Establish `h : ⇑((piInf τ).comp (algebraMap (AF F) (AE F E))) = fun a : AF F => InfinitePlace.Completion.extensionEmbedding w (a.1 w)`. Use function extensionality and compare the values at `a`. Express the relevant statement in the definitionally equal form `piInf τ (a ⊗ₜ[F] (1 : E)) = _`. Rewrite using `[piInf_tmul', map_one, mul_one]`.

Rewrite using `[h]`. Conclude with `(InfinitePlace.Completion.isometry_extensionEmbedding w).continuous.comp ((continuous_apply w).comp continuous_fst)`.
-/
theorem continuous_piInf {w : InfinitePlace F} (τ : EmbOver E w) : Continuous (piInf τ) := by
  refine IsModuleTopology.continuous_of_ringHom (R := AF F) (piInf τ) ?_
  have h : ⇑((piInf τ).comp (algebraMap (AF F) (AE F E))) =
      fun a : AF F => InfinitePlace.Completion.extensionEmbedding w (a.1 w) := by
    funext a
    change piInf τ (a ⊗ₜ[F] (1 : E)) = _
    rw [piInf_tmul', map_one, mul_one]
  rw [h]
  exact (InfinitePlace.Completion.isometry_extensionEmbedding w).continuous.comp
    ((continuous_apply w).comp continuous_fst)

/- English proof (translation)
Establish `hw : w.IsReal` using `h.1.isReal w`. Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp only [map_zero, star_zero]`. Consider the case `add x y hx hy => simp only [map_add, hx, hy, star_add]`. Consider the case `tmul a x`.

Express the relevant statement in the definitionally equal form `piInf τ (a ⊗ₜ[F] σ x) = _`. Rewrite using `[piInf_tmul', piInf_tmul', h.2.2.2, star_mul', ← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply hw]`. Rewrite using `[Complex.star_def, Complex.conj_ofReal]`.
-/
theorem piInf_cA (h : IsCMExt F E σ) {w : InfinitePlace F} (τ : EmbOver E w) (z : AE F E) :
    piInf τ (cA σ z) = star (piInf τ z) := by
  have hw : w.IsReal := h.1.isReal w
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero, star_zero]
  | add x y hx hy => simp only [map_add, hx, hy, star_add]
  | tmul a x =>
    change piInf τ (a ⊗ₜ[F] σ x) = _
    rw [piInf_tmul', piInf_tmul', h.2.2.2, star_mul',
      ← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply hw]
    rw [Complex.star_def, Complex.conj_ofReal]

/- English proof (translation)
Use extensionality with `i j`. Conclude with `(piInf_tmul' τ 1 (J i j)).trans (by rw [show (1 : AF F).1 w = 1 from rfl, map_one, one_mul]; rfl)`.
-/
theorem map_incM {w : InfinitePlace F} (τ : EmbOver E w) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) :
    (incM F J).map (piInf τ) = J.map τ.1 := by
  ext i j
  exact (piInf_tmul' τ 1 (J i j)).trans (by rw [show (1 : AF F).1 w = 1 from rfl, map_one, one_mul]; rfl)

end ExponentialLineGeneration

open ExponentialLineGeneration in
/- English proof (translation)
Introduce `F E _ _ _ _ _ σ h τ d W _ γ hγ`. Establish `main : ∀ w, ∃ Y : Matrix (Fin d) (Fin d) ℂ, Yᵀ * W.J.map (τ w).1 + W.J.map (τ w).1 * Y.map star = 0 ∧ ∀ t : ℝ, (mat (γ (Multiplicative.ofAdd t))).map (piInf (τ w)) = NormedSpace.exp ((t : ℂ) • Y)`. Introduce `w`. Set `g : ℝ → Matrix (Fin d) (Fin d) ℂ` to `fun t => (mat (γ (Multiplicative.ofAdd t))).map (piInf (τ w))`. Establish `hm : Continuous (mat : UA σ W.J → Matrix (Fin d) (Fin d) (AE F E))` using `Units.continuous_val.comp continuous_subtype_val`.

Establish `hc : Continuous g` using `((hm.comp (hγ.1.comp continuous_ofAdd))).matrix_map (continuous_piInf (τ w))`. Establish `h0 : g 0 = 1`. Express the relevant statement in the definitionally equal form `(mat (γ 1)).map (piInf (τ w)) = 1`. Rewrite using `[map_one]`. Conclude with `Matrix.map_one _ (map_zero _) (map_one _)`.

Establish `ha : ∀ s t, g (s + t) = g s * g t`. Introduce `s t`. Express the relevant statement in the definitionally equal form `(mat (γ (Multiplicative.ofAdd s * Multiplicative.ofAdd t))).map (piInf (τ w)) = _`. Rewrite using `[map_mul]`. Conclude with `Matrix.map_mul`.

Take `⟨Y, h1, h2⟩` from `mat_exp hc h0 ha`. Use `⟨Y, lie_of_unitary h0 h1 fun t => ?_, h2⟩` and prove the remaining obligations. Establish `hu : (mat (γ (Multiplicative.ofAdd t)))ᵀ * incM F W.J * (mat (γ (Multiplicative.ofAdd t))).map (cA σ) = incM F W.J` using `(γ (Multiplicative.ofAdd t)).2`. Establish `e : ((mat (γ (Multiplicative.ofAdd t))).map (cA σ)).map (piInf (τ w)) = (g t).map star`. Use extensionality with `i j`.

Conclude with `piInf_cA h _ _`. Establish `hv` using `congrArg (fun M : Matrix (Fin d) (Fin d) (AE F E) => M.map (piInf (τ w))) hu`. Simplify using `only [Matrix.map_mul] at hv`. Rewrite `hv` using `[Matrix.transpose_map, map_incM, e]`. Then use the resulting hypothesis. Use `choose Y hY using main`.

Conclude with `⟨Y, fun w => (hY w).1, fun w => (hY w).2⟩`.
-/
theorem lineGen_of : LineGen := by
  intro F E _ _ _ _ _ σ h τ d W _ γ hγ
  have main : ∀ w, ∃ Y : Matrix (Fin d) (Fin d) ℂ,
      Yᵀ * W.J.map (τ w).1 + W.J.map (τ w).1 * Y.map star = 0 ∧
      ∀ t : ℝ, (mat (γ (Multiplicative.ofAdd t))).map (piInf (τ w)) = NormedSpace.exp ((t : ℂ) • Y) := by
    intro w
    let g : ℝ → Matrix (Fin d) (Fin d) ℂ := fun t => (mat (γ (Multiplicative.ofAdd t))).map (piInf (τ w))
    have hm : Continuous (mat : UA σ W.J → Matrix (Fin d) (Fin d) (AE F E)) :=
      Units.continuous_val.comp continuous_subtype_val
    have hc : Continuous g :=
      ((hm.comp (hγ.1.comp continuous_ofAdd))).matrix_map (continuous_piInf (τ w))
    have h0 : g 0 = 1 := by
      change (mat (γ 1)).map (piInf (τ w)) = 1
      rw [map_one]
      exact Matrix.map_one _ (map_zero _) (map_one _)
    have ha : ∀ s t, g (s + t) = g s * g t := by
      intro s t
      change (mat (γ (Multiplicative.ofAdd s * Multiplicative.ofAdd t))).map (piInf (τ w)) = _
      rw [map_mul]
      exact Matrix.map_mul
    obtain ⟨Y, h1, h2⟩ := mat_exp hc h0 ha
    refine ⟨Y, lie_of_unitary h0 h1 fun t => ?_, h2⟩
    have hu : (mat (γ (Multiplicative.ofAdd t)))ᵀ * incM F W.J * (mat (γ (Multiplicative.ofAdd t))).map (cA σ) =
        incM F W.J := (γ (Multiplicative.ofAdd t)).2
    have e : ((mat (γ (Multiplicative.ofAdd t))).map (cA σ)).map (piInf (τ w)) = (g t).map star := by
      ext i j
      exact piInf_cA h _ _
    have hv := congrArg (fun M : Matrix (Fin d) (Fin d) (AE F E) => M.map (piInf (τ w))) hu
    simp only [Matrix.map_mul] at hv
    rwa [Matrix.transpose_map, map_incM, e] at hv
  choose Y hY using main
  exact ⟨Y, fun w => (hY w).1, fun w => (hY w).2⟩

end PositivityTheory.ThKEst

end
