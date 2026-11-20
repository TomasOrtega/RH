import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.UnipotentBlockPairs

open MeasureTheory NumberField Set Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq
open scoped ENNReal NumberField.AdeleRing InnerProductSpace ComplexConjugate
open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial

/- English proof (translation)
Establish `h` using `(isFiniteMeasure_quotientMeasure (K := K) (n := n) μ).measure_univ_lt_top`. Rewrite `h` using `[quotientMeasure_univ μ (isFundamentalDomain_fundamentalDomain _ μ)]`. Conclude with `⟨by rwa [Measure.restrict_apply_univ]⟩`.
-/
private theorem finFd {K : Type} [Field K] [NumberField K] {n : ℕ} (μ : Measure (G1 K n)) [μ.IsHaarMeasure] :
    IsFiniteMeasure (fd μ) := by
  have h := (isFiniteMeasure_quotientMeasure (K := K) (n := n) μ).measure_univ_lt_top
  rw [quotientMeasure_univ μ (isFundamentalDomain_fundamentalDomain _ μ)] at h
  exact ⟨by rwa [Measure.restrict_apply_univ]⟩

/- English proof (translation)
Rewrite using `[L2.inner_def, integral_quotientMeasure]`. Use `integral_congr_ae ?_` and prove the remaining obligations. Use `filter_upwards [ae_restrict_of_ae hv, ae_restrict_of_ae hw] with y h1 h2`. Rewrite using `[h1, h2, RCLike.inner_apply, mul_comm]`.
-/
private theorem orth {K : Type} [Field K] [NumberField K] {n : ℕ} {μ : Measure (G1 K n)} {v w : L2 μ}
    {φ ψ : G1 K n → ℂ} (hv : Reps μ v φ) (hw : Reps μ w ψ) :
    ∫ m, conj (φ m) * ψ m ∂fd μ = ⟪v, w⟫_ℂ := by
  rw [L2.inner_def, integral_quotientMeasure]
  refine integral_congr_ae ?_
  filter_upwards [ae_restrict_of_ae hv, ae_restrict_of_ae hw] with y h1 h2
  rw [h1, h2, RCLike.inner_apply, mul_comm]

/- English proof (translation)
Establish `h1` using `(quasiMeasurePreserving_mk (Gam K n) μ).ae (coeFn_rightRegularRep (Gam K n) μ g v)`. Establish `h2` using `(measurePreserving_mul_right μ g).quasiMeasurePreserving.ae h`. Use `filter_upwards [h1, h2] with y e1 e2`. Rewrite using `[e1]`. Conclude with `e2`.
-/
private theorem repsRight {K : Type} [Field K] [NumberField K] {n : ℕ} (μ : Measure (G1 K n)) [μ.IsHaarMeasure]
    {v : L2 μ} {φ : G1 K n → ℂ} (h : Reps μ v φ) (g : G1 K n) :
    Reps μ (rightRegularRep (Gam K n) μ g v) (fun y => φ (y * g)) := by
  have h1 := (quasiMeasurePreserving_mk (Gam K n) μ).ae (coeFn_rightRegularRep (Gam K n) μ g v)
  have h2 := (measurePreserving_mul_right μ g).quasiMeasurePreserving.ae h
  filter_upwards [h1, h2] with y e1 e2
  rw [e1]
  exact e2

/- English proof (translation)
Use `isFiniteMeasure_quotientMeasure (K := K) (n := n) μ` as an intermediate fact. Establish `hs : Function.Surjective (mk (Gam K n))` using `mk_surjective (Gam K n)`. Set `Fb : RightCosetSpace (Gam K n) → ℂ` to `fun q => F (Function.surjInv hs q)`. Establish `hFb : ∀ y, Fb (mk (Gam K n) y) = F y`. Introduce `y`.

Take `⟨γ, hγ⟩` from `mk_eq_mk_iff.1 (Function.surjInv_eq hs (mk (Gam K n) y))`. Use `show F (Function.surjInv hs _) = F y`. Rewrite using `[← hγ]`. Conclude with `hi γ γ.2 y`. Establish `hq : IsQuotientMap (mk (Gam K n))` using `(isOpenMap_mk _).isQuotientMap (continuous_mk _) hs`.

Establish `hFc : Continuous Fb` using `hq.continuous_iff.2 (by`. Establish `: Fb ∘ mk (Gam K n) = F` using `funext hFb`. Rewrite using `[this]`. Conclude with `hc)`. Establish `hm : MemLp Fb 2 (quotientMeasure (Gam K n) μ)` using `MemLp.of_bound hFc.aestronglyMeasurable C (Eventually.of_forall fun q => by`.

Take `⟨y, rfl⟩` from `hs q`. Rewrite using `[hFb]`. Conclude with `hb y)`. Use `⟨hm.toLp _, ?_⟩` and prove the remaining obligations. Use `filter_upwards [(quasiMeasurePreserving_mk (Gam K n) μ).ae hm.coeFn_toLp] with y hy`.

Rewrite using `[hy, hFb]`.
-/
private theorem classOf {K : Type} [Field K] [NumberField K] {n : ℕ} (μ : Measure (G1 K n)) [μ.IsHaarMeasure]
    {F : G1 K n → ℂ} (hc : Continuous F) {C : ℝ} (hb : ∀ m, ‖F m‖ ≤ C)
    (hi : ∀ γ ∈ Gam K n, ∀ m, F (γ * m) = F m) : ∃ v : L2 μ, Reps μ v F := by
  have := isFiniteMeasure_quotientMeasure (K := K) (n := n) μ
  have hs : Function.Surjective (mk (Gam K n)) := mk_surjective (Gam K n)
  let Fb : RightCosetSpace (Gam K n) → ℂ := fun q => F (Function.surjInv hs q)
  have hFb : ∀ y, Fb (mk (Gam K n) y) = F y := by
    intro y
    obtain ⟨γ, hγ⟩ := mk_eq_mk_iff.1 (Function.surjInv_eq hs (mk (Gam K n) y))
    show F (Function.surjInv hs _) = F y
    rw [← hγ]
    exact hi γ γ.2 y
  have hq : IsQuotientMap (mk (Gam K n)) := (isOpenMap_mk _).isQuotientMap (continuous_mk _) hs
  have hFc : Continuous Fb := hq.continuous_iff.2 (by
    have : Fb ∘ mk (Gam K n) = F := funext hFb
    rw [this]
    exact hc)
  have hm : MemLp Fb 2 (quotientMeasure (Gam K n) μ) :=
    MemLp.of_bound hFc.aestronglyMeasurable C (Eventually.of_forall fun q => by
      obtain ⟨y, rfl⟩ := hs q
      rw [hFb]
      exact hb y)
  refine ⟨hm.toLp _, ?_⟩
  filter_upwards [(quasiMeasurePreserving_mk (Gam K n) μ).ae hm.coeFn_toLp] with y hy
  rw [hy, hFb]

/- English proof (translation)
Use `isFiniteMeasure_quotientMeasure (K := K) (n := n) μ` as an intermediate fact. Establish `h : Integrable (w : RightCosetSpace (Gam K n) → ℂ) (quotientMeasure (Gam K n) μ)` using `(Lp.memLp w).integrable one_le_two`. Establish `h' : Integrable (w : RightCosetSpace (Gam K n) → ℂ) (Measure.map (mk (Gam K n)) (fd μ))` using `h`. Conclude with `h'.comp_measurable (measurable_mk _)`.
-/
private theorem intW {K : Type} [Field K] [NumberField K] {n : ℕ} (μ : Measure (G1 K n)) [μ.IsHaarMeasure]
    (w : L2 μ) : Integrable (fun y => (w : RightCosetSpace (Gam K n) → ℂ) (mk (Gam K n) y)) (fd μ) := by
  have := isFiniteMeasure_quotientMeasure (K := K) (n := n) μ
  have h : Integrable (w : RightCosetSpace (Gam K n) → ℂ) (quotientMeasure (Gam K n) μ) :=
    (Lp.memLp w).integrable one_le_two
  have h' : Integrable (w : RightCosetSpace (Gam K n) → ℂ) (Measure.map (mk (Gam K n)) (fd μ)) := h
  exact h'.comp_measurable (measurable_mk _)

/- English proof (translation)
Introduce `K _ _ n μ _ τ hτ φ hφ ⟨C, hC⟩ hΓ ⟨v, hvτ, hv⟩ U _ _ _ _ _ lam _ c x hc hx`. Use `haveI := finFd μ`. Take `⟨Cc, hCc⟩` from `isCompact_univ.exists_bound_of_continuousOn hc.continuousOn`. Establish `hC0 : 0 ≤ C` using `(norm_nonneg _).trans (hC 1)`. Establish `hB : ∀ (m : G1 K n) (u : U), ‖c u * φ (m * x u)‖ ≤ Cc * C` using `fun m u => by`.

Rewrite using `[norm_mul]`. Conclude with `mul_le_mul (hCc u (mem_univ u)) (hC _) (norm_nonneg _) ((norm_nonneg _).trans (hCc u (mem_univ u)))`. Establish `hcont2 : Continuous fun p : G1 K n × U => c p.2 * φ (p.1 * x p.2)` using `by fun_prop`. Establish `hFc : Continuous fun m : G1 K n => ∫ u, c u * φ (m * x u) ∂lam` using `continuous_of_dominated (bound := fun _ => Cc * C) (fun m => (hcont2.comp (Continuous.prodMk_right m)).aestronglyMeasurable) (fun m => ae_of_all _ fun u => hB m u) (integrable_const _) (ae_of_all _ fun u => hcont2.comp (continuous_id.prodMk continuous_const))`. Establish `hFb : ∀ m : G1 K n, ‖∫ u, c u * φ (m * x u) ∂lam‖ ≤ Cc * C * lam.real univ` using `fun m => norm_integral_le_of_norm_le_const (ae_of_all _ fun u => hB m u)`.

Take `⟨v', hv'⟩` from `classOf μ hFc hFb (fun γ hγ m => by`. Simplify using `only [mul_assoc, hΓ γ hγ])`. Use `⟨v', ?_, hv'⟩` and prove the remaining obligations. Use `haveI : CompleteSpace τ := hτ.closed.completeSpace_coe`. Rewrite using `[← τ.orthogonal_orthogonal, Submodule.mem_orthogonal]`.

Introduce `w hw`. Establish `hW : Reps μ w fun y => (w : RightCosetSpace (Gam K n) → ℂ) (mk (Gam K n) y)` using `ae_of_all _ fun _ => rfl`. Rewrite using `[← orth hW hv']`. Use `set W : G1 K n → ℂ := fun y => (w : RightCosetSpace (Gam K n) → ℂ) (mk (Gam K n) y) with hWd`. Establish `hWi : Integrable W (fd μ)` using `intW μ w`.

Establish `hint : Integrable (Function.uncurry fun (y : G1 K n) (u : U) => conj (W y) * (c u * φ (y * x u))) ((fd μ).prod lam)`. Establish `h1 : Integrable (fun p : G1 K n × U => conj (W p.1)) ((fd μ).prod lam)` using `((Complex.conjCLE : ℂ →L[ℝ] ℂ).integrable_comp hWi).comp_fst lam`. Conclude with `h1.mul_bdd (c := Cc * C) hcont2.aestronglyMeasurable (ae_of_all _ fun p => hB p.1 p.2)`. Repeatedly rewrite using `[← integral_const_mul]`. Rewrite using `[integral_integral_swap hint]`.

Establish `hz : ∀ u, ∫ y, conj (W y) * (c u * φ (y * x u)) ∂fd μ = 0` using `fun u => by`. Establish `e : ∀ y, conj (W y) * (c u * φ (y * x u)) = c u * (conj (W y) * φ (y * x u))` using `fun y => by ring`. Repeatedly rewrite using `[e]`. Rewrite using `[integral_const_mul, orth hW (repsRight μ hv (x u)), Submodule.inner_left_of_mem_orthogonal (hτ.inv _ _ hvτ) hw, mul_zero]`. Simplify using `only [hz, integral_zero]`.
-/
theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.KX.sliceRep :
    ∀ {K : Type} [Field K] [NumberField K] {n : ℕ} (μ : Measure (G1 K n)) [μ.IsHaarMeasure] (τ : Submodule ℂ (L2 μ)), CuspIrr μ τ →
      ∀ φ : G1 K n → ℂ, Continuous φ → (∃ C : ℝ, ∀ m, ‖φ m‖ ≤ C) → (∀ γ ∈ Gam K n, ∀ m, φ (γ * m) = φ m) → (∃ v ∈ τ, Reps μ v φ) →
      ∀ (U : Type) [TopologicalSpace U] [CompactSpace U] [SecondCountableTopology U] [MeasurableSpace U] [BorelSpace U] (lam : Measure U) [IsFiniteMeasure lam]
        (c : U → ℂ) (x : U → G1 K n), Continuous c → Continuous x → ∃ v ∈ τ, Reps μ v fun m => ∫ u, c u * φ (m * x u) ∂lam := by
  intro K _ _ n μ _ τ hτ φ hφ ⟨C, hC⟩ hΓ ⟨v, hvτ, hv⟩ U _ _ _ _ _ lam _ c x hc hx
  haveI := finFd μ
  obtain ⟨Cc, hCc⟩ := isCompact_univ.exists_bound_of_continuousOn hc.continuousOn
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 1)
  have hB : ∀ (m : G1 K n) (u : U), ‖c u * φ (m * x u)‖ ≤ Cc * C := fun m u => by
    rw [norm_mul]
    exact mul_le_mul (hCc u (mem_univ u)) (hC _) (norm_nonneg _) ((norm_nonneg _).trans (hCc u (mem_univ u)))
  have hcont2 : Continuous fun p : G1 K n × U => c p.2 * φ (p.1 * x p.2) := by fun_prop
  have hFc : Continuous fun m : G1 K n => ∫ u, c u * φ (m * x u) ∂lam :=
    continuous_of_dominated (bound := fun _ => Cc * C)
      (fun m => (hcont2.comp (Continuous.prodMk_right m)).aestronglyMeasurable)
      (fun m => ae_of_all _ fun u => hB m u) (integrable_const _)
      (ae_of_all _ fun u => hcont2.comp (continuous_id.prodMk continuous_const))
  have hFb : ∀ m : G1 K n, ‖∫ u, c u * φ (m * x u) ∂lam‖ ≤ Cc * C * lam.real univ := fun m =>
    norm_integral_le_of_norm_le_const (ae_of_all _ fun u => hB m u)
  obtain ⟨v', hv'⟩ := classOf μ hFc hFb (fun γ hγ m => by
    simp only [mul_assoc, hΓ γ hγ])
  refine ⟨v', ?_, hv'⟩
  haveI : CompleteSpace τ := hτ.closed.completeSpace_coe
  rw [← τ.orthogonal_orthogonal, Submodule.mem_orthogonal]
  intro w hw
  have hW : Reps μ w fun y => (w : RightCosetSpace (Gam K n) → ℂ) (mk (Gam K n) y) := ae_of_all _ fun _ => rfl
  rw [← orth hW hv']
  set W : G1 K n → ℂ := fun y => (w : RightCosetSpace (Gam K n) → ℂ) (mk (Gam K n) y) with hWd
  have hWi : Integrable W (fd μ) := intW μ w
  have hint : Integrable (Function.uncurry fun (y : G1 K n) (u : U) => conj (W y) * (c u * φ (y * x u)))
      ((fd μ).prod lam) := by
    have h1 : Integrable (fun p : G1 K n × U => conj (W p.1)) ((fd μ).prod lam) := ((Complex.conjCLE : ℂ →L[ℝ] ℂ).integrable_comp hWi).comp_fst lam
    exact h1.mul_bdd (c := Cc * C) hcont2.aestronglyMeasurable (ae_of_all _ fun p => hB p.1 p.2)
  simp_rw [← integral_const_mul]
  rw [integral_integral_swap hint]
  have hz : ∀ u, ∫ y, conj (W y) * (c u * φ (y * x u)) ∂fd μ = 0 := fun u => by
    have e : ∀ y, conj (W y) * (c u * φ (y * x u)) = c u * (conj (W y) * φ (y * x u)) := fun y => by ring
    simp_rw [e]
    rw [integral_const_mul, orth hW (repsRight μ hv (x u)),
      Submodule.inner_left_of_mem_orthogonal (hτ.inv _ _ hvτ) hw, mul_zero]
  simp only [hz, integral_zero]
