import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.CuspDiscreteDecompositionOfTraceClass
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SetIntegralNormRmulLe
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ContinuousIntegralInvMulOfLocallyIntegrable
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsArchEquivEq
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CcGASmoothAndRderMem
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ContinuousSetIntegralConstTermOn
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsMapInfFinEquivEqProd
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOnAtTau

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta MeasureTheory Set Filter NumberField
open scoped Topology ContDiff TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ConvRDeriv

open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Orb

variable {D : D7} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {V : HSp D}
  {τ : D.what₂.Tau} {X : Matrix (Fin V.rank) (Fin V.rank) ℂ}

/- English proof (translation)
Establish `e : ∀ r : ℝ, NormedSpace.exp (r • X) ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)` using `fun r => GlobalTheory.SmoothAutCheck.exp_mem_UH (GlobalTheory.SmoothAutCheck.gramAt_unit V τ) hX r`. Unfold `oneP`. Rewrite using `[← GlobalTheory.PointAtPlaceHom.atTau_mul hθ V τ (e s) (e t), add_smul, Matrix.exp_add_of_commute _ _ (((Commute.refl X).smul_left s).smul_right t)]`.
-/
theorem oneP_add' (hθ : IsInfFam θ) (hX : X ∈ lieAt V τ) (s t : ℝ) :
    oneP θ V τ X (s + t) = oneP θ V τ X s * oneP θ V τ X t := by
  have e : ∀ r : ℝ, NormedSpace.exp (r • X) ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ) := fun r =>
    GlobalTheory.SmoothAutCheck.exp_mem_UH (GlobalTheory.SmoothAutCheck.gramAt_unit V τ) hX r
  unfold oneP
  rw [← GlobalTheory.PointAtPlaceHom.atTau_mul hθ V τ (e s) (e t), add_smul,
    Matrix.exp_add_of_commute _ _ (((Commute.refl X).smul_left s).smul_right t)]

/- English proof (translation)
Establish `hh : starFn f ∈ CcGA V` using `starFn_mem_ccAd hf`. Establish `hsm` using `ccGA_smooth_and_Rder_mem D V θ hθ _ hh`. Establish `hd0 : ∀ w, HasDerivAt (fun t : ℝ => starFn f (w * oneP θ V τ X t)) (Rder θ V τ X (starFn f) w) 0` using `fun w => (((isSmoothRealFam_oneP hθ hX).1.contDiff hh w).differentiable (by simp) 0).hasDerivAt`. Use `⟨starFn_mem_ccAd (hsm.2 τ X hX), fun z t => ?_⟩` and prove the remaining obligations. Establish `h1` using `HasDerivAt.comp_sub_const t t (by rw [sub_self]; exact hd0 (z⁻¹ * oneP θ V τ X t))`.

Establish `h2 : HasDerivAt (fun s : ℝ => starFn f (z⁻¹ * oneP θ V τ X s)) (Rder θ V τ X (starFn f) (z⁻¹ * oneP θ V τ X t)) t` using `h1.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => by`. Simplify using `only [mul_assoc, ← oneP_add' hθ hX, add_sub_cancel])`. Establish `h3` using `h2.star`. Establish `ef : (fun s => f ((oneP θ V τ X s)⁻¹ * z)) = fun s => star (starFn f (z⁻¹ * oneP θ V τ X s))`. Use function extensionality and compare the values at `s`.

Simplify using `[starFn, mul_inv_rev, Complex.star_def]`. Establish `ev : starFn (Rder θ V τ X (starFn f)) ((oneP θ V τ X t)⁻¹ * z) = star (Rder θ V τ X (starFn f) (z⁻¹ * oneP θ V τ X t))`. Simplify using `[starFn, mul_inv_rev, Complex.star_def]`. Rewrite using `[ef, ev]`. Conclude with `h3`.
-/
theorem leftDeriv (hθ : IsInfFam θ) (hX : X ∈ lieAt V τ) {f : GA D V → ℂ} (hf : f ∈ CcGA V) :
    starFn (Rder θ V τ X (starFn f)) ∈ CcGA V ∧ ∀ z t, HasDerivAt (fun s => f ((oneP θ V τ X s)⁻¹ * z))
      (starFn (Rder θ V τ X (starFn f)) ((oneP θ V τ X t)⁻¹ * z)) t := by
  have hh : starFn f ∈ CcGA V := starFn_mem_ccAd hf
  have hsm := ccGA_smooth_and_Rder_mem D V θ hθ _ hh
  have hd0 : ∀ w, HasDerivAt (fun t : ℝ => starFn f (w * oneP θ V τ X t)) (Rder θ V τ X (starFn f) w) 0 := fun w =>
    (((isSmoothRealFam_oneP hθ hX).1.contDiff hh w).differentiable (by simp) 0).hasDerivAt
  refine ⟨starFn_mem_ccAd (hsm.2 τ X hX), fun z t => ?_⟩
  have h1 := HasDerivAt.comp_sub_const t t (by rw [sub_self]; exact hd0 (z⁻¹ * oneP θ V τ X t))
  have h2 : HasDerivAt (fun s : ℝ => starFn f (z⁻¹ * oneP θ V τ X s)) (Rder θ V τ X (starFn f) (z⁻¹ * oneP θ V τ X t)) t :=
    h1.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => by
      simp only [mul_assoc, ← oneP_add' hθ hX, add_sub_cancel])
  have h3 := h2.star
  have ef : (fun s => f ((oneP θ V τ X s)⁻¹ * z)) = fun s => star (starFn f (z⁻¹ * oneP θ V τ X s)) := by
    funext s; simp [starFn, mul_inv_rev, Complex.star_def]
  have ev : starFn (Rder θ V τ X (starFn f)) ((oneP θ V τ X t)⁻¹ * z) =
      star (Rder θ V τ X (starFn f) (z⁻¹ * oneP θ V τ X t)) := by
    simp [starFn, mul_inv_rev, Complex.star_def]
  rw [ef, ev]; exact h3

/- English proof (translation)
Introduce `D V μ _ _ θ hθ f hf τ X hX`. Take `⟨hf', hD⟩` from `leftDeriv hθ hX hf`. Use `set f' := starFn (Rder θ V τ X (starFn f)) with hf'_def`. Use `set u := oneP θ V τ X with hu_def`. Establish `hu` using `isSmoothRealFam_oneP hθ hX`.

Establish `huc : Continuous u` using `hu.2.1`. Establish `hu0 : u 0 = 1` using `hu.2.2`. Take `⟨hfc, hfs⟩` from `continuous_of_mem_ccAd hf`. Take `⟨hf'c, hf's⟩` from `continuous_of_mem_ccAd hf'`. Use `⟨f', hf', ?_, fun F => ?_⟩` and prove the remaining obligations.

Use `closure_minimal (fun y hy => ?_) (isClosed_tsupport f)` and prove the remaining obligations. Assume the negation of the conclusion as `hy'`. Apply `hy` to reduce the goal to its premises. Establish `ht : Tendsto (fun s : ℝ => (u s)⁻¹ * y) (𝓝 0) (𝓝 y)`. Simplify `((huc.inv.mul continuous_const).tendsto (f := fun s : ℝ => (u s)⁻¹ * y) 0)` using `[hu0]`.

Establish `hev : (fun s : ℝ => f ((u s)⁻¹ * y)) =ᶠ[𝓝 0] fun _ => 0` using `ht.eventually (notMem_tsupport_iff_eventuallyEq.1 hy')`. Establish `h1` using `(hD y 0).deriv`. Rewrite `h1` using `[hu0, inv_one, one_mul, hev.deriv_eq, deriv_const]`. Conclude with `h1.symm`. Use `set φ := lift (GQ V) F`.

Establish `hφ : LocallyIntegrable φ μ` using `locallyIntegrable_iff.2 fun C hC => (GlobalTheory.AutomorphicL2Local.memLp_restrict_compact _ (GQ V) μ F C hC).2`. Use function extensionality and compare the values at `g`. Take `⟨M, hM⟩` from `hf'c.bounded_above_of_compact_support hf's`. Establish `hK : IsCompact ((fun p : ℝ × GA D V => g * u p.1 * p.2) '' (Metric.closedBall 0 1 ×ˢ tsupport f'))` using `((isCompact_closedBall 0 1).prod hf's.isCompact).image (by fun_prop)`. Use `set K := (fun p : ℝ × GA D V => g * u p.1 * p.2) '' (Metric.closedBall 0 1 ×ˢ tsupport f')`.

Establish `key` using `hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (x₀ := (0 : ℝ)) (F := fun t y => f ((u t)⁻¹ * (g⁻¹ * y)) * φ y) (F' := fun t y => f' ((u t)⁻¹ * (g⁻¹ * y)) * φ y) (bound := K.indicator fun y => M * ‖φ y‖) (s := Metric.closedBall 0 1) (Metric.closedBall_mem_nhds 0 zero_lt …`. Establish `e1 : (fun t : ℝ => convR μ f φ (g * u t)) = fun t => ∫ y, f ((u t)⁻¹ * (g⁻¹ * y)) * φ y ∂μ`. Use function extensionality and compare the values at `t`. Rewrite using `[convR_eq]`. Simplify using `only [mul_inv_rev, mul_assoc]`.

Establish `e2 : convR μ f' φ g = ∫ y, f' ((u 0)⁻¹ * (g⁻¹ * y)) * φ y ∂μ`. Rewrite using `[convR_eq, hu0]`. Simplify using the standard rewrite rules. Use `show deriv (fun t : ℝ => convR μ f φ (g * u t)) 0 = _`. Rewrite using `[e1, e2]`.

Conclude with `key.2.deriv`. Distinguish the cases in `hy : y ∈ K`. Rewrite using `[indicator_of_mem hy, norm_mul]`. Conclude with `mul_le_mul_of_nonneg_right (hM _) (norm_nonneg _)`. Rewrite using `[indicator_of_notMem hy, image_eq_zero_of_notMem_tsupport (f := f') fun h => hy ⟨(t, _), ⟨?_, h⟩, ?_⟩]`.

Simplify using the standard rewrite rules. Conclude with `ht`. Simplify using `[mul_assoc]`.
-/
theorem Rder_convR : ∀ {D : D7} {V : HSp D} (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsInfFam θ → ∀ {f : GA D V → ℂ}, f ∈ GlobalTheory.Orb.CcGA V → ∀ {τ : D.what₂.Tau} {X : Matrix (Fin V.rank) (Fin V.rank) ℂ}, X ∈ lieAt V τ → ∃ f' ∈ GlobalTheory.Orb.CcGA V, tsupport f' ⊆ tsupport f ∧ ∀ F : GlobalTheory.AutomorphicL2Unitary.DividedPowerChartLift V μ, Rder θ V τ X (GlobalTheory.AutomorphicL2Unitary.convR μ f (GlobalTheory.AutomorphicL2Unitary.lift (GQ V) F)) = GlobalTheory.AutomorphicL2Unitary.convR μ f' (GlobalTheory.AutomorphicL2Unitary.lift (GQ V) F) := by
  intro D V μ _ _ θ hθ f hf τ X hX
  obtain ⟨hf', hD⟩ := leftDeriv hθ hX hf
  set f' := starFn (Rder θ V τ X (starFn f)) with hf'_def
  set u := oneP θ V τ X with hu_def
  have hu := isSmoothRealFam_oneP hθ hX
  have huc : Continuous u := hu.2.1
  have hu0 : u 0 = 1 := hu.2.2
  obtain ⟨hfc, hfs⟩ := continuous_of_mem_ccAd hf
  obtain ⟨hf'c, hf's⟩ := continuous_of_mem_ccAd hf'
  refine ⟨f', hf', ?_, fun F => ?_⟩
  · refine closure_minimal (fun y hy => ?_) (isClosed_tsupport f)
    by_contra hy'
    apply hy
    have ht : Tendsto (fun s : ℝ => (u s)⁻¹ * y) (𝓝 0) (𝓝 y) := by
      simpa [hu0] using ((huc.inv.mul continuous_const).tendsto (f := fun s : ℝ => (u s)⁻¹ * y) 0)
    have hev : (fun s : ℝ => f ((u s)⁻¹ * y)) =ᶠ[𝓝 0] fun _ => 0 :=
      ht.eventually (notMem_tsupport_iff_eventuallyEq.1 hy')
    have h1 := (hD y 0).deriv
    rw [hu0, inv_one, one_mul, hev.deriv_eq, deriv_const] at h1
    exact h1.symm
  · set φ := lift (GQ V) F
    have hφ : LocallyIntegrable φ μ :=
      locallyIntegrable_iff.2 fun C hC => (GlobalTheory.AutomorphicL2Local.memLp_restrict_compact _ (GQ V) μ F C hC).2
    funext g
    obtain ⟨M, hM⟩ := hf'c.bounded_above_of_compact_support hf's
    have hK : IsCompact ((fun p : ℝ × GA D V => g * u p.1 * p.2) '' (Metric.closedBall 0 1 ×ˢ tsupport f')) :=
      ((isCompact_closedBall 0 1).prod hf's.isCompact).image (by fun_prop)
    set K := (fun p : ℝ × GA D V => g * u p.1 * p.2) '' (Metric.closedBall 0 1 ×ˢ tsupport f')
    have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (x₀ := (0 : ℝ))
      (F := fun t y => f ((u t)⁻¹ * (g⁻¹ * y)) * φ y) (F' := fun t y => f' ((u t)⁻¹ * (g⁻¹ * y)) * φ y)
      (bound := K.indicator fun y => M * ‖φ y‖) (s := Metric.closedBall 0 1) (Metric.closedBall_mem_nhds 0 zero_lt_one)
      (.of_forall fun t => (hfc.comp (by fun_prop)).aestronglyMeasurable.mul hφ.aestronglyMeasurable)
      (by simpa [hu0] using (GlobalTheory.AutomorphicL2Local.continuous_integral_inv_mul_of_locallyIntegrable hfc hfs hφ).1 g)
      ((hf'c.comp (by fun_prop)).aestronglyMeasurable.mul hφ.aestronglyMeasurable)
      (.of_forall fun y t ht => ?_)
      ((integrable_indicator_iff hK.measurableSet).2 ((hφ.integrableOn_isCompact hK).norm.const_mul M))
      (.of_forall fun y t _ => (hD (g⁻¹ * y) t).mul_const (φ y))
    · have e1 : (fun t : ℝ => convR μ f φ (g * u t)) = fun t => ∫ y, f ((u t)⁻¹ * (g⁻¹ * y)) * φ y ∂μ := by
        funext t; rw [convR_eq]; simp only [mul_inv_rev, mul_assoc]
      have e2 : convR μ f' φ g = ∫ y, f' ((u 0)⁻¹ * (g⁻¹ * y)) * φ y ∂μ := by
        rw [convR_eq, hu0]; simp
      show deriv (fun t : ℝ => convR μ f φ (g * u t)) 0 = _
      rw [e1, e2]
      exact key.2.deriv
    · by_cases hy : y ∈ K
      · rw [indicator_of_mem hy, norm_mul]
        exact mul_le_mul_of_nonneg_right (hM _) (norm_nonneg _)
      · rw [indicator_of_notMem hy, image_eq_zero_of_notMem_tsupport (f := f') fun h => hy ⟨(t, _), ⟨?_, h⟩, ?_⟩]
        · simp
        · exact ht
        · simp [mul_assoc]

end GlobalTheory.ConvRDeriv
