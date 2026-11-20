import ReciprocityTheory.L2DbarEstimates.LeviForms.HoloClosedNeed
import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.ChartSymmEventuallyEq

universe u

namespace ReciprocityTheory.L2DbarEstimates.I

open MeasureTheory Metric Filter Topology
open scoped ENNReal ContDiff NNReal

noncomputable section

section
variable {M : Type u} [TopologicalSpace M] [MeasurableSpace M]

def bgDens (ps : M → ℝ) (x : M) : ℝ≥0 := Real.toNNReal (Real.exp (-ps x))

def bgMeas (n : ℕ) (z : M → V n) (ps : M → ℝ) : Measure M :=
  (vol n z).withDensity (fun x => (bgDens ps x : ℝ≥0∞))

/- English proof (translation)
Establish `hm : Measurable (fun x => (bgDens ps x : ℝ≥0∞))` using `((Real.measurable_exp.comp hps.neg).real_toNNReal).coe_nnreal_ennreal`. Unfold `bgMeas wint`. Rewrite using `[lintegral_withDensity_eq_lintegral_mul_non_measurable _ hm (Filter.Eventually.of_forall fun x => ENNReal.coe_lt_top)]`. Use `lintegral_congr fun x => ?_` and prove the remaining obligations. Simplify using `only [Pi.mul_apply, bgDens]`.

Rewrite using `[← ofReal_norm_eq_enorm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num), Real.rpow_two, mul_comm (‖f x‖ ^ 2), ENNReal.ofReal_mul (Real.exp_pos _).le]`. Both sides reduce to the same expression.
-/
theorem bg_wint_eq_lintegral (n : ℕ) (z : M → V n) (ps : M → ℝ) (hps : Measurable ps) (f : M → ℂ) :
    wint n z f ps = ∫⁻ x, ‖f x‖ₑ ^ (2:ℝ) ∂bgMeas n z ps := by
  have hm : Measurable (fun x => (bgDens ps x : ℝ≥0∞)) :=
    ((Real.measurable_exp.comp hps.neg).real_toNNReal).coe_nnreal_ennreal
  unfold bgMeas wint
  rw [lintegral_withDensity_eq_lintegral_mul_non_measurable _ hm
    (Filter.Eventually.of_forall fun x => ENNReal.coe_lt_top)]
  refine lintegral_congr fun x => ?_
  simp only [Pi.mul_apply, bgDens]
  rw [← ofReal_norm_eq_enorm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num),
    Real.rpow_two, mul_comm (‖f x‖ ^ 2), ENNReal.ofReal_mul (Real.exp_pos _).le]
  rfl

/- English proof (translation)
Rewrite using `[eLpNorm_eq_lintegral_rpow_enorm (by norm_num) (by norm_num), bg_wint_eq_lintegral n z ps hps f, ENNReal.toReal_ofNat]`.
-/
theorem bg_eLpNorm_two_eq (n : ℕ) (z : M → V n) (ps : M → ℝ) (hps : Measurable ps) (f : M → ℂ) :
    eLpNorm f 2 (bgMeas n z ps) = wint n z f ps ^ (1/(2:ℝ)) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm (by norm_num) (by norm_num), bg_wint_eq_lintegral n z ps hps f,
    ENNReal.toReal_ofNat]

/- English proof (translation)
Use `⟨hf, ?_⟩` and prove the remaining obligations. Rewrite using `[bg_eLpNorm_two_eq n z ps hps f]`. Conclude with `ENNReal.rpow_lt_top_of_nonneg (by norm_num) h.ne`.
-/
theorem bg_memLp_of_wint (n : ℕ) (z : M → V n) (ps : M → ℝ) (hps : Measurable ps) (f : M → ℂ)
    (hf : AEStronglyMeasurable f (bgMeas n z ps)) (h : wint n z f ps < ⊤) :
    MemLp f 2 (bgMeas n z ps) := by
  refine ⟨hf, ?_⟩
  rw [bg_eLpNorm_two_eq n z ps hps f]
  exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) h.ne

/- English proof (translation)
Establish `h` using `hf.2`. Rewrite `h` using `[bg_eLpNorm_two_eq n z ps hps f]`. Conclude with `(ENNReal.rpow_lt_top_iff_of_pos (by norm_num)).1 h`.
-/
theorem bg_wint_lt_top_of_memLp (n : ℕ) (z : M → V n) (ps : M → ℝ) (hps : Measurable ps) (f : M → ℂ)
    (hf : MemLp f 2 (bgMeas n z ps)) : wint n z f ps < ⊤ := by
  have h := hf.2
  rw [bg_eLpNorm_two_eq n z ps hps f] at h
  exact (ENNReal.rpow_lt_top_iff_of_pos (by norm_num)).1 h

end

variable {M : Type u} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [MeasurableSpace M] [BorelSpace M]

def bgHoloSub (n : ℕ) (z : M → V n) (ps : M → ℝ) : Submodule ℂ (Lp ℂ 2 (bgMeas n z ps)) where
  carrier := {f | ∃ G, Holo n z G ∧ (f : M → ℂ) =ᵐ[bgMeas n z ps] G}
  add_mem' := by
    rintro f g ⟨F, hF, hf⟩ ⟨G, hG, hg⟩
    refine ⟨F + G, fun e he => (hF e he).add (hG e he), ?_⟩
    filter_upwards [Lp.coeFn_add f g, hf, hg] with x h1 h2 h3
    rw [h1, Pi.add_apply, Pi.add_apply, h2, h3]
  zero_mem' := ⟨0, fun e _ => differentiableOn_const (0 : ℂ), Lp.coeFn_zero _ _ _⟩
  smul_mem' := by
    rintro c f ⟨F, hF, hf⟩
    refine ⟨c • F, fun e he => (hF e he).const_smul c, ?_⟩
    filter_upwards [Lp.coeFn_smul c f, hf] with x h1 h2
    rw [h1, Pi.smul_apply, Pi.smul_apply, h2]

/- English proof (translation)
Use `isClosed_of_closure_subset fun f hf => ?_` and prove the remaining obligations. Take `⟨F, hFS, hF⟩` from `mem_closure_iff_seq_limit.1 hf`. Establish `hFS' : ∀ k, ∃ G, Holo n X.z G ∧ (F k : M → ℂ) =ᵐ[bgMeas n X.z ps] G` using `fun k => hFS k`. Use `choose G hG hGe using hFS'`. Establish `hfa` using `Lp.aestronglyMeasurable f`.

Establish `hf0m : Measurable (hfa.mk (f : M → ℂ))` using `hfa.stronglyMeasurable_mk.measurable`. Establish `hf0 : (f : M → ℂ) =ᵐ[bgMeas n X.z ps] hfa.mk (f : M → ℂ)` using `hfa.ae_eq_mk`. Establish `hw : ∀ k, wint n X.z (fun x => G k x - hfa.mk (f : M → ℂ) x) ps = (eLpNorm (⇑(F k) - ⇑f) 2 (bgMeas n X.z ps)) ^ (2 : ℝ)`. Introduce `k`. Establish `h1` using `bg_eLpNorm_two_eq n X.z ps hpsm (fun x => G k x - hfa.mk (f : M → ℂ) x)`.

Establish `h2 : eLpNorm (fun x => G k x - hfa.mk (f : M → ℂ) x) 2 (bgMeas n X.z ps) = eLpNorm (⇑(F k) - ⇑f) 2 (bgMeas n X.z ps)`. Apply `eLpNorm_congr_ae` to reduce the goal to its premises. Use `filter_upwards [hGe k, hf0] with x h3 h4`. Rewrite using `[Pi.sub_apply, h3, h4]`. Rewrite using `[← h2, h1, ← ENNReal.rpow_mul]`.

Evaluate the numerical expressions. Establish `ht` using `(Lp.tendsto_Lp_iff_tendsto_eLpNorm' F f).1 hF`. Establish `hw0 : Tendsto (fun k => wint n X.z (fun x => G k x - hfa.mk (f : M → ℂ) x) ps) atTop (𝓝 0)`. Repeatedly rewrite using `[hw]`. Use `((ENNReal.continuous_rpow_const (y := (2 : ℝ))).tendsto 0).comp ht` as an intermediate fact.

Rewrite `this` using `[ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 2)]`. Conclude with `this`. Take `⟨G0, hG0, hfe⟩` from `hC X ps G (hfa.mk (f : M → ℂ)) hps hG hf0m hw0`. Use `show ∃ G, Holo n X.z G ∧ (f : M → ℂ) =ᵐ[bgMeas n X.z ps] G`. Use `⟨G0, hG0, hf0.trans ?_⟩` and prove the remaining obligations.

Conclude with `(withDensity_absolutelyContinuous (vol n X.z) _ : bgMeas n X.z ps ≪ vol n X.z).ae_eq hfe`.
-/
theorem bgHoloSub_closed (n : ℕ) (X : EtaleStein n M) (ps : M → ℝ) (hps : SmoothR n X.z ps)
    (hpsm : Measurable ps) (hC : HoloClosedNeed n M) :
    IsClosed (bgHoloSub n X.z ps : Set (Lp ℂ 2 (bgMeas n X.z ps))) := by
  refine isClosed_of_closure_subset fun f hf => ?_
  obtain ⟨F, hFS, hF⟩ := mem_closure_iff_seq_limit.1 hf
  have hFS' : ∀ k, ∃ G, Holo n X.z G ∧ (F k : M → ℂ) =ᵐ[bgMeas n X.z ps] G := fun k => hFS k
  choose G hG hGe using hFS'
  have hfa := Lp.aestronglyMeasurable f
  have hf0m : Measurable (hfa.mk (f : M → ℂ)) := hfa.stronglyMeasurable_mk.measurable
  have hf0 : (f : M → ℂ) =ᵐ[bgMeas n X.z ps] hfa.mk (f : M → ℂ) := hfa.ae_eq_mk
  have hw : ∀ k, wint n X.z (fun x => G k x - hfa.mk (f : M → ℂ) x) ps =
      (eLpNorm (⇑(F k) - ⇑f) 2 (bgMeas n X.z ps)) ^ (2 : ℝ) := by
    intro k
    have h1 := bg_eLpNorm_two_eq n X.z ps hpsm (fun x => G k x - hfa.mk (f : M → ℂ) x)
    have h2 : eLpNorm (fun x => G k x - hfa.mk (f : M → ℂ) x) 2 (bgMeas n X.z ps) =
        eLpNorm (⇑(F k) - ⇑f) 2 (bgMeas n X.z ps) := by
      apply eLpNorm_congr_ae
      filter_upwards [hGe k, hf0] with x h3 h4
      rw [Pi.sub_apply, h3, h4]
    rw [← h2, h1, ← ENNReal.rpow_mul]
    norm_num
  have ht := (Lp.tendsto_Lp_iff_tendsto_eLpNorm' F f).1 hF
  have hw0 : Tendsto (fun k => wint n X.z (fun x => G k x - hfa.mk (f : M → ℂ) x) ps) atTop (𝓝 0) := by
    simp_rw [hw]
    have := ((ENNReal.continuous_rpow_const (y := (2 : ℝ))).tendsto 0).comp ht
    rw [ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 2)] at this
    exact this
  obtain ⟨G0, hG0, hfe⟩ := hC X ps G (hfa.mk (f : M → ℂ)) hps hG hf0m hw0
  show ∃ G, Holo n X.z G ∧ (f : M → ℂ) =ᵐ[bgMeas n X.z ps] G
  refine ⟨G0, hG0, hf0.trans ?_⟩
  exact (withDensity_absolutelyContinuous (vol n X.z) _ : bgMeas n X.z ps ≪ vol n X.z).ae_eq hfe

/- English proof (translation)
Introduce `X ps F0 hps hF0 hw`. Establish `hpsc : Continuous ps`. Use `Smooth.continuous n X.z X.isLocalHomeomorph _ hps` as an intermediate fact. Conclude with `(Complex.continuous_re.comp this).congr fun x => by simp`. Establish `hpsm : Measurable ps` using `hpsc.measurable`.

Establish `hF0L : MemLp F0 2 (bgMeas n X.z ps)` using `bg_memLp_of_wint n X.z ps hpsm F0 hF0.aestronglyMeasurable hw`. Establish `hK : IsClosed (bgHoloSub n X.z ps : Set (Lp ℂ 2 (bgMeas n X.z ps)))` using `bgHoloSub_closed n X ps hps hpsm hC`. Use `haveI : CompleteSpace (bgHoloSub n X.z ps) := hK.completeSpace_coe`. Use `set K := bgHoloSub n X.z ps with hKdef`. Use `set P : Lp ℂ 2 (bgMeas n X.z ps) := (K.orthogonalProjection (hF0L.toLp F0) : Lp ℂ 2 (bgMeas n X.z ps)) with hPdef`.

Establish `hPK : ∃ G, Holo n X.z G ∧ (P : M → ℂ) =ᵐ[bgMeas n X.z ps] G` using `(K.orthogonalProjection (hF0L.toLp F0)).2`. Take `⟨G, hG, hPG⟩` from `hPK`. Use `⟨G, hG, bg_wint_lt_top_of_memLp n X.z ps hpsm G (MemLp.ae_eq hPG (Lp.memLp P)), ?_⟩` and prove the remaining obligations. Introduce `H hH hwH`. Establish `hHc : Continuous H` using `Smooth.continuous n X.z X.isLocalHomeomorph H (Holo.smooth n X.z H hH)`.

Establish `hHL : MemLp H 2 (bgMeas n X.z ps)` using `bg_memLp_of_wint n X.z ps hpsm H hHc.aestronglyMeasurable hwH`. Establish `hHK : hHL.toLp H ∈ K` using `show ∃ G, Holo n X.z G ∧ _ from ⟨H, hH, hHL.coeFn_toLp⟩`. Establish `horth : inner ℂ (hHL.toLp H : Lp ℂ 2 (bgMeas n X.z ps)) (hF0L.toLp F0 - P) = 0` using `by first`. Consider the case `exact Submodule.inner_right_of_mem_orthogonal hHK (K.sub_starProjection_mem_orthogonal _)`. Consider the case `exact Submodule.inner_right_of_mem_orthogonal hHK (K.sub_orthogonalProjection_mem_orthogonal _)`.

Consider the case `exact Submodule.inner_right_of_mem_orthogonal hHK (sub_orthogonalProjection_mem_orthogonal _)`. Consider the case `exact orthogonalProjection_inner_eq_zero _ _ hHK`. Rewrite `horth` using `[MeasureTheory.L2.inner_def]`. Establish `hint : ∫ a, inner ℂ ((hHL.toLp H : Lp ℂ 2 (bgMeas n X.z ps)) a) ((hF0L.toLp F0 - P : Lp ℂ 2 (bgMeas n X.z ps)) a) ∂(bgMeas n X.z ps) = ∫ a, (starRingEnd ℂ) (H a) * (F0 a - G a) ∂(bgMeas n X.z ps)`. Use `integral_congr_ae ?_` and prove the remaining obligations.

Use `filter_upwards [hHL.coeFn_toLp, hF0L.coeFn_toLp, Lp.coeFn_sub (hF0L.toLp F0) P, hPG] with a h1 h2 h3 h4`. Rewrite using `[h3, Pi.sub_apply, h1, h2, h4]`. Simplify using `[RCLike.inner_apply]`. Apply the tactic sequence `try ring`. Establish `hdm : Measurable (bgDens ps)` using `(Real.measurable_exp.comp hpsm.neg).real_toNNReal`.

Establish `key : ∫ x, (F0 x - G x) * (starRingEnd ℂ) (H x) * (Real.exp (-ps x) : ℂ) ∂vol n X.z = ∫ a, (starRingEnd ℂ) (H a) * (F0 a - G a) ∂(bgMeas n X.z ps)`. Rewrite using `[bgMeas, integral_withDensity_eq_integral_smul hdm]`. Use `integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)` and prove the remaining obligations. Simplify using `only [bgDens, NNReal.smul_def, Real.coe_toNNReal _ (Real.exp_pos _).le, Complex.real_smul]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[key, ← hint]`. Conclude with `horth`.
-/
theorem bergmanExists (n : ℕ) (M : Type u) [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [MeasurableSpace M] [BorelSpace M]
    (hC : HoloClosedNeed n M) : BergmanExistsStatement n M := by
  intro X ps F0 hps hF0 hw
  have hpsc : Continuous ps := by
    have := Smooth.continuous n X.z X.isLocalHomeomorph _ hps
    exact (Complex.continuous_re.comp this).congr fun x => by simp
  have hpsm : Measurable ps := hpsc.measurable
  have hF0L : MemLp F0 2 (bgMeas n X.z ps) :=
    bg_memLp_of_wint n X.z ps hpsm F0 hF0.aestronglyMeasurable hw
  have hK : IsClosed (bgHoloSub n X.z ps : Set (Lp ℂ 2 (bgMeas n X.z ps))) :=
    bgHoloSub_closed n X ps hps hpsm hC
  haveI : CompleteSpace (bgHoloSub n X.z ps) := hK.completeSpace_coe
  set K := bgHoloSub n X.z ps with hKdef
  set P : Lp ℂ 2 (bgMeas n X.z ps) := (K.orthogonalProjection (hF0L.toLp F0) : Lp ℂ 2 (bgMeas n X.z ps))
    with hPdef
  have hPK : ∃ G, Holo n X.z G ∧ (P : M → ℂ) =ᵐ[bgMeas n X.z ps] G :=
    (K.orthogonalProjection (hF0L.toLp F0)).2
  obtain ⟨G, hG, hPG⟩ := hPK
  refine ⟨G, hG, bg_wint_lt_top_of_memLp n X.z ps hpsm G (MemLp.ae_eq hPG (Lp.memLp P)), ?_⟩
  intro H hH hwH
  have hHc : Continuous H := Smooth.continuous n X.z X.isLocalHomeomorph H (Holo.smooth n X.z H hH)
  have hHL : MemLp H 2 (bgMeas n X.z ps) :=
    bg_memLp_of_wint n X.z ps hpsm H hHc.aestronglyMeasurable hwH
  have hHK : hHL.toLp H ∈ K := show ∃ G, Holo n X.z G ∧ _ from ⟨H, hH, hHL.coeFn_toLp⟩
  have horth : inner ℂ (hHL.toLp H : Lp ℂ 2 (bgMeas n X.z ps)) (hF0L.toLp F0 - P) = 0 := by
    first
    | exact Submodule.inner_right_of_mem_orthogonal hHK (K.sub_starProjection_mem_orthogonal _)
    | exact Submodule.inner_right_of_mem_orthogonal hHK (K.sub_orthogonalProjection_mem_orthogonal _)
    | exact Submodule.inner_right_of_mem_orthogonal hHK (sub_orthogonalProjection_mem_orthogonal _)
    | exact orthogonalProjection_inner_eq_zero _ _ hHK
  rw [MeasureTheory.L2.inner_def] at horth
  have hint : ∫ a, inner ℂ ((hHL.toLp H : Lp ℂ 2 (bgMeas n X.z ps)) a)
      ((hF0L.toLp F0 - P : Lp ℂ 2 (bgMeas n X.z ps)) a) ∂(bgMeas n X.z ps) =
      ∫ a, (starRingEnd ℂ) (H a) * (F0 a - G a) ∂(bgMeas n X.z ps) := by
    refine integral_congr_ae ?_
    filter_upwards [hHL.coeFn_toLp, hF0L.coeFn_toLp, Lp.coeFn_sub (hF0L.toLp F0) P, hPG] with a h1 h2 h3 h4
    rw [h3, Pi.sub_apply, h1, h2, h4]
    simp [RCLike.inner_apply]
    try ring
  have hdm : Measurable (bgDens ps) := (Real.measurable_exp.comp hpsm.neg).real_toNNReal
  have key : ∫ x, (F0 x - G x) * (starRingEnd ℂ) (H x) * (Real.exp (-ps x) : ℂ) ∂vol n X.z =
      ∫ a, (starRingEnd ℂ) (H a) * (F0 a - G a) ∂(bgMeas n X.z ps) := by
    rw [bgMeas, integral_withDensity_eq_integral_smul hdm]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [bgDens, NNReal.smul_def, Real.coe_toNNReal _ (Real.exp_pos _).le, Complex.real_smul]
    ring
  rw [key, ← hint]
  exact horth

end

end ReciprocityTheory.L2DbarEstimates.I
