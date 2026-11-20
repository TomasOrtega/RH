import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaOn
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFinsetOfEventually
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LintegralFintypeProdEqProd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdemSmulUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSeriesFactorizableRestrictionFinite
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzMemL2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAdelicGroupTopology
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStdCharNegOneOfStandardTraceAdelicAddChar

noncomputable section

namespace GlobalTheory.ThK.CoefBound

open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Doubling GlobalTheory.ThK.Bot GlobalTheory.ThK.ConeEuler

/- English proof (translation)
Rewrite using `[L2.inner_def]`. Use `integral_congr_ae ?_` and prove the remaining obligations. Use `filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x h1 h2`. Rewrite using `[h1, h2, RCLike.inner_apply]`.
-/
theorem integral_eq_inner {α : Type} [MeasurableSpace α] {μ : Measure α} {f g : α → ℂ} (hf : MemLp f 2 μ)
    (hg : MemLp g 2 μ) : ∫ x, f x * starRingEnd ℂ (g x) ∂μ = inner ℂ (hg.toLp g) (hf.toLp f) := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x h1 h2
  rw [h1, h2, RCLike.inner_apply]

/- English proof (translation)
Establish `hn : ‖hf.toLp f‖ = ‖hg.toLp g‖`. Rewrite using `[Lp.norm_toLp, Lp.norm_toLp, eLpNorm_eq_lintegral_rpow_enorm (by norm_num) (by norm_num), eLpNorm_eq_lintegral_rpow_enorm (by norm_num) (by norm_num)]`. Simplify using `only [ENNReal.toReal_ofNat, ENNReal.rpow_ofNat]`. Rewrite using `[h]`. Rewrite using `[integral_eq_inner hf hg, integral_eq_inner hg hg, inner_self_eq_norm_sq_to_K]`.

Use `(norm_inner_le_norm _ _).trans ?_` and prove the remaining obligations. Rewrite using `[hn]`. Simplify using `[sq]`.
-/
theorem norm_integral_le {α : Type} [MeasurableSpace α] {μ : Measure α} {f g : α → ℂ} (hf : MemLp f 2 μ)
    (hg : MemLp g 2 μ) (h : ∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ = ∫⁻ x, ‖g x‖ₑ ^ 2 ∂μ) :
    ‖∫ x, f x * starRingEnd ℂ (g x) ∂μ‖ ≤ ‖∫ x, g x * starRingEnd ℂ (g x) ∂μ‖ := by
  have hn : ‖hf.toLp f‖ = ‖hg.toLp g‖ := by
    rw [Lp.norm_toLp, Lp.norm_toLp, eLpNorm_eq_lintegral_rpow_enorm (by norm_num) (by norm_num),
      eLpNorm_eq_lintegral_rpow_enorm (by norm_num) (by norm_num)]
    simp only [ENNReal.toReal_ofNat, ENNReal.rpow_ofNat]
    rw [h]
  rw [integral_eq_inner hf hg, integral_eq_inner hg hg, inner_self_eq_norm_sq_to_K]
  refine (norm_inner_le_norm _ _).trans ?_
  rw [hn]
  simp [sq]

/- English proof (translation)
The claim follows from `TopologicalSpace.metrizableSpace_of_t3_secondCountable G`.
-/
theorem metrizable_group (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [SecondCountableTopology G] : TopologicalSpace.MetrizableSpace G :=
  TopologicalSpace.metrizableSpace_of_t3_secondCountable G

open scoped Classical in

/- English proof (translation)
Establish `hl : (LinearMap.proj x0 : ((Fin n × Fin d → AF F) → ℂ) →ₗ[ℂ] ℂ) ∈ (adeleClass F).adm (Fin n × Fin d)`. Introduce `g _`. Use `⟨g (fun i => (x0 i).2) • ((BoundedContinuousFunction.evalCLM ℂ (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x0 i).1)).comp (SchwartzMap.toBoundedContinuousFunctionCLM ℂ (Fin n × Fin d → mixedEmbedding.mixedSpace F) ℂ)), fun f => ?_⟩` and prove the remaining obligations. Simplify using `only [LinearMap.proj_apply, pureA, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, smul_eq_mul]`. Rewrite using `[mul_comm]`.

Both sides reduce to the same expression. Conclude with `hW.2.2 _ hl Φ hΦ`.
-/
theorem continuous_apply_pt {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {n d : ℕ} {X : Spc F E n} {W : Spc F E d} {M : Model σ X W} {ψ : AddChar (AF F) ℂ}
    {χX χW : Chr F E} {om : Rep σ X W} (hW : M.IsWeil ψ χX χW om) (Φ : (Fin n × Fin d → AF F) → ℂ)
    (hΦ : Φ ∈ schA F (Fin n × Fin d)) (x0 : Fin n × Fin d → AF F) :
    Continuous fun p : UA σ X.J × UA σ W.J => om p Φ x0 := by
  have hl : (LinearMap.proj x0 : ((Fin n × Fin d → AF F) → ℂ) →ₗ[ℂ] ℂ) ∈ (adeleClass F).adm (Fin n × Fin d) := by
    intro g _
    refine ⟨g (fun i => (x0 i).2) • ((BoundedContinuousFunction.evalCLM ℂ
      (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x0 i).1)).comp
        (SchwartzMap.toBoundedContinuousFunctionCLM ℂ (Fin n × Fin d → mixedEmbedding.mixedSpace F) ℂ)), fun f => ?_⟩
    simp only [LinearMap.proj_apply, pureA, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, smul_eq_mul]
    rw [mul_comm]
    rfl
  exact hW.2.2 _ hl Φ hΦ

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B n d X W M χX χW om r s' r₁ s₁ hP mS hB m hm Φ hΦ h0`. Take `⟨rfl⟩` from `hB`. Use `letI : MeasurableSpace (Fin n × Fin d → AF F) := borel _`. Use `haveI : BorelSpace (Fin n × Fin d → AF F) := ⟨rfl⟩`. Use `haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele F`.

Use `haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F`. Use `haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F`. Establish `hF : IsTotallyReal F` using `hP.base.cm.1`. Establish `hW` using `GlobalTheory.WeilM.IsUWeilPair.isUSplitting hP.weil`. Establish `h2` using `GlobalTheory.WeilM.schA_memLp_two F _ m hm Φ hΦ`.

Establish `hc : Continuous Φ` using `(GlobalTheory.SplitSvN.schA_facts hF hΦ).1`. Establish `e1 : Bot.coef m om Φ 1 = ∫ x, Φ x * starRingEnd ℂ (Φ x) ∂m`. Establish `e : om ((1 : UA σ X.J), (1 : UA σ W.J)) = 1` using `map_one om`. Unfold `Bot.coef`. Rewrite using `[e]`.

Both sides reduce to the same expression. Use `⟨?_, fun g => ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[e1, integral_eq_inner h2 h2, ne_eq, inner_self_eq_zero]`. Introduce `hz`. Apply `h0` to reduce the goal to its premises.

Establish `h3 : Φ =ᵐ[m] 0`. Use `h2.coeFn_toLp` as an intermediate fact. Rewrite `this` using `[hz]`. Conclude with `this.symm.trans (Lp.coeFn_zero _ _ _)`. Conclude with `(hc.ae_eq_iff_eq m continuous_const).1 h3`.

Rewrite using `[e1]`. Conclude with `norm_integral_le (GlobalTheory.WeilM.schA_memLp_two F _ m hm _ (hW.pres (g, 1) Φ hΦ)) h2 (hW.unit m hm _ Φ hΦ)`. Take `⟨_, _, _, _⟩` from `GlobalTheory.UnitaryAdelicTop.lcsc_UA F E σ n X.J haveI : BorelSpace (UA σ X.J) := ⟨rfl⟩ haveI : TopologicalSpace.MetrizableSpace (UA σ X.J) := metrizable_group _`. Establish `hs : StronglyMeasurable (Function.uncurry fun (g : UA σ X.J) (x : Fin n × Fin d → AF F) => om (g, 1) Φ x * starRingEnd ℂ (Φ x))`. Use `stronglyMeasurable_uncurry_of_continuous_of_stronglyMeasurable (fun x => ?_) (fun g => ?_)` and prove the remaining obligations.

Conclude with `((continuous_apply_pt hP.weil Φ hΦ x).comp (continuous_id.prodMk continuous_const)).mul continuous_const`. Conclude with `(((GlobalTheory.SplitSvN.schA_facts hF (hW.pres (g, 1) Φ hΦ)).1).mul (Complex.continuous_conj.comp hc)).stronglyMeasurable`. Conclude with `(hs.integral_prod_right (ν := m)).measurable`.
-/
theorem coef_ne_zero_bound_measurable : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s' r₁ s₁ : ℕ),
    IsPair B M χX χW om r s' r₁ s₁ →
    ∀ [MeasurableSpace (Fin n × Fin d → AF F)] [BorelSpace (Fin n × Fin d → AF F)] (m : Measure (Fin n × Fin d → AF F)), m.IsAddHaarMeasure →
    ∀ Φ ∈ schA F (Fin n × Fin d), Φ ≠ 0 →
      Bot.coef m om Φ 1 ≠ 0 ∧ (∀ g, ‖Bot.coef m om Φ g‖ ≤ ‖Bot.coef m om Φ 1‖) ∧ Measurable (Bot.coef m om Φ) := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s' r₁ s₁ hP mS hB m hm Φ hΦ h0
  obtain ⟨rfl⟩ := hB
  letI : MeasurableSpace (Fin n × Fin d → AF F) := borel _
  haveI : BorelSpace (Fin n × Fin d → AF F) := ⟨rfl⟩
  haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele F
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  have hF : IsTotallyReal F := hP.base.cm.1
  have hW := GlobalTheory.WeilM.IsUWeilPair.isUSplitting hP.weil
  have h2 := GlobalTheory.WeilM.schA_memLp_two F _ m hm Φ hΦ
  have hc : Continuous Φ := (GlobalTheory.SplitSvN.schA_facts hF hΦ).1
  have e1 : Bot.coef m om Φ 1 = ∫ x, Φ x * starRingEnd ℂ (Φ x) ∂m := by
    have e : om ((1 : UA σ X.J), (1 : UA σ W.J)) = 1 := map_one om
    unfold Bot.coef
    rw [e]
    rfl
  refine ⟨?_, fun g => ?_, ?_⟩
  · rw [e1, integral_eq_inner h2 h2, ne_eq, inner_self_eq_zero]
    intro hz
    apply h0
    have h3 : Φ =ᵐ[m] 0 := by
      have := h2.coeFn_toLp
      rw [hz] at this
      exact this.symm.trans (Lp.coeFn_zero _ _ _)
    exact (hc.ae_eq_iff_eq m continuous_const).1 h3
  · rw [e1]
    exact norm_integral_le (GlobalTheory.WeilM.schA_memLp_two F _ m hm _ (hW.pres (g, 1) Φ hΦ)) h2 (hW.unit m hm _ Φ hΦ)
  · obtain ⟨_, _, _, _⟩ := GlobalTheory.UnitaryAdelicTop.lcsc_UA F E σ n X.J
    haveI : BorelSpace (UA σ X.J) := ⟨rfl⟩
    haveI : TopologicalSpace.MetrizableSpace (UA σ X.J) := metrizable_group _
    have hs : StronglyMeasurable (Function.uncurry fun (g : UA σ X.J) (x : Fin n × Fin d → AF F) =>
        om (g, 1) Φ x * starRingEnd ℂ (Φ x)) := by
      refine stronglyMeasurable_uncurry_of_continuous_of_stronglyMeasurable (fun x => ?_) (fun g => ?_)
      · exact ((continuous_apply_pt hP.weil Φ hΦ x).comp (continuous_id.prodMk continuous_const)).mul continuous_const
      · exact (((GlobalTheory.SplitSvN.schA_facts hF (hW.pres (g, 1) Φ hΦ)).1).mul
          (Complex.continuous_conj.comp hc)).stronglyMeasurable
    exact (hs.integral_prod_right (ν := m)).measurable

end GlobalTheory.ThK.CoefBound
