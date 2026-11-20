import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaTranslationIntertwinerUnitary
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SetAverageProdFundamentalDomainPlaneLatticePow
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.ThetaIso

open MeasureTheory GlobalTheory.ThetaInter

section General

variable {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W] [NormedSpace ℝ W] [IsScalarTower ℝ ℂ W]
  [FiniteDimensional ℝ W] [MeasurableSpace W] [BorelSpace W] (μ : Measure W) [μ.IsAddHaarMeasure]

/- English proof (translation)
Take `⟨n, b, hb⟩` from `exists_basis hA hsp`. Establish `hb₁ : (Submodule.span ℤ (Set.range (b.map e))).toAddSubgroup = A₁`. Use extensionality with `y`. Take `⟨x, rfl⟩` from `e.surjective y`. Rewrite using `[← he, ← hb, Submodule.mem_toAddSubgroup, Submodule.mem_toAddSubgroup, Module.Basis.mem_span_iff_repr_mem, Module.Basis.mem_span_iff_repr_mem]`.

Simplify using the standard rewrite rules. Rewrite using `[mean_eq μ b hb hf, mean_eq μ (b.map e) hb₁ fun x hx z => by`. Rewrite using `[map_add, hf _ ((he _).2 (by simpa using hx))]]`. Set `ec : W ≃L[ℝ] W` to `e.toContinuousLinearEquiv`. Set `em : W ≃ᵐ W` to `ec.toHomeomorph.toMeasurableEquiv`.

Establish `hpre : ZSpan.fundamentalDomain b = em ⁻¹' ZSpan.fundamentalDomain (b.map e)`. Use extensionality with `x`. Express the relevant statement in the definitionally equal form `_ ↔ e x ∈ ZSpan.fundamentalDomain (b.map e)`. Simplify using `[ZSpan.mem_fundamentalDomain]`. Use `haveI : (μ.map em).IsAddHaarMeasure := ec.isAddHaarMeasure_map μ`.

Establish `hs` using `Measure.isAddLeftInvariant_eq_smul (μ.map em) μ`. Establish `hc0 : Measure.addHaarScalarFactor (μ.map em) μ ≠ 0` using `(Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _).ne'`. Establish `h1 : ⨍ z in em ⁻¹' ZSpan.fundamentalDomain (b.map e), f z ∂μ = ⨍ z in ZSpan.fundamentalDomain (b.map e), f (e.symm z) ∂(μ.map em)`. Rewrite using `[setAverage_eq, setAverage_eq, setIntegral_map_equiv, measureReal_def, measureReal_def, em.map_apply]`. Use `congr 2`.

Use function extensionality and compare the values at `z`. Conclude with `congrArg f (e.symm_apply_apply z).symm`. Rewrite using `[hpre, h1, hs, setAverage_eq, setAverage_eq, Measure.restrict_smul, integral_smul_nnreal_measure, measureReal_nnreal_smul_apply]`. Establish `hc1 : ((Measure.addHaarScalarFactor (μ.map em) μ : NNReal) : ℝ) ≠ 0`. Conclude with `hc0` after adjusting the coercions.

Rewrite using `[NNReal.smul_def, smul_eq_mul, smul_eq_mul, smul_eq_mul, mul_inv]`. Clear the denominators using the available nonvanishing facts.
-/
theorem mean_transport {A A₁ : AddSubgroup W} (hA : DiscreteTopology A)
    (hsp : Submodule.span ℝ (A : Set W) = ⊤) (e : W ≃ₗ[ℝ] W) (he : ∀ x, x ∈ A ↔ e x ∈ A₁)
    {f : W → ℝ} (hf : ∀ x ∈ A, ∀ z, f (z + x) = f z) :
    mean μ A₁ (fun z => f (e.symm z)) = mean μ A f := by
  obtain ⟨n, b, hb⟩ := exists_basis hA hsp
  have hb₁ : (Submodule.span ℤ (Set.range (b.map e))).toAddSubgroup = A₁ := by
    ext y
    obtain ⟨x, rfl⟩ := e.surjective y
    rw [← he, ← hb, Submodule.mem_toAddSubgroup, Submodule.mem_toAddSubgroup,
      Module.Basis.mem_span_iff_repr_mem, Module.Basis.mem_span_iff_repr_mem]
    simp
  rw [mean_eq μ b hb hf, mean_eq μ (b.map e) hb₁ fun x hx z => by
    rw [map_add, hf _ ((he _).2 (by simpa using hx))]]
  let ec : W ≃L[ℝ] W := e.toContinuousLinearEquiv
  let em : W ≃ᵐ W := ec.toHomeomorph.toMeasurableEquiv
  have hpre : ZSpan.fundamentalDomain b = em ⁻¹' ZSpan.fundamentalDomain (b.map e) := by
    ext x
    change _ ↔ e x ∈ ZSpan.fundamentalDomain (b.map e)
    simp [ZSpan.mem_fundamentalDomain]
  haveI : (μ.map em).IsAddHaarMeasure := ec.isAddHaarMeasure_map μ
  have hs := Measure.isAddLeftInvariant_eq_smul (μ.map em) μ
  have hc0 : Measure.addHaarScalarFactor (μ.map em) μ ≠ 0 :=
    (Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _).ne'
  have h1 : ⨍ z in em ⁻¹' ZSpan.fundamentalDomain (b.map e), f z ∂μ
      = ⨍ z in ZSpan.fundamentalDomain (b.map e), f (e.symm z) ∂(μ.map em) := by
    rw [setAverage_eq, setAverage_eq, setIntegral_map_equiv, measureReal_def, measureReal_def,
      em.map_apply]
    congr 2
    funext z
    exact congrArg f (e.symm_apply_apply z).symm
  rw [hpre, h1, hs, setAverage_eq, setAverage_eq, Measure.restrict_smul, integral_smul_nnreal_measure,
    measureReal_nnreal_smul_apply]
  have hc1 : ((Measure.addHaarScalarFactor (μ.map em) μ : NNReal) : ℝ) ≠ 0 := by
    exact_mod_cast hc0
  rw [NNReal.smul_def, smul_eq_mul, smul_eq_mul, smul_eq_mul, mul_inv]
  field_simp

/- English proof (translation)
Take `⟨n, b, hb⟩` from `exists_basis hA hsp`. Rewrite using `[mean_eq μ b hb hf, setAverage_eq, smul_eq_mul]`. Establish `hbd` using `ZSpan.fundamentalDomain_isBounded b`. Establish `hI : IntegrableOn f (ZSpan.fundamentalDomain b) μ` using `(hc.continuousOn.integrableOn_compact hbd.isCompact_closure).mono_set subset_closure`. Establish `hsupp : 0 < μ (Function.support f ∩ ZSpan.fundamentalDomain b)`.

Rewrite using `[pos_iff_ne_zero]`. Introduce `h`. Establish `hfd` using `ZSpan.isAddFundamentalDomain' b μ`. Establish `hz0` using `hfd.measure_zero_of_invariant (Function.support f) (fun g => ?_) h`. Conclude with `(hc.isOpen_support.measure_pos μ ⟨z₀, hz⟩).ne' hz0`.

Use extensionality with `y`. Rewrite using `[Set.mem_vadd_set_iff_neg_vadd_mem]`. Express the relevant statement in the definitionally equal form `f (-(g : W) + y) ≠ 0 ↔ f y ≠ 0`. Rewrite using `[add_comm, hf _ (A.neg_mem (hb.le g.2))]`. Use `mul_pos (inv_pos.2 ?_) ?_` and prove the remaining obligations.

Conclude with `ENNReal.toReal_pos (hsupp.trans_le (measure_mono Set.inter_subset_right)).ne' hbd.measure_lt_top.ne`. Conclude with `(setIntegral_pos_iff_support_of_nonneg_ae (Filter.Eventually.of_forall h0) hI).2 hsupp`.
-/
theorem mean_pos {A : AddSubgroup W} (hA : DiscreteTopology A)
    (hsp : Submodule.span ℝ (A : Set W) = ⊤) {f : W → ℝ} (hc : Continuous f) (h0 : ∀ z, 0 ≤ f z)
    (hf : ∀ x ∈ A, ∀ z, f (z + x) = f z) {z₀ : W} (hz : f z₀ ≠ 0) : 0 < mean μ A f := by
  obtain ⟨n, b, hb⟩ := exists_basis hA hsp
  rw [mean_eq μ b hb hf, setAverage_eq, smul_eq_mul]
  have hbd := ZSpan.fundamentalDomain_isBounded b
  have hI : IntegrableOn f (ZSpan.fundamentalDomain b) μ :=
    (hc.continuousOn.integrableOn_compact hbd.isCompact_closure).mono_set subset_closure
  have hsupp : 0 < μ (Function.support f ∩ ZSpan.fundamentalDomain b) := by
    rw [pos_iff_ne_zero]
    intro h
    have hfd := ZSpan.isAddFundamentalDomain' b μ
    have hz0 := hfd.measure_zero_of_invariant (Function.support f) (fun g => ?_) h
    · exact (hc.isOpen_support.measure_pos μ ⟨z₀, hz⟩).ne' hz0
    · ext y
      rw [Set.mem_vadd_set_iff_neg_vadd_mem]
      change f (-(g : W) + y) ≠ 0 ↔ f y ≠ 0
      rw [add_comm, hf _ (A.neg_mem (hb.le g.2))]
  refine mul_pos (inv_pos.2 ?_) ?_
  · exact ENNReal.toReal_pos (hsupp.trans_le (measure_mono Set.inter_subset_right)).ne' hbd.measure_lt_top.ne
  · exact (setIntegral_pos_iff_support_of_nonneg_ae (Filter.Eventually.of_forall h0) hI).2 hsupp

end General

/- English proof (translation)
Introduce `D cc δ hc N N' A A₁ h₁ _ u hu hA th hth`. Take `⟨f₁, s₁, d₁, c₁⟩` from `klat_facts hc h₁`. Establish `hH` using `isHerm_sesqOf D (tor0 D cc δ) N N'`. Establish `: (volume : Measure (Fin N' → Fin N → ℂ)).IsAddHaarMeasure` using `Measure.pi.isAddHaarMeasure _`. Establish `: (volume : Measure (VC D N N')).IsAddHaarMeasure` using `Measure.pi.isAddHaarMeasure _`.

Establish `t₁` using `discrete_of_selfDual hH d₁ f₁`. Establish `hF : th ∈ Formalism.L2.Th1.H.fixedBy (sesqOf D (tor0 D cc δ) N N') (al D (tor0 D cc δ)) A` using `hth.2`. Establish `hper` using `fun x hx z => rho_add_of_fixed hH c₁ hF (x := x) hx z`. Use `⟨⟨hth.1.comp u.symm.toContinuousLinearEquiv.differentiable, fun x hx z => ?_⟩, ?_, fun hne => ?_⟩` and prove the remaining obligations. Take `⟨x, rfl⟩` from `u.surjective x`.

Take `⟨z, rfl⟩` from `u.surjective z`. Use `hth.2 x ((hA x).2 hx) z` as an intermediate fact. Simplify using `only [al, U, hu, ← map_add, LinearEquiv.symm_apply_apply] at this ⊢`. Conclude with `this`. Use `mean_transport volume t₁ s₁ (u.restrictScalars ℝ) hA hper` as an intermediate fact.

Use `Eq.trans ?_ this` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `mean volume A₁ (rho (sesqOf D (tor0 D cc δ) N N') fun z => th (u.symm z)) = _`. Use `congr 1`. Use function extensionality and compare the values at `z`. Take `⟨z, rfl⟩` from `u.surjective z`.

Express the relevant statement in the definitionally equal form `‖th (u.symm (u z))‖ ^ 2 * Real.exp (-Real.pi * (Hf D _ (u z) (u z)).re) = ‖th (u.symm (u z))‖ ^ 2 * Real.exp (-Real.pi * (Hf D _ (u.symm (u z)) (u.symm (u z))).re)`. Rewrite using `[hu, u.symm_apply_apply]`. Take `⟨z₀, hz⟩` from `Function.ne_iff.1 hne`. Use `mean_pos (f := rho (sesqOf D (tor0 D cc δ) N N') th) volume t₁ s₁ (continuous_rho hH hth.1.continuous) (fun z => by unfold rho; positivity) hper (z₀ := z₀) ?_` and prove the remaining obligations. Establish `: 0 < ‖th z₀‖` using `norm_pos_iff.2 hz`.

Unfold `rho`. Check the signs of the components of the expression.
-/
theorem theta_transport : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ (N N' : ℕ) (A A₁ : AddSubgroup (VC D N N')), KLat D (tor0 D cc δ) A → KLat D (tor0 D cc δ) A₁ → ∀ (u : VC D N N' ≃ₗ[ℂ] VC D N N'), (∀ z w, Hf D (tor0 D cc δ) (u z) (u w) = Hf D (tor0 D cc δ) z w) → (∀ x, x ∈ A ↔ u x ∈ A₁) → ∀ th ∈ ThSp D (tor0 D cc δ) A, (fun z => th (u.symm z)) ∈ ThSp D (tor0 D cc δ) A₁ ∧ normSq D (tor0 D cc δ) A₁ (fun z => th (u.symm z)) = normSq D (tor0 D cc δ) A th ∧ (th ≠ 0 → 0 < normSq D (tor0 D cc δ) A th) := by
  intro D cc δ hc N N' A A₁ h₁ _ u hu hA th hth
  obtain ⟨f₁, s₁, d₁, c₁⟩ := klat_facts hc h₁
  have hH := isHerm_sesqOf D (tor0 D cc δ) N N'
  have : (volume : Measure (Fin N' → Fin N → ℂ)).IsAddHaarMeasure :=
    Measure.pi.isAddHaarMeasure _
  have : (volume : Measure (VC D N N')).IsAddHaarMeasure :=
    Measure.pi.isAddHaarMeasure _
  have t₁ := discrete_of_selfDual hH d₁ f₁
  have hF : th ∈ Formalism.L2.Th1.H.fixedBy (sesqOf D (tor0 D cc δ) N N') (al D (tor0 D cc δ)) A := hth.2
  have hper := fun x hx z => rho_add_of_fixed hH c₁ hF (x := x) hx z
  refine ⟨⟨hth.1.comp u.symm.toContinuousLinearEquiv.differentiable, fun x hx z => ?_⟩, ?_, fun hne => ?_⟩
  · obtain ⟨x, rfl⟩ := u.surjective x
    obtain ⟨z, rfl⟩ := u.surjective z
    have := hth.2 x ((hA x).2 hx) z
    simp only [al, U, hu, ← map_add, LinearEquiv.symm_apply_apply] at this ⊢
    exact this
  · have := mean_transport volume t₁ s₁ (u.restrictScalars ℝ) hA hper
    refine Eq.trans ?_ this
    change mean volume A₁ (rho (sesqOf D (tor0 D cc δ) N N') fun z => th (u.symm z)) = _
    congr 1
    funext z
    obtain ⟨z, rfl⟩ := u.surjective z
    change ‖th (u.symm (u z))‖ ^ 2 * Real.exp (-Real.pi * (Hf D _ (u z) (u z)).re) =
      ‖th (u.symm (u z))‖ ^ 2 * Real.exp (-Real.pi * (Hf D _ (u.symm (u z)) (u.symm (u z))).re)
    rw [hu, u.symm_apply_apply]
  · obtain ⟨z₀, hz⟩ := Function.ne_iff.1 hne
    refine mean_pos (f := rho (sesqOf D (tor0 D cc δ) N N') th) volume t₁ s₁ (continuous_rho hH hth.1.continuous) (fun z => by unfold rho; positivity) hper
      (z₀ := z₀) ?_
    have : 0 < ‖th z₀‖ := norm_pos_iff.2 hz
    unfold rho
    positivity

end GlobalTheory.ThetaIso
