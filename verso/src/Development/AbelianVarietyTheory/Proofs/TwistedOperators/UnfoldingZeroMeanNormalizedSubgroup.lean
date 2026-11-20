import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.QuotientIntegrationFormulaDiscreteSubgroupLeft
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NullMeasurableSetShearImage
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HaarMapMulRightEqOfFiniteFundamentalDomainStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HaarMapConjNormalizingLatticeEqSelfStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SmulInvariantMeasureShearedProductPairGroupStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MapSwapShearedProductMeasureUnimodularStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AeExistsPairGroupSmulMemShearedDomainStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AedisjointPairGroupSmulShearedDomainStatement

open MeasureTheory

namespace GlobalTheory.UnfoldNormal

/- English proof (translation)
Introduce `H _ _ _ _ _ _ _ _ ν _ Γ N hΓ hNc hN κ 𝓝 hκ h𝓝 h𝓝t K F hKm hFm hKN hKΓ hFΓ h0 𝓕 h𝓕 hint`. Use `haveI : LocallyCompactSpace N := hNc.locallyCompactSpace`. Use `haveI : SecondCountableTopology N := TopologicalSpace.Subtype.secondCountableTopology (N : Set H)`. Use `haveI : SigmaCompactSpace N := inferInstance`. Use `haveI : SigmaFinite κ := inferInstance`.

Use `haveI : Countable (Γ.subgroupOf N) := by`. Use `Function.Injective.countable (f := fun x : Γ.subgroupOf N => (⟨(x : N), x.2⟩ : Γ)) ?_` and prove the remaining obligations. Introduce `a b hab`. Apply `Subtype.ext` to reduce the goal to its premises. Apply `Subtype.ext` to reduce the goal to its premises.

Simplify using `using congrArg (fun y : Γ => (y : H)) hab`. Establish `hR : ∀ n₀ : N, κ.map (· * n₀) = κ` using `GlobalTheory.T.haar_map_mul_right_eq_of_finite_fundamentalDomain H Γ N hΓ hNc κ 𝓝 hκ h𝓝 h𝓝t`. Establish `hI : κ.map (fun n => n⁻¹) = κ` using `by haveI : κ.IsMulRightInvariant := ⟨hR⟩`. Conclude with `(GlobalTheory.QuotDiscrete.isInvInvariant_of_isMulRightInvariant κ).inv_eq_self`. Establish `hC : ∀ γ (hγ : γ ∈ Γ), κ.map (fun n : N => (⟨γ * n * γ⁻¹, hN γ hγ n n.2⟩ : N)) = κ` using `GlobalTheory.T.haar_map_conj_normalizing_lattice_eq_self H Γ N hΓ hNc hN κ 𝓝 hκ h𝓝 h𝓝t`.

Establish `hemb : MeasurableEmbedding (shear N)` using `measurableEmbedding_shear hNc`. Use `set G := pairGroup Γ N hN with hG`. Use `set μ := (κ.prod ν).map (shear N) with hμ`. Use `haveI : Countable G := by`. Use `Function.Injective.countable (f := fun g : G => ((⟨(g : H × H).1, g.2.1⟩ : Γ), (⟨(g : H × H).2, g.2.2.1⟩ : Γ))) ?_` and prove the remaining obligations.

Introduce `a b hab`. Simplify using `only [Prod.mk.injEq, Subtype.mk.injEq] at hab`. Conclude with `Subtype.ext (Prod.ext hab.1 hab.2)`. Use `haveI : MeasurableConstSMul G (H × H) := inferInstance`. Use `haveI : SMulInvariantMeasure G (H × H) μ := GlobalTheory.T.smulInvariantMeasure_sheared_product_pairGroup H ν Γ N hNc hN κ hκ hC`.

Establish `hS : IsFundamentalDomain G (shear N '' (𝓝 ×ˢ 𝓕)) μ` using `⟨nullMeasurableSet_shear_image hNc κ ν h𝓝.nullMeasurableSet h𝓕.nullMeasurableSet, GlobalTheory.T.ae_exists_pairGroup_smul_mem_sheared_domain H ν Γ N hΓ hNc hN κ 𝓝 hκ h𝓝 hC 𝓕 h𝓕, GlobalTheory.T.aedisjoint_pairGroup_smul_sheared_domain H ν Γ N hΓ hNc hN κ 𝓝 hκ h𝓝 hC 𝓕 h𝓕⟩`. Establish `hsw : μ.map Prod.swap = μ` using `GlobalTheory.T.map_swap_sheared_product_measure_unimodular H ν N hNc κ hκ hI`. Use `set S := shear N '' (𝓝 ×ˢ 𝓕) with hSdef`. Use `set f : H → ℂ := fun x => K x * F x with hf`. Establish `hmp : MeasurePreserving (shear N) (κ.prod ν) μ` using `⟨hemb.measurable, rfl⟩`.

Establish `hsp : MeasurePreserving (Prod.swap : H × H → H × H) μ μ` using `⟨measurable_swap, hsw⟩`. Establish `hswemb : MeasurableEmbedding (Prod.swap : H × H → H × H)` using `MeasurableEquiv.prodComm.measurableEmbedding`. Set `e : G → G` to `fun g => ⟨(g : H × H).swap, by`. Take `⟨h1, h2, h3⟩` from `g.2`. Use `⟨h2, h1, ?_⟩` and prove the remaining obligations.

Establish `: (g : H × H).2 * ((g : H × H).1)⁻¹ = ((g : H × H).1 * ((g : H × H).2)⁻¹)⁻¹` using `by group`. Simplify using `only [Prod.fst_swap, Prod.snd_swap]`. Rewrite using `[this]`. Conclude with `N.inv_mem h3⟩`. Establish `he : Function.Bijective e`.

Establish `: Function.Involutive e` using `fun g => Subtype.ext (Prod.swap_swap _)`. Conclude with `this.bijective`. Establish `hS2 : IsFundamentalDomain G (Prod.swap ⁻¹' S) μ`. Use `hS.preimage_of_equiv hsp.quasiMeasurePreserving he fun g x => ?_` and prove the remaining obligations. Both sides reduce to the same expression.

Establish `hΦ : ∀ (g : G) (p : H × H), f (g • p).1 = f p.1`. Introduce `g p`. Establish `hu : (g : H × H).1 ∈ Γ` using `g.2.1`. Express the relevant statement in the definitionally equal form `K ((g : H × H).1 * p.1) * F ((g : H × H).1 * p.1) = K p.1 * F p.1`. Rewrite using `[hKΓ _ hu, hFΓ _ hu]`.

Establish `step1 : ∫ p in S, f p.1 ∂μ = ∫ p in Prod.swap ⁻¹' S, f p.1 ∂μ` using `hS.setIntegral_eq hS2 (f := fun p => f p.1) hΦ`. Establish `step2 : ∫ p in Prod.swap ⁻¹' S, f p.1 ∂μ = ∫ p in S, f p.2 ∂μ` using `hsp.setIntegral_preimage_emb hswemb (fun p => f p.2) S`. Establish `step3 : ∀ g : H × H → ℂ, ∫ p in S, g p ∂μ = ∫ q in 𝓝 ×ˢ 𝓕, g (shear N q) ∂(κ.prod ν)` using `fun g => hmp.setIntegral_image_emb hemb g _`. Establish `hint2 : IntegrableOn (fun p : H × H => f p.1) S μ`. Rewrite using `[hS.integrableOn_iff hS2 (f := fun p => f p.1) hΦ]`.

Establish `h2 : IntegrableOn (fun p : H × H => f p.2) S μ`. Rewrite using `[hmp.integrableOn_image hemb]`. Use `haveI : IsFiniteMeasure (κ.restrict 𝓝) := isFiniteMeasure_restrict.2 h𝓝t`. Express the relevant statement in the definitionally equal form `Integrable (fun q : N × H => f q.2) ((κ.prod ν).restrict (𝓝 ×ˢ 𝓕))`. Rewrite using `[← Measure.prod_restrict]`.

Conclude with `hint.comp_snd (κ.restrict 𝓝)`. Conclude with `(hsp.integrableOn_comp_preimage hswemb).2 h2`. Establish `hint3 : Integrable (fun q : N × H => f ((q.1 : H) * q.2)) ((κ.restrict 𝓝).prod (ν.restrict 𝓕))`. Rewrite using `[Measure.prod_restrict]`. Conclude with `(hmp.integrableOn_image hemb).1 hint2`.

Establish `lhs : ∫ q in 𝓝 ×ˢ 𝓕, f (shear N q).1 ∂(κ.prod ν) = 0`. Rewrite using `[← Measure.prod_restrict]`. Express the relevant statement in the definitionally equal form `∫ q : N × H, f ((q.1 : H) * q.2) ∂((κ.restrict 𝓝).prod (ν.restrict 𝓕)) = 0`. Rewrite using `[integral_prod_symm _ hint3]`. Use `integral_eq_zero_of_ae (Filter.Eventually.of_forall fun y => ?_)` and prove the remaining obligations.

Simplify using `only [shear, hf, Pi.zero_apply]`. Establish `: ∀ x : N, K ((x : H) * y) * F ((x : H) * y) = K y * F ((x : H) * y)` using `fun x => by rw [hKN _ x.2]`. Repeatedly rewrite using `[this]`. Rewrite using `[integral_const_mul, h0, mul_zero]`. Establish `rhs : ∫ q in 𝓝 ×ˢ 𝓕, f (shear N q).2 ∂(κ.prod ν) = (κ 𝓝).toReal • ∫ h in 𝓕, f h ∂ν`.

Rewrite using `[← Measure.prod_restrict]`. Simplify using `only [shear]`. Rewrite using `[integral_fun_snd, measureReal_restrict_apply_univ]`. Both sides reduce to the same expression. Establish `key : (κ 𝓝).toReal • ∫ h in 𝓕, f h ∂ν = 0`.

Establish `e1 : ∫ p in S, f p.1 ∂μ = ∫ q in 𝓝 ×ˢ 𝓕, f (shear N q).1 ∂(κ.prod ν)` using `step3 _`. Establish `e2 : ∫ p in S, f p.2 ∂μ = ∫ q in 𝓝 ×ˢ 𝓕, f (shear N q).2 ∂(κ.prod ν)` using `step3 _`. Rewrite using `[← rhs, ← e2, ← step2, ← step1, e1, lhs]`. Establish `hne : κ 𝓝 ≠ 0` using `h𝓝.measure_ne_zero (NeZero.ne κ)`. Establish `hpos : (κ 𝓝).toReal ≠ 0` using `ENNReal.toReal_ne_zero.2 ⟨hne, h𝓝t⟩`.

Conclude with `(smul_eq_zero.1 key).resolve_left hpos`.
-/
theorem unfold_zero_mean : ∀ (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H] [SecondCountableTopology H] [T2Space H] [MeasurableSpace H] [BorelSpace H] (ν : Measure H) [ν.IsHaarMeasure] (Γ N : Subgroup H), Countable Γ → IsClosed (N : Set H) → (∀ γ ∈ Γ, ∀ n ∈ N, γ * n * γ⁻¹ ∈ N) → ∀ (κ : Measure N) (𝓝 : Set N), κ.IsHaarMeasure → IsFundamentalDomain (Γ.subgroupOf N) 𝓝 κ → κ 𝓝 ≠ ⊤ → ∀ K F : H → ℂ, Measurable K → Measurable F → (∀ n ∈ N, ∀ h, K (n * h) = K h) → (∀ γ ∈ Γ, ∀ h, K (γ * h) = K h) → (∀ γ ∈ Γ, ∀ h, F (γ * h) = F h) → (∀ h, ∫ n in 𝓝, F ((n : H) * h) ∂κ = 0) → ∀ 𝓕 : Set H, IsFundamentalDomain Γ 𝓕 ν → IntegrableOn (fun h => K h * F h) 𝓕 ν → ∫ h in 𝓕, K h * F h ∂ν = 0 := by
  intro H _ _ _ _ _ _ _ _ ν _ Γ N hΓ hNc hN κ 𝓝 hκ h𝓝 h𝓝t K F hKm hFm hKN hKΓ hFΓ h0 𝓕 h𝓕 hint
  haveI : LocallyCompactSpace N := hNc.locallyCompactSpace
  haveI : SecondCountableTopology N := TopologicalSpace.Subtype.secondCountableTopology (N : Set H)
  haveI : SigmaCompactSpace N := inferInstance
  haveI : SigmaFinite κ := inferInstance
  haveI : Countable (Γ.subgroupOf N) := by
    refine Function.Injective.countable (f := fun x : Γ.subgroupOf N => (⟨(x : N), x.2⟩ : Γ)) ?_
    intro a b hab
    apply Subtype.ext; apply Subtype.ext
    simpa using congrArg (fun y : Γ => (y : H)) hab
  have hR : ∀ n₀ : N, κ.map (· * n₀) = κ := GlobalTheory.T.haar_map_mul_right_eq_of_finite_fundamentalDomain H Γ N hΓ hNc κ 𝓝 hκ h𝓝 h𝓝t
  have hI : κ.map (fun n => n⁻¹) = κ := by
    haveI : κ.IsMulRightInvariant := ⟨hR⟩
    exact (GlobalTheory.QuotDiscrete.isInvInvariant_of_isMulRightInvariant κ).inv_eq_self
  have hC : ∀ γ (hγ : γ ∈ Γ), κ.map (fun n : N => (⟨γ * n * γ⁻¹, hN γ hγ n n.2⟩ : N)) = κ :=
    GlobalTheory.T.haar_map_conj_normalizing_lattice_eq_self H Γ N hΓ hNc hN κ 𝓝 hκ h𝓝 h𝓝t
  have hemb : MeasurableEmbedding (shear N) := measurableEmbedding_shear hNc
  set G := pairGroup Γ N hN with hG
  set μ := (κ.prod ν).map (shear N) with hμ
  haveI : Countable G := by
    refine Function.Injective.countable (f := fun g : G => ((⟨(g : H × H).1, g.2.1⟩ : Γ), (⟨(g : H × H).2, g.2.2.1⟩ : Γ))) ?_
    intro a b hab
    simp only [Prod.mk.injEq, Subtype.mk.injEq] at hab
    exact Subtype.ext (Prod.ext hab.1 hab.2)
  haveI : MeasurableConstSMul G (H × H) := inferInstance
  haveI : SMulInvariantMeasure G (H × H) μ := GlobalTheory.T.smulInvariantMeasure_sheared_product_pairGroup H ν Γ N hNc hN κ hκ hC
  have hS : IsFundamentalDomain G (shear N '' (𝓝 ×ˢ 𝓕)) μ :=
    ⟨nullMeasurableSet_shear_image hNc κ ν h𝓝.nullMeasurableSet h𝓕.nullMeasurableSet,
      GlobalTheory.T.ae_exists_pairGroup_smul_mem_sheared_domain H ν Γ N hΓ hNc hN κ 𝓝 hκ h𝓝 hC 𝓕 h𝓕, GlobalTheory.T.aedisjoint_pairGroup_smul_sheared_domain H ν Γ N hΓ hNc hN κ 𝓝 hκ h𝓝 hC 𝓕 h𝓕⟩
  have hsw : μ.map Prod.swap = μ := GlobalTheory.T.map_swap_sheared_product_measure_unimodular H ν N hNc κ hκ hI
  set S := shear N '' (𝓝 ×ˢ 𝓕) with hSdef
  set f : H → ℂ := fun x => K x * F x with hf
  have hmp : MeasurePreserving (shear N) (κ.prod ν) μ := ⟨hemb.measurable, rfl⟩
  have hsp : MeasurePreserving (Prod.swap : H × H → H × H) μ μ := ⟨measurable_swap, hsw⟩
  have hswemb : MeasurableEmbedding (Prod.swap : H × H → H × H) := MeasurableEquiv.prodComm.measurableEmbedding
  let e : G → G := fun g => ⟨(g : H × H).swap, by
    obtain ⟨h1, h2, h3⟩ := g.2
    refine ⟨h2, h1, ?_⟩
    have : (g : H × H).2 * ((g : H × H).1)⁻¹ = ((g : H × H).1 * ((g : H × H).2)⁻¹)⁻¹ := by group
    simp only [Prod.fst_swap, Prod.snd_swap]
    rw [this]; exact N.inv_mem h3⟩
  have he : Function.Bijective e := by
    have : Function.Involutive e := fun g => Subtype.ext (Prod.swap_swap _)
    exact this.bijective
  have hS2 : IsFundamentalDomain G (Prod.swap ⁻¹' S) μ := by
    refine hS.preimage_of_equiv hsp.quasiMeasurePreserving he fun g x => ?_
    rfl
  have hΦ : ∀ (g : G) (p : H × H), f (g • p).1 = f p.1 := by
    intro g p
    have hu : (g : H × H).1 ∈ Γ := g.2.1
    change K ((g : H × H).1 * p.1) * F ((g : H × H).1 * p.1) = K p.1 * F p.1
    rw [hKΓ _ hu, hFΓ _ hu]
  have step1 : ∫ p in S, f p.1 ∂μ = ∫ p in Prod.swap ⁻¹' S, f p.1 ∂μ :=
    hS.setIntegral_eq hS2 (f := fun p => f p.1) hΦ
  have step2 : ∫ p in Prod.swap ⁻¹' S, f p.1 ∂μ = ∫ p in S, f p.2 ∂μ :=
    hsp.setIntegral_preimage_emb hswemb (fun p => f p.2) S
  have step3 : ∀ g : H × H → ℂ, ∫ p in S, g p ∂μ = ∫ q in 𝓝 ×ˢ 𝓕, g (shear N q) ∂(κ.prod ν) :=
    fun g => hmp.setIntegral_image_emb hemb g _

  have hint2 : IntegrableOn (fun p : H × H => f p.1) S μ := by
    rw [hS.integrableOn_iff hS2 (f := fun p => f p.1) hΦ]
    have h2 : IntegrableOn (fun p : H × H => f p.2) S μ := by
      rw [hmp.integrableOn_image hemb]
      haveI : IsFiniteMeasure (κ.restrict 𝓝) := isFiniteMeasure_restrict.2 h𝓝t
      change Integrable (fun q : N × H => f q.2) ((κ.prod ν).restrict (𝓝 ×ˢ 𝓕))
      rw [← Measure.prod_restrict]
      exact hint.comp_snd (κ.restrict 𝓝)
    exact (hsp.integrableOn_comp_preimage hswemb).2 h2
  have hint3 : Integrable (fun q : N × H => f ((q.1 : H) * q.2)) ((κ.restrict 𝓝).prod (ν.restrict 𝓕)) := by
    rw [Measure.prod_restrict]
    exact (hmp.integrableOn_image hemb).1 hint2
  have lhs : ∫ q in 𝓝 ×ˢ 𝓕, f (shear N q).1 ∂(κ.prod ν) = 0 := by
    rw [← Measure.prod_restrict]
    change ∫ q : N × H, f ((q.1 : H) * q.2) ∂((κ.restrict 𝓝).prod (ν.restrict 𝓕)) = 0
    rw [integral_prod_symm _ hint3]
    refine integral_eq_zero_of_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [shear, hf, Pi.zero_apply]
    have : ∀ x : N, K ((x : H) * y) * F ((x : H) * y) = K y * F ((x : H) * y) := fun x => by rw [hKN _ x.2]
    simp_rw [this]
    rw [integral_const_mul, h0, mul_zero]
  have rhs : ∫ q in 𝓝 ×ˢ 𝓕, f (shear N q).2 ∂(κ.prod ν) = (κ 𝓝).toReal • ∫ h in 𝓕, f h ∂ν := by
    rw [← Measure.prod_restrict]
    simp only [shear]
    rw [integral_fun_snd, measureReal_restrict_apply_univ]
    rfl
  have key : (κ 𝓝).toReal • ∫ h in 𝓕, f h ∂ν = 0 := by
    have e1 : ∫ p in S, f p.1 ∂μ = ∫ q in 𝓝 ×ˢ 𝓕, f (shear N q).1 ∂(κ.prod ν) := step3 _
    have e2 : ∫ p in S, f p.2 ∂μ = ∫ q in 𝓝 ×ˢ 𝓕, f (shear N q).2 ∂(κ.prod ν) := step3 _
    rw [← rhs, ← e2, ← step2, ← step1, e1, lhs]
  have hne : κ 𝓝 ≠ 0 := h𝓝.measure_ne_zero (NeZero.ne κ)
  have hpos : (κ 𝓝).toReal ≠ 0 := ENNReal.toReal_ne_zero.2 ⟨hne, h𝓝t⟩
  exact (smul_eq_zero.1 key).resolve_left hpos

end GlobalTheory.UnfoldNormal
