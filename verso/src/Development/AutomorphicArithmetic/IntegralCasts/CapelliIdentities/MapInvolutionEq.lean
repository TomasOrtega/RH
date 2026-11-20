import Mathlib

open MeasureTheory in
/- English proof (translation)
Establish `h1 : φ.trans φ = ContinuousMulEquiv.refl G`. Use extensionality with `x`. Conclude with `hφ x`. Establish `h2 : mulEquivHaarChar φ * mulEquivHaarChar φ = 1`. Rewrite using `[← mulEquivHaarChar_trans, h1, mulEquivHaarChar_refl]`.

Establish `h3 : mulEquivHaarChar φ = 1`. Establish `h : (mulEquivHaarChar φ) ^ 2 = 1` using `by rw [sq, h2]`. Conclude with `(pow_eq_one_iff_of_nonneg zero_le two_ne_zero).1 h`. Establish `h4` using `mulEquivHaarChar_smul_map μ φ`. Rewrite `h4` using `[h3, one_smul]`. Then use the resulting hypothesis.
-/
private theorem UpperTheory.Reformulated.B.Qh1.map_involution_eq {G : Type*} [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] (φ : G ≃ₜ* G) (hφ : ∀ x, φ (φ x) = x) :
    μ.map φ = μ := by
  have h1 : φ.trans φ = ContinuousMulEquiv.refl G := by
    ext x
    exact hφ x
  have h2 : mulEquivHaarChar φ * mulEquivHaarChar φ = 1 := by
    rw [← mulEquivHaarChar_trans, h1, mulEquivHaarChar_refl]
  have h3 : mulEquivHaarChar φ = 1 := by
    have h : (mulEquivHaarChar φ) ^ 2 = 1 := by rw [sq, h2]
    exact (pow_eq_one_iff_of_nonneg zero_le two_ne_zero).1 h
  have h4 := mulEquivHaarChar_smul_map μ φ
  rwa [h3, one_smul] at h4

/- English proof (translation)
Introduce `G _ _ _ _ _ _ _ μ _ Γ _ F hF θ hθc hθθ hθΓ f hf hfi`. Set `φ : G ≃ₜ* G` to `{ toFun := θ invFun := θ left_inv := hθθ right_inv := hθθ map_mul' := map_mul θ continuous_toFun := hθc continuous_invFun := hθc }`. Establish `hmp : MeasureTheory.MeasurePreserving θ μ μ` using `⟨hθc.measurable, UpperTheory.Reformulated.B.Qh1.map_involution_eq μ φ hθθ⟩`. Establish `hemb : MeasurableEmbedding (θ : G → G)` using `φ.toHomeomorph.measurableEmbedding`. Set `e : Γ → Γ` to `fun γ => ⟨θ γ, hθΓ γ γ.2⟩`.

Establish `he : Function.Involutive e` using `fun γ => Subtype.ext (hθθ γ)`. Establish `hF' : MeasureTheory.IsFundamentalDomain Γ (θ ⁻¹' F) μ`. Use `hF.preimage_of_equiv hmp.quasiMeasurePreserving he.bijective ?_` and prove the remaining obligations. Introduce `γ x`. Express the relevant statement in the definitionally equal form `θ (θ γ * x) = γ * θ x`.

Rewrite using `[map_mul, hθθ]`. Establish `hg : ∀ (γ : Γ) (x : G), f (θ (γ • x)) = f (θ x)`. Introduce `γ x`. Express the relevant statement in the definitionally equal form `f (θ (γ * x)) = f (θ x)`. Rewrite using `[map_mul]`.

Conclude with `hf (e γ) (θ x)`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Establish `h1 : MeasureTheory.IntegrableOn (fun x => f (θ x)) (θ ⁻¹' F) μ` using `(hmp.integrableOn_comp_preimage hemb).2 hfi`. Conclude with `(hF.integrableOn_iff hF' (f := fun x => f (θ x)) hg).2 h1`. Rewrite using `[hF.setIntegral_eq hF' (f := fun x => f (θ x)) hg]`.

Conclude with `hmp.setIntegral_preimage_emb hemb f F`.
-/
theorem UpperTheory.Reformulated.B.Qh1.twist_general.{u_1} :
    ∀ {G : Type u_1} [inst : Group G]
    [inst_1 : TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G]
    [inst_5 : MeasurableSpace G] [BorelSpace G] (μ : MeasureTheory.Measure G) [μ.IsHaarMeasure] (Γ : Subgroup G)
    [Countable ↥Γ] {F : Set G},
    MeasureTheory.IsFundamentalDomain (↥Γ) F μ →
      ∀ (θ : G →* G),
        Continuous (⇑θ : G → G) →
          (∀ (x : G), (θ : G → G) ((θ : G → G) x) = x) →
            (∀ γ ∈ Γ, (θ : G → G) γ ∈ Γ) →
              ∀ (f : G → ℂ),
                (∀ (γ : ↥Γ) (x : G), f ((↑γ : G) * x) = f x) →
                  MeasureTheory.Integrable f (μ.restrict F) →
                    MeasureTheory.Integrable (fun (x : G) ↦ f ((θ : G → G) x)) (μ.restrict F) ∧
                      ∫ (x : G) in F, f ((θ : G → G) x) ∂μ = ∫ (x : G) in F, f x ∂μ := by
  intro G _ _ _ _ _ _ _ μ _ Γ _ F hF θ hθc hθθ hθΓ f hf hfi
  let φ : G ≃ₜ* G :=
    { toFun := θ
      invFun := θ
      left_inv := hθθ
      right_inv := hθθ
      map_mul' := map_mul θ
      continuous_toFun := hθc
      continuous_invFun := hθc }
  have hmp : MeasureTheory.MeasurePreserving θ μ μ :=
    ⟨hθc.measurable, UpperTheory.Reformulated.B.Qh1.map_involution_eq μ φ hθθ⟩
  have hemb : MeasurableEmbedding (θ : G → G) := φ.toHomeomorph.measurableEmbedding
  let e : Γ → Γ := fun γ => ⟨θ γ, hθΓ γ γ.2⟩
  have he : Function.Involutive e := fun γ => Subtype.ext (hθθ γ)
  have hF' : MeasureTheory.IsFundamentalDomain Γ (θ ⁻¹' F) μ := by
    refine hF.preimage_of_equiv hmp.quasiMeasurePreserving he.bijective ?_
    intro γ x
    change θ (θ γ * x) = γ * θ x
    rw [map_mul, hθθ]
  have hg : ∀ (γ : Γ) (x : G), f (θ (γ • x)) = f (θ x) := by
    intro γ x
    change f (θ (γ * x)) = f (θ x)
    rw [map_mul]
    exact hf (e γ) (θ x)
  refine ⟨?_, ?_⟩
  · have h1 : MeasureTheory.IntegrableOn (fun x => f (θ x)) (θ ⁻¹' F) μ :=
      (hmp.integrableOn_comp_preimage hemb).2 hfi
    exact (hF.integrableOn_iff hF' (f := fun x => f (θ x)) hg).2 h1
  · rw [hF.setIntegral_eq hF' (f := fun x => f (θ x)) hg]
    exact hmp.setIntegral_preimage_emb hemb f F
