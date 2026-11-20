import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogAbsEEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantTermUnipotentIntegralStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.CtTyp

set_option synthInstance.maxHeartbeats 400000 in

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B a a' G X om om' hT d₁ W₁ H' i₀ i₁ hA f _hfc hf μ 𝓕 hμ h𝓕 h1 γ hγ hn g`. Use `haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E`. Use `haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _`. Use `haveI : IsTopologicalGroup (UA σ G.W.J) := inferInstance`. Use `haveI : BorelSpace (UA σ G.W.J) := ⟨rfl⟩`.

Establish `hc` using `GlobalTheory.T.constant_term_unipotent_integral F E σ B a a' G X om om' hT d₁ W₁ H' i₀ i₁ hA f hf μ 𝓕 hμ h𝓕 h1`. Set `c : unip σ G.W H' ≃ₜ* unip σ G.W H'` to `{ toFun := fun u => ⟨γ⁻¹ * u.1 * γ, (hn u.1 u.2).2⟩ invFun := fun u => ⟨γ * u.1 * γ⁻¹, (hn u.1 u.2).1⟩ left_inv := fun u => by ext1; simp [mul_assoc] right_inv := fun u => by ext1; simp [mul_assoc] map_mul' := fun u v => by ext1; simp [mul_assoc] continuous_toFun := by`. Conclude with `((continuous_const.mul continuous_subtype_val).mul continuous_const).subtype_mk _`. Use `continuous_invFun := by`. Conclude with `((continuous_const.mul continuous_subtype_val).mul continuous_const).subtype_mk _ }`.

Establish `hcv : ∀ u, (c u).1 = γ⁻¹ * u.1 * γ` using `fun u => rfl`. Establish `hcs : ∀ u, (c.symm u).1 = γ * u.1 * γ⁻¹` using `fun u => rfl`. Set `e : unip σ G.W H' ≃ᵐ unip σ G.W H'` to `c.toHomeomorph.toMeasurableEquiv`. Establish `he : ∀ u, e u = c u` using `fun u => rfl`. Set `μ' : Measure (unip σ G.W H')` to `μ.map e`.

Use `haveI : μ'.IsHaarMeasure := ContinuousMulEquiv.isHaarMeasure_map μ c`. Set `𝓕' : Set (unip σ G.W H')` to `e.symm ⁻¹' 𝓕`. Establish `hpres : MeasurePreserving e.symm μ' μ`. Use `⟨e.symm.measurable, ?_⟩` and prove the remaining obligations. Simplify using `only [μ', Measure.map_map e.symm.measurable e.measurable, MeasurableEquiv.symm_comp_self, Measure.map_id]`.

Establish `hrat : ∀ δ ∈ (ratU σ G.W.J).subgroupOf (unip σ G.W H'), c δ ∈ (ratU σ G.W.J).subgroupOf (unip σ G.W H')`. Introduce `δ hδ`. Rewrite `hδ`, the goal using `[Subgroup.mem_subgroupOf]`. Rewrite using `[hcv]`. Conclude with `(Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hγ) hδ) hγ)`.

Establish `hrat' : ∀ δ ∈ (ratU σ G.W.J).subgroupOf (unip σ G.W H'), c.symm δ ∈ (ratU σ G.W.J).subgroupOf (unip σ G.W H')`. Introduce `δ hδ`. Rewrite `hδ`, the goal using `[Subgroup.mem_subgroupOf]`. Rewrite using `[hcs]`. Conclude with `(Subgroup.mul_mem _ (Subgroup.mul_mem _ hγ hδ) (Subgroup.inv_mem _ hγ))`.

Set `eΓ : (ratU σ G.W.J).subgroupOf (unip σ G.W H') → (ratU σ G.W.J).subgroupOf (unip σ G.W H')` to `fun δ => ⟨c δ.1, hrat δ.1 δ.2⟩`. Establish `heΓ : Function.Bijective eΓ`. Use `Function.bijective_iff_has_inverse.2 ⟨fun δ => ⟨c.symm δ.1, hrat' δ.1 δ.2⟩, ?_, ?_⟩` and prove the remaining obligations. Introduce `δ`. Use `ext1`.

Simplify using `[eΓ]`. Introduce `δ`. Use `ext1`. Simplify using `[eΓ]`. Establish `h𝓕' : IsFundamentalDomain ((ratU σ G.W.J).subgroupOf (unip σ G.W H')) 𝓕' μ'`.

Use `h𝓕.preimage_of_equiv hpres.quasiMeasurePreserving heΓ ?_` and prove the remaining obligations. Introduce `δ x`. Use `show e.symm (eΓ δ • x) = δ • e.symm x`. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `only [Subgroup.smul_def, smul_eq_mul]`.

Use `show (c.symm ((eΓ δ : unip σ G.W H') * x)).1 = ((δ : unip σ G.W H') * c.symm x).1`. Rewrite using `[hcs, Subgroup.coe_mul, Subgroup.coe_mul, hcs]`. Use `show γ * ((γ⁻¹ * (δ : unip σ G.W H').1 * γ) * x.1) * γ⁻¹ = (δ : unip σ G.W H').1 * (γ * x.1 * γ⁻¹)`. Use `group`. Establish `h1' : μ' 𝓕' = 1`.

Simplify using `only [μ', 𝓕', e.map_apply]`. Rewrite using `[← Set.preimage_comp, e.symm_comp_self, Set.preimage_id]`. Conclude with `h1`. Establish `A` using `hc μ' 𝓕' inferInstance h𝓕' h1' g`. Simplify using `only at A`.

Unfold `ctf`. Rewrite using `[A, e.measurableEmbedding.setIntegral_map]`. Establish `hpre : e ⁻¹' 𝓕' = 𝓕`. Simplify using `only [𝓕']`. Rewrite using `[← Set.preimage_comp, e.symm_comp_self, Set.preimage_id]`.

Rewrite using `[hpre]`. Use `congr 1`. Use function extensionality and compare the values at `u`. Rewrite using `[he, hcv]`. Use `hf γ⁻¹ (Subgroup.inv_mem _ hγ) (u.1 * (γ * g))` as an intermediate fact.

Rewrite using `[← this]`. Use `congr 1`. Use `group`.
-/
theorem ctf_rat_normaliser : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' → ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E (a + a') d₁) (i₀ i₁ : ℕ), H'.IsAdapted σ B G.W W₁ i₀ i₁ → ∀ f : UA σ G.W.J → ℂ, Continuous f → (∀ γ ∈ ratU σ G.W.J, ∀ h, f (γ * h) = f h) → ∀ (μ : Measure (unip σ G.W H')) (𝓕 : Set (unip σ G.W H')), μ.IsHaarMeasure → IsFundamentalDomain ((ratU σ G.W.J).subgroupOf (unip σ G.W H')) 𝓕 μ → μ 𝓕 = 1 → ∀ γ ∈ ratU σ G.W.J, (∀ u ∈ unip σ G.W H', γ * u * γ⁻¹ ∈ unip σ G.W H' ∧ γ⁻¹ * u * γ ∈ unip σ G.W H') → ∀ g, GlobalTheory.CtTyp.ctf H' μ 𝓕 f (γ * g) = GlobalTheory.CtTyp.ctf H' μ 𝓕 f g := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT d₁ W₁ H' i₀ i₁ hA f _hfc hf μ 𝓕 hμ h𝓕 h1 γ hγ hn g
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  haveI : IsTopologicalGroup (UA σ G.W.J) := inferInstance
  haveI : BorelSpace (UA σ G.W.J) := ⟨rfl⟩
  have hc := GlobalTheory.T.constant_term_unipotent_integral F E σ B a a' G X om om' hT d₁ W₁ H' i₀ i₁ hA f hf μ 𝓕 hμ h𝓕 h1
  let c : unip σ G.W H' ≃ₜ* unip σ G.W H' :=
    { toFun := fun u => ⟨γ⁻¹ * u.1 * γ, (hn u.1 u.2).2⟩
      invFun := fun u => ⟨γ * u.1 * γ⁻¹, (hn u.1 u.2).1⟩
      left_inv := fun u => by ext1; simp [mul_assoc]
      right_inv := fun u => by ext1; simp [mul_assoc]
      map_mul' := fun u v => by ext1; simp [mul_assoc]
      continuous_toFun := by
        exact ((continuous_const.mul continuous_subtype_val).mul continuous_const).subtype_mk _
      continuous_invFun := by
        exact ((continuous_const.mul continuous_subtype_val).mul continuous_const).subtype_mk _ }
  have hcv : ∀ u, (c u).1 = γ⁻¹ * u.1 * γ := fun u => rfl
  have hcs : ∀ u, (c.symm u).1 = γ * u.1 * γ⁻¹ := fun u => rfl
  let e : unip σ G.W H' ≃ᵐ unip σ G.W H' := c.toHomeomorph.toMeasurableEquiv
  have he : ∀ u, e u = c u := fun u => rfl
  let μ' : Measure (unip σ G.W H') := μ.map e
  haveI : μ'.IsHaarMeasure := ContinuousMulEquiv.isHaarMeasure_map μ c
  let 𝓕' : Set (unip σ G.W H') := e.symm ⁻¹' 𝓕
  have hpres : MeasurePreserving e.symm μ' μ := by
    refine ⟨e.symm.measurable, ?_⟩
    simp only [μ', Measure.map_map e.symm.measurable e.measurable, MeasurableEquiv.symm_comp_self, Measure.map_id]
  have hrat : ∀ δ ∈ (ratU σ G.W.J).subgroupOf (unip σ G.W H'), c δ ∈ (ratU σ G.W.J).subgroupOf (unip σ G.W H') := by
    intro δ hδ
    rw [Subgroup.mem_subgroupOf] at hδ ⊢
    rw [hcv]
    exact (Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hγ) hδ) hγ)
  have hrat' : ∀ δ ∈ (ratU σ G.W.J).subgroupOf (unip σ G.W H'), c.symm δ ∈ (ratU σ G.W.J).subgroupOf (unip σ G.W H') := by
    intro δ hδ
    rw [Subgroup.mem_subgroupOf] at hδ ⊢
    rw [hcs]
    exact (Subgroup.mul_mem _ (Subgroup.mul_mem _ hγ hδ) (Subgroup.inv_mem _ hγ))
  let eΓ : (ratU σ G.W.J).subgroupOf (unip σ G.W H') → (ratU σ G.W.J).subgroupOf (unip σ G.W H') :=
    fun δ => ⟨c δ.1, hrat δ.1 δ.2⟩
  have heΓ : Function.Bijective eΓ := by
    refine Function.bijective_iff_has_inverse.2 ⟨fun δ => ⟨c.symm δ.1, hrat' δ.1 δ.2⟩, ?_, ?_⟩
    · intro δ; ext1; simp [eΓ]
    · intro δ; ext1; simp [eΓ]
  have h𝓕' : IsFundamentalDomain ((ratU σ G.W.J).subgroupOf (unip σ G.W H')) 𝓕' μ' := by
    refine h𝓕.preimage_of_equiv hpres.quasiMeasurePreserving heΓ ?_
    intro δ x
    show e.symm (eΓ δ • x) = δ • e.symm x
    apply Subtype.ext
    simp only [Subgroup.smul_def, smul_eq_mul]
    show (c.symm ((eΓ δ : unip σ G.W H') * x)).1 = ((δ : unip σ G.W H') * c.symm x).1
    rw [hcs, Subgroup.coe_mul, Subgroup.coe_mul, hcs]
    show γ * ((γ⁻¹ * (δ : unip σ G.W H').1 * γ) * x.1) * γ⁻¹ = (δ : unip σ G.W H').1 * (γ * x.1 * γ⁻¹)
    group
  have h1' : μ' 𝓕' = 1 := by
    simp only [μ', 𝓕', e.map_apply]
    rw [← Set.preimage_comp, e.symm_comp_self, Set.preimage_id]; exact h1
  have A := hc μ' 𝓕' inferInstance h𝓕' h1' g
  simp only at A
  unfold ctf
  rw [A, e.measurableEmbedding.setIntegral_map]
  have hpre : e ⁻¹' 𝓕' = 𝓕 := by
    simp only [𝓕']; rw [← Set.preimage_comp, e.symm_comp_self, Set.preimage_id]
  rw [hpre]
  congr 1; funext u
  rw [he, hcv]
  have := hf γ⁻¹ (Subgroup.inv_mem _ hγ) (u.1 * (γ * g))
  rw [← this]
  congr 1
  group

end GlobalTheory.CtTyp
