import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIntertwinerGoodModelsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewAdaptedPlanePairVanishStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewAdaptedPlanePairFactorStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.MixWLeft

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP d₁ W₁ H' i₀ i₁ M₁ om₁ r₁ s₁ hA hP₁ e he g`. Establish `hs` using `IsUWeilPair.isUSplitting hP.weil`. Establish `hs₁` using `IsUWeilPair.isUSplitting hP₁.weil`. Establish `h1 : incM F (1 : Matrix (Fin n) (Fin n) E) = 1`. Simplify using `[incM]`.

Use `⟨fun Φ hΦ => ?_, fun z Φ hΦ => ?_, fun u hu Φ hΦ => ?_⟩` and prove the remaining obligations. Conclude with `hs₁.pres _ _ (he.maps _ (hs.pres _ _ hΦ))`. Simplify using `only [LinearMap.comp_apply]`. Rewrite using `[hs.impl (g, 1) _ Φ hΦ]`. Establish `key : actAB (cA σ) ((g, 1) : UA σ X.J × UA σ W.J) (incM F (1 : Matrix (Fin n) (Fin n) E) * z * (incM F H'.ι)ᵀ) = incM F (1 : Matrix (Fin n) (Fin n) E) * (mat g * z) * (incM F H'.ι)ᵀ`.

Simplify using `[actAB, mat, h1, Matrix.mul_assoc]`. Rewrite using `[key, he.Heisenberg₂ _ _ (hs.pres _ _ hΦ), hs₁.impl (g⁻¹, 1) _ _ (he.maps _ (hs.pres _ _ hΦ))]`. Use `congr 2`. Simplify using `[actAB, mat, ← Matrix.mul_assoc]`. Take `⟨y, rfl⟩` from `hu`.

Simplify using `only [LinearMap.comp_apply]`. Rewrite using `[hs.impl (g, 1) _ Φ hΦ]`. Establish `key : actAB (cA σ) ((g, 1) : UA σ X.J × UA σ W.J) (Matrix.vecMulVec y (incV F H'.x)) = Matrix.vecMulVec (mat g *ᵥ y) (incV F H'.x)`. Simplify using `[actAB, mat, Matrix.mul_vecMulVec]`. Rewrite using `[key, he.inv _ ⟨_, rfl⟩ _ (hs.pres _ _ hΦ)]`.
-/
theorem twist_left : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ : ℕ) (M₁ : Model σ X W₁) (om₁ : Rep σ X W₁) (r₁ s₁ : ℕ),
      H'.IsAdapted σ B W W₁ i₀ i₁ → IsPair B M₁ χX χW om₁ r s r₁ s₁ → ∀ e, IsEv B M M₁ 1 H'.ι (iso0 n H') e →
      ∀ g : UA σ X.J,
        (∀ Φ ∈ schA F (Fin n × Fin d), (om₁ (g⁻¹, 1) ∘ₗ e ∘ₗ om (g, 1)) Φ ∈ schA F (Fin n × Fin d₁)) ∧
        (∀ z : Matrix (Fin n) (Fin d₁) (AE F E), ∀ Φ ∈ schA F (Fin n × Fin d), (om₁ (g⁻¹, 1) ∘ₗ e ∘ₗ om (g, 1)) (M.co.rho B.ψ (incM F (1 : Matrix (Fin n) (Fin n) E) * z * (incM F H'.ι)ᵀ) Φ) =
          M₁.co.rho B.ψ z ((om₁ (g⁻¹, 1) ∘ₗ e ∘ₗ om (g, 1)) Φ)) ∧
        (∀ u ∈ iso0 n H', ∀ Φ ∈ schA F (Fin n × Fin d), (om₁ (g⁻¹, 1) ∘ₗ e ∘ₗ om (g, 1)) (M.co.rho B.ψ u Φ) =
          (om₁ (g⁻¹, 1) ∘ₗ e ∘ₗ om (g, 1)) Φ) := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP d₁ W₁ H' i₀ i₁ M₁ om₁ r₁ s₁ hA hP₁ e he g
  have hs := IsUWeilPair.isUSplitting hP.weil
  have hs₁ := IsUWeilPair.isUSplitting hP₁.weil
  have h1 : incM F (1 : Matrix (Fin n) (Fin n) E) = 1 := by
    simp [incM]
  refine ⟨fun Φ hΦ => ?_, fun z Φ hΦ => ?_, fun u hu Φ hΦ => ?_⟩
  · exact hs₁.pres _ _ (he.maps _ (hs.pres _ _ hΦ))
  · simp only [LinearMap.comp_apply]
    rw [hs.impl (g, 1) _ Φ hΦ]
    have key : actAB (cA σ) ((g, 1) : UA σ X.J × UA σ W.J) (incM F (1 : Matrix (Fin n) (Fin n) E) * z * (incM F H'.ι)ᵀ) =
        incM F (1 : Matrix (Fin n) (Fin n) E) * (mat g * z) * (incM F H'.ι)ᵀ := by
      simp [actAB, mat, h1, Matrix.mul_assoc]
    rw [key, he.Heisenberg₂ _ _ (hs.pres _ _ hΦ), hs₁.impl (g⁻¹, 1) _ _ (he.maps _ (hs.pres _ _ hΦ))]
    congr 2
    simp [actAB, mat, ← Matrix.mul_assoc]
  · obtain ⟨y, rfl⟩ := hu
    simp only [LinearMap.comp_apply]
    rw [hs.impl (g, 1) _ Φ hΦ]
    have key : actAB (cA σ) ((g, 1) : UA σ X.J × UA σ W.J) (Matrix.vecMulVec y (incV F H'.x)) =
        Matrix.vecMulVec (mat g *ᵥ y) (incV F H'.x) := by
      simp [actAB, mat, Matrix.mul_vecMulVec]
    rw [key, he.inv _ ⟨_, rfl⟩ _ (hs.pres _ _ hΦ)]

/- English proof (translation)
Introduce `hPr F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP d₁ W₁ H' i₀ i₁ M₁ om₁ r₁ s₁ hA hP₁ e he`. Use `GlobalTheory.T.skew_adapted_plane_pair_factor hPr F E σ B n d X W M χX χW om r s r' s' hP d₁ W₁ H' i₀ i₁ M₁ om₁ r₁ s₁ hA hP₁ e he ?_` and prove the remaining obligations. Introduce `g`. Take `⟨hmaps, hheis, hinv⟩` from `twist_left F E σ B n d X W M χX χW om r s r' s' hP d₁ W₁ H' i₀ i₁ M₁ om₁ r₁ s₁ hA hP₁ e he g`. Establish `hspl` using `IsUWeilPair.isUSplitting hP.weil`.

Establish `hspl₁` using `IsUWeilPair.isUSplitting hP₁.weil`. Establish `hadm : ∀ l ∈ (adeleClass F).adm (Fin n × Fin d₁), l ∘ₗ (om₁ (g⁻¹, 1) ∘ₗ e ∘ₗ om (g, 1)) ∈ (adeleClass F).adm (Fin n × Fin d)`. Introduce `l hl`. Establish `h1` using `hspl₁.adm (g⁻¹, 1) l hl`. Establish `h2` using `GlobalTheory.T.eigen_intertwiner_good_models F E σ B n d n d₁ X W X W₁ M M₁ 1 H'.ι (iso0 n H') e hP.good hP₁.good he _ h1`.

Establish `h3` using `hspl.adm (g, 1) _ h2`. Simplify `h3` using `[LinearMap.comp_assoc]`. Take `⟨c, hc⟩` from `GlobalTheory.T.skew_adapted_plane_pair_vanish hPr F E σ B n d X W M χX χW om r s r' s' hP d₁ W₁ H' i₀ i₁ M₁ om₁ r₁ s₁ hA hP₁ e he _ hmaps hheis hinv hadm`. Use `⟨c, fun Φ hΦ => ?_⟩` and prove the remaining obligations. Establish `key` using `hc Φ hΦ`.

Establish `hinv1 : ∀ Ψ, om₁ (g, 1) (om₁ (g⁻¹, 1) Ψ) = Ψ`. Introduce `Ψ`. Rewrite using `[← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one, mul_inv_cancel, Prod.mk_one_one, map_one, Module.End.one_apply]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem evalZero_unitary_left : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ : ℕ) (M₁ : Model σ X W₁) (om₁ : Rep σ X W₁) (r₁ s₁ : ℕ),
      H'.IsAdapted σ B W W₁ i₀ i₁ → IsPair B M₁ χX χW om₁ r s r₁ s₁ → ∀ e, IsEv B M M₁ 1 H'.ι (iso0 n H') e →
      ∀ g, ∀ Φ ∈ schA F (Fin n × Fin d), e (om (g, 1) Φ) = om₁ (g, 1) (e Φ) := by
  intro hPr F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP d₁ W₁ H' i₀ i₁ M₁ om₁ r₁ s₁ hA hP₁ e he
  refine GlobalTheory.T.skew_adapted_plane_pair_factor hPr F E σ B n d X W M χX χW om r s r' s' hP d₁ W₁ H' i₀ i₁ M₁ om₁ r₁ s₁ hA hP₁ e he ?_
  intro g
  obtain ⟨hmaps, hheis, hinv⟩ := twist_left F E σ B n d X W M χX χW om r s r' s' hP d₁ W₁ H' i₀ i₁ M₁ om₁ r₁ s₁ hA hP₁ e he g
  have hspl := IsUWeilPair.isUSplitting hP.weil
  have hspl₁ := IsUWeilPair.isUSplitting hP₁.weil
  have hadm : ∀ l ∈ (adeleClass F).adm (Fin n × Fin d₁),
      l ∘ₗ (om₁ (g⁻¹, 1) ∘ₗ e ∘ₗ om (g, 1)) ∈ (adeleClass F).adm (Fin n × Fin d) := by
    intro l hl
    have h1 := hspl₁.adm (g⁻¹, 1) l hl
    have h2 := GlobalTheory.T.eigen_intertwiner_good_models F E σ B n d n d₁ X W X W₁ M M₁ 1 H'.ι (iso0 n H') e hP.good hP₁.good he _ h1
    have h3 := hspl.adm (g, 1) _ h2
    simpa [LinearMap.comp_assoc] using h3
  obtain ⟨c, hc⟩ := GlobalTheory.T.skew_adapted_plane_pair_vanish hPr F E σ B n d X W M χX χW om r s r' s' hP d₁ W₁ H' i₀ i₁ M₁ om₁ r₁ s₁ hA hP₁ e he _ hmaps hheis hinv hadm
  refine ⟨c, fun Φ hΦ => ?_⟩
  have key := hc Φ hΦ
  have hinv1 : ∀ Ψ, om₁ (g, 1) (om₁ (g⁻¹, 1) Ψ) = Ψ := by
    intro Ψ
    rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one, mul_inv_cancel, Prod.mk_one_one, map_one,
      Module.End.one_apply]
  calc e (om (g, 1) Φ) = om₁ (g, 1) (om₁ (g⁻¹, 1) (e (om (g, 1) Φ))) := (hinv1 _).symm
    _ = om₁ (g, 1) ((om₁ (g⁻¹, 1) ∘ₗ e ∘ₗ om (g, 1)) Φ) := rfl
    _ = c • om₁ (g, 1) (e Φ) := by rw [key, map_smul]

end GlobalTheory.MixWLeft

end
