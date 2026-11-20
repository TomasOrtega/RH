import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdmittedFormEqAdelicThetaDistribution
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecondConfigurationTripleCompatible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzMapBarrelledSpace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperbolicPlanePairDecompositionStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

open scoped Classical

namespace GlobalTheory.ThKExpandYAdm

/- English proof (translation)
Introduce `hKP F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP d₂ H hH V₁ M₁ e hV hM₁ hev g hg`. Establish `hψ : IsStd B.ψ` using `hP.base.std`. Establish `hSumm : ∀ Ψ ∈ schA F (Fin n × Fin d), Summable (fun w : Fin d → E => thetaSum F (e (M.co.rho B.ψ (Matrix.vecMulVec (incV F H.y) (incV F w)) Ψ)))` using `GlobalTheory.T.hyperbolic_plane_pair_decomposition hKP F E σ B n d X W M χX χW om r s r' s' hP d₂ H hH V₁ M₁ e hV hM₁ hev`. Take `⟨l₀, hl₀, hl₀eq⟩` from `GlobalTheory.ThetaAdmitted.exists_admitted_form_eq_adelicThetaDistribution_alt F (Fin d₂ × Fin d)`. Establish `hl₁` using `GlobalTheory.ConeMeasV.comp_ev_mem_adm hP.good hM₁ hev hl₀`.

Establish `hterm : ∀ w : Fin d → E, ∃ T : SInf F (Fin n × Fin d) →L[ℂ] ℂ, ∀ f : SInf F (Fin n × Fin d), thetaSum F (e (M.co.rho B.ψ (Matrix.vecMulVec (incV F H.y) (incV F w)) (pureA F f g))) = T f`. Introduce `w`. Take `⟨T, hT⟩` from `GlobalTheory.ConeMeasV.comp_schr_mem_adm hψ (M.co.e (Matrix.vecMulVec (incV F H.y) (incV F w))) hl₁ g hg`. Use `⟨T, fun f => ?_⟩` and prove the remaining obligations. Establish `hA : pureA F (f : (Fin n × Fin d → mixedEmbedding.mixedSpace F) → ℂ) g ∈ schA F (Fin n × Fin d)` using `Submodule.subset_span ⟨f, g, hg, rfl⟩`.

Establish `h1` using `GlobalTheory.ConeMeasV.schr_mem_schA hψ (M.co.e (Matrix.vecMulVec (incV F H.y) (incV F w))) hA`. Establish `h2` using `hev.maps _ h1`. Rewrite using `[← hT f]`. Conclude with `(hl₀eq _ h2).symm`. Use `choose T hT using hterm`.

Establish `hsum : ∀ f : SInf F (Fin n × Fin d), Summable fun w : Fin d → E => T w f`. Introduce `f`. Establish `hA : pureA F (f : (Fin n × Fin d → mixedEmbedding.mixedSpace F) → ℂ) g ∈ schA F (Fin n × Fin d)` using `Submodule.subset_span ⟨f, g, hg, rfl⟩`. Use `hSumm _ hA` as an intermediate fact. Simplify `this` using `only [hT]`.

Use `haveI : Countable E := (Module.finBasis ℚ E).equivFun.injective.countable`. Take `⟨en, hen⟩` from `exists_surjective_nat (Fin d → E)`. Set `S : ℕ → Finset (Fin d → E)` to `fun N => (Finset.range N).image en`. Establish `hS : Tendsto S atTop atTop`. Use `Filter.tendsto_atTop_finset_of_monotone (fun a b hab => ?_) (fun w => ?_)` and prove the remaining obligations.

Conclude with `Finset.image_subset_image (Finset.range_subset_range.2 hab)`. Take `⟨k, rfl⟩` from `hen w`. Conclude with `⟨k + 1, Finset.mem_image_of_mem _ (Finset.mem_range.2 (Nat.lt_succ_self k))⟩`. Use `haveI : BarrelledSpace ℂ (SInf F (Fin n × Fin d)) := GlobalTheory.schwartzMap_barrelledSpace _`. Establish `hlim : Tendsto (fun N f => (∑ w ∈ S N, T w) f) atTop (𝓝 fun f : SInf F (Fin n × Fin d) => ∑' w, T w f)`.

Rewrite using `[tendsto_pi_nhds]`. Introduce `f`. Simplify using `only [ContinuousLinearMap.sum_apply]`. Conclude with `(hsum f).hasSum.comp hS`. Use `⟨continuousLinearMapOfTendsto (fun N => ∑ w ∈ S N, T w) hlim, fun f => ?_⟩` and prove the remaining obligations.

Use `show _ = linearMapOfTendsto _ _ hlim f`. Rewrite using `[linearMapOfTendsto_apply]`. Simplify using `only [hT]`.
-/
theorem adm : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    IsPair B M χX χW om r s r' s' →
    ∀ (d₂ : ℕ) (H : Plane E n d₂), (d₂ + 2 = n ∧ form σ X.J H.x H.x = 0 ∧ form σ X.J H.y H.y = 0 ∧ form σ X.J H.x H.y = 1 ∧
        (∀ u, form σ X.J (H.ι *ᵥ u) H.x = 0 ∧ form σ X.J (H.ι *ᵥ u) H.y = 0) ∧ Function.Injective H.ι.mulVec) →
    ∀ (V₁ : Spc F E d₂) (M₁ : Model σ V₁ W) (e : Fn F n d →ₗ[ℂ] Fn F d₂ d),
      V₁.J = H.ιᵀ * X.J * H.ι.map σ → M₁.IsGood B.ψ → IsEv B M M₁ H.ι 1 {u | ∃ z, u = Matrix.vecMulVec (incV F H.x) z} e →
    ∀ g ∈ SB (Fin n × Fin d → FiniteAdeleRing (𝓞 F) F), ∃ T : SInf F (Fin n × Fin d) →L[ℂ] ℂ,
      ∀ f : SInf F (Fin n × Fin d), (∑' w : Fin d → E, thetaSum F (e (M.co.rho B.ψ (Matrix.vecMulVec (incV F H.y) (incV F w)) (pureA F f g)))) = T f := by
  intro hKP F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP d₂ H hH V₁ M₁ e hV hM₁ hev g hg
  have hψ : IsStd B.ψ := hP.base.std
  have hSumm : ∀ Ψ ∈ schA F (Fin n × Fin d),
      Summable (fun w : Fin d → E => thetaSum F (e (M.co.rho B.ψ (Matrix.vecMulVec (incV F H.y) (incV F w)) Ψ))) :=
    GlobalTheory.T.hyperbolic_plane_pair_decomposition hKP F E σ B n d X W M χX χW om r s r' s' hP d₂ H hH V₁ M₁ e hV hM₁ hev
  obtain ⟨l₀, hl₀, hl₀eq⟩ := GlobalTheory.ThetaAdmitted.exists_admitted_form_eq_adelicThetaDistribution_alt F (Fin d₂ × Fin d)
  have hl₁ := GlobalTheory.ConeMeasV.comp_ev_mem_adm hP.good hM₁ hev hl₀
  have hterm : ∀ w : Fin d → E, ∃ T : SInf F (Fin n × Fin d) →L[ℂ] ℂ, ∀ f : SInf F (Fin n × Fin d),
      thetaSum F (e (M.co.rho B.ψ (Matrix.vecMulVec (incV F H.y) (incV F w)) (pureA F f g))) = T f := by
    intro w
    obtain ⟨T, hT⟩ := GlobalTheory.ConeMeasV.comp_schr_mem_adm hψ (M.co.e (Matrix.vecMulVec (incV F H.y) (incV F w))) hl₁ g hg
    refine ⟨T, fun f => ?_⟩
    have hA : pureA F (f : (Fin n × Fin d → mixedEmbedding.mixedSpace F) → ℂ) g ∈ schA F (Fin n × Fin d) :=
      Submodule.subset_span ⟨f, g, hg, rfl⟩
    have h1 := GlobalTheory.ConeMeasV.schr_mem_schA hψ (M.co.e (Matrix.vecMulVec (incV F H.y) (incV F w))) hA
    have h2 := hev.maps _ h1
    rw [← hT f]
    exact (hl₀eq _ h2).symm
  choose T hT using hterm
  have hsum : ∀ f : SInf F (Fin n × Fin d), Summable fun w : Fin d → E => T w f := by
    intro f
    have hA : pureA F (f : (Fin n × Fin d → mixedEmbedding.mixedSpace F) → ℂ) g ∈ schA F (Fin n × Fin d) :=
      Submodule.subset_span ⟨f, g, hg, rfl⟩
    have := hSumm _ hA
    simpa only [hT] using this
  haveI : Countable E := (Module.finBasis ℚ E).equivFun.injective.countable
  obtain ⟨en, hen⟩ := exists_surjective_nat (Fin d → E)
  let S : ℕ → Finset (Fin d → E) := fun N => (Finset.range N).image en
  have hS : Tendsto S atTop atTop := by
    refine Filter.tendsto_atTop_finset_of_monotone (fun a b hab => ?_) (fun w => ?_)
    · exact Finset.image_subset_image (Finset.range_subset_range.2 hab)
    · obtain ⟨k, rfl⟩ := hen w
      exact ⟨k + 1, Finset.mem_image_of_mem _ (Finset.mem_range.2 (Nat.lt_succ_self k))⟩
  haveI : BarrelledSpace ℂ (SInf F (Fin n × Fin d)) := GlobalTheory.schwartzMap_barrelledSpace _
  have hlim : Tendsto (fun N f => (∑ w ∈ S N, T w) f) atTop
      (𝓝 fun f : SInf F (Fin n × Fin d) => ∑' w, T w f) := by
    rw [tendsto_pi_nhds]
    intro f
    simp only [ContinuousLinearMap.sum_apply]
    exact (hsum f).hasSum.comp hS
  refine ⟨continuousLinearMapOfTendsto (fun N => ∑ w ∈ S N, T w) hlim, fun f => ?_⟩
  show _ = linearMapOfTendsto _ _ hlim f
  rw [linearMapOfTendsto_apply]
  simp only [hT]

end GlobalTheory.ThKExpandYAdm
