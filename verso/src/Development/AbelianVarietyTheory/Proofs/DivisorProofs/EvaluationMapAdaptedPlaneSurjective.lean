import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvaluationMapAdaptedPlaneEquivariantStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdmittedFormEqAdelicThetaDistribution
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecondConfigurationTripleCompatible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzMapBarrelledSpace

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

open scoped Classical

namespace GlobalTheory.ThKExpandAdm

/- English proof (translation)
Introduce `hKP F E _ _ _ _ _ σ B n d d₁ X W W₁ M M₁ H' i₀ i₁ hH hM₁ e₀ hev hB hM hXW g hg`. Establish `hψ : IsStd B.ψ` using `hB.std`. Take `⟨l₀, hl₀, hl₀eq⟩` from `GlobalTheory.ThetaAdmitted.exists_admitted_form_eq_adelicThetaDistribution_alt F (Fin n × Fin d₁)`. Establish `hl₁` using `GlobalTheory.ConeMeasV.comp_ev_mem_adm hM hM₁ hev hl₀`. Establish `hterm : ∀ ξ : Fin n → E, ∃ T : SInf F (Fin n × Fin d) →L[ℂ] ℂ, ∀ f : SInf F (Fin n × Fin d), thetaSum F (e₀ (M.co.rho B.ψ (Matrix.vecMulVec (incV F ξ) (incV F H'.y)) (pureA F f g))) = T f`.

Introduce `ξ`. Take `⟨T, hT⟩` from `GlobalTheory.ConeMeasV.comp_schr_mem_adm hψ (M.co.e (Matrix.vecMulVec (incV F ξ) (incV F H'.y))) hl₁ g hg`. Use `⟨T, fun f => ?_⟩` and prove the remaining obligations. Establish `hA : pureA F (f : (Fin n × Fin d → mixedEmbedding.mixedSpace F) → ℂ) g ∈ schA F (Fin n × Fin d)` using `Submodule.subset_span ⟨f, g, hg, rfl⟩`. Establish `h1` using `GlobalTheory.ConeMeasV.schr_mem_schA hψ (M.co.e (Matrix.vecMulVec (incV F ξ) (incV F H'.y))) hA`.

Establish `h2` using `hev.maps _ h1`. Rewrite using `[← hT f]`. Conclude with `(hl₀eq _ h2).symm`. Use `choose T hT using hterm`. Establish `hsum : ∀ f : SInf F (Fin n × Fin d), Summable fun ξ : Fin n → E => T ξ f`.

Introduce `f`. Establish `hA : pureA F (f : (Fin n × Fin d → mixedEmbedding.mixedSpace F) → ℂ) g ∈ schA F (Fin n × Fin d)` using `Submodule.subset_span ⟨f, g, hg, rfl⟩`. Use `GlobalTheory.T.evaluation_map_adapted_plane_equivariant hKP F E σ B n d d₁ X W W₁ M M₁ H' i₀ i₁ hH hM₁ e₀ hev hB hM hXW _ hA` as an intermediate fact. Simplify `this` using `only [hT]`. Use `haveI : Countable E := (Module.finBasis ℚ E).equivFun.injective.countable`.

Take `⟨en, hen⟩` from `exists_surjective_nat (Fin n → E)`. Set `S : ℕ → Finset (Fin n → E)` to `fun N => (Finset.range N).image en`. Establish `hS : Tendsto S atTop atTop`. Use `Filter.tendsto_atTop_finset_of_monotone (fun a b hab => ?_) (fun ξ => ?_)` and prove the remaining obligations. Conclude with `Finset.image_subset_image (Finset.range_subset_range.2 hab)`.

Take `⟨k, rfl⟩` from `hen ξ`. Conclude with `⟨k + 1, Finset.mem_image_of_mem _ (Finset.mem_range.2 (Nat.lt_succ_self k))⟩`. Use `haveI : BarrelledSpace ℂ (SInf F (Fin n × Fin d)) := GlobalTheory.schwartzMap_barrelledSpace _`. Establish `hlim : Tendsto (fun N f => (∑ ξ ∈ S N, T ξ) f) atTop (𝓝 fun f : SInf F (Fin n × Fin d) => ∑' ξ, T ξ f)`. Rewrite using `[tendsto_pi_nhds]`.

Introduce `f`. Simplify using `only [ContinuousLinearMap.sum_apply]`. Conclude with `(hsum f).hasSum.comp hS`. Use `⟨continuousLinearMapOfTendsto (fun N => ∑ ξ ∈ S N, T ξ) hlim, fun f => ?_⟩` and prove the remaining obligations. Use `show _ = linearMapOfTendsto _ _ hlim f`.

Rewrite using `[linearMapOfTendsto_apply]`. Simplify using `only [hT]`.
-/
theorem adm : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d d₁ : ℕ) (X : Spc F E n) (W : Spc F E d) (W₁ : Spc F E d₁) (M : Model σ X W) (M₁ : Model σ X W₁) (H' : Plane E d d₁) (i₀ i₁ : ℕ),
    H'.IsAdapted σ B W W₁ i₀ i₁ → M₁.IsGood B.ψ → ∀ (e₀ : Fn F n d →ₗ[ℂ] Fn F n d₁), IsEv B M M₁ 1 H'.ι (iso0 n H') e₀ → B.IsGood σ → M.IsGood B.ψ → (∃ r s r' s' : ℕ, X.IsHerm σ B r s ∧ W.IsSkew σ B r' s') →
    ∀ g ∈ SB (Fin n × Fin d → FiniteAdeleRing (𝓞 F) F), ∃ T : SInf F (Fin n × Fin d) →L[ℂ] ℂ,
      ∀ f : SInf F (Fin n × Fin d), (∑' ξ : Fin n → E, thetaSum F (e₀ (M.co.rho B.ψ (Matrix.vecMulVec (incV F ξ) (incV F H'.y)) (pureA F f g)))) = T f := by
  intro hKP F E _ _ _ _ _ σ B n d d₁ X W W₁ M M₁ H' i₀ i₁ hH hM₁ e₀ hev hB hM hXW g hg
  have hψ : IsStd B.ψ := hB.std
  obtain ⟨l₀, hl₀, hl₀eq⟩ := GlobalTheory.ThetaAdmitted.exists_admitted_form_eq_adelicThetaDistribution_alt F (Fin n × Fin d₁)
  have hl₁ := GlobalTheory.ConeMeasV.comp_ev_mem_adm hM hM₁ hev hl₀
  have hterm : ∀ ξ : Fin n → E, ∃ T : SInf F (Fin n × Fin d) →L[ℂ] ℂ, ∀ f : SInf F (Fin n × Fin d),
      thetaSum F (e₀ (M.co.rho B.ψ (Matrix.vecMulVec (incV F ξ) (incV F H'.y)) (pureA F f g))) = T f := by
    intro ξ
    obtain ⟨T, hT⟩ := GlobalTheory.ConeMeasV.comp_schr_mem_adm hψ (M.co.e (Matrix.vecMulVec (incV F ξ) (incV F H'.y))) hl₁ g hg
    refine ⟨T, fun f => ?_⟩
    have hA : pureA F (f : (Fin n × Fin d → mixedEmbedding.mixedSpace F) → ℂ) g ∈ schA F (Fin n × Fin d) :=
      Submodule.subset_span ⟨f, g, hg, rfl⟩
    have h1 := GlobalTheory.ConeMeasV.schr_mem_schA hψ (M.co.e (Matrix.vecMulVec (incV F ξ) (incV F H'.y))) hA
    have h2 := hev.maps _ h1
    rw [← hT f]
    exact (hl₀eq _ h2).symm
  choose T hT using hterm
  have hsum : ∀ f : SInf F (Fin n × Fin d), Summable fun ξ : Fin n → E => T ξ f := by
    intro f
    have hA : pureA F (f : (Fin n × Fin d → mixedEmbedding.mixedSpace F) → ℂ) g ∈ schA F (Fin n × Fin d) :=
      Submodule.subset_span ⟨f, g, hg, rfl⟩
    have := GlobalTheory.T.evaluation_map_adapted_plane_equivariant hKP F E σ B n d d₁ X W W₁ M M₁ H' i₀ i₁ hH hM₁ e₀ hev hB hM hXW _ hA
    simpa only [hT] using this
  haveI : Countable E := (Module.finBasis ℚ E).equivFun.injective.countable
  obtain ⟨en, hen⟩ := exists_surjective_nat (Fin n → E)
  let S : ℕ → Finset (Fin n → E) := fun N => (Finset.range N).image en
  have hS : Tendsto S atTop atTop := by
    refine Filter.tendsto_atTop_finset_of_monotone (fun a b hab => ?_) (fun ξ => ?_)
    · exact Finset.image_subset_image (Finset.range_subset_range.2 hab)
    · obtain ⟨k, rfl⟩ := hen ξ
      exact ⟨k + 1, Finset.mem_image_of_mem _ (Finset.mem_range.2 (Nat.lt_succ_self k))⟩
  haveI : BarrelledSpace ℂ (SInf F (Fin n × Fin d)) := GlobalTheory.schwartzMap_barrelledSpace _
  have hlim : Tendsto (fun N f => (∑ ξ ∈ S N, T ξ) f) atTop
      (𝓝 fun f : SInf F (Fin n × Fin d) => ∑' ξ, T ξ f) := by
    rw [tendsto_pi_nhds]
    intro f
    simp only [ContinuousLinearMap.sum_apply]
    exact (hsum f).hasSum.comp hS
  refine ⟨continuousLinearMapOfTendsto (fun N => ∑ ξ ∈ S N, T ξ) hlim, fun f => ?_⟩
  show _ = linearMapOfTendsto _ _ hlim f
  rw [linearMapOfTendsto_apply]
  simp only [hT]

end GlobalTheory.ThKExpandAdm
