import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaAbsoluteSum
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InfPartEqZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.T2SpaceHalfAdelicMatrixAddSubgroup
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
open scoped GlobalTheory.HalfAverage

noncomputable section

namespace GlobalTheory.HalfLinForm

set_option synthInstance.maxHeartbeats 200000 in
set_option maxHeartbeats 1000000 in

/- English proof (translation)
Introduce `D ψ hψ S S₀ T ρ d μ 𝓕 hμ e he ℓ₀ H hH _ _ ν _`. Use `haveI : IsTopologicalAddGroup (Mx D T.rank ρ) := GlobalTheory.HalfAverage.tagMx _ _`. Use `haveI : T2Space (Mx D T.rank ρ) := GlobalTheory.HalfAverage.t2Mx _ _`. Use `haveI : T2Space H := inferInstance`. Use `haveI : R1Space H := T2Space.r1Space`.

Apply the tactic sequence `haveI : ContinuousSub (Mx D T.rank ρ) := by first | exact IsTopologicalAddGroup.to_continuousSub | exact inferInstance`. Establish `hHc : IsClosed (H : Set (Mx D T.rank ρ))`. Establish `: (H : Set (Mx D T.rank ρ)) = ⋂ i, ⋂ j, {t : Mx D T.rank ρ | cA D e * t i j = t i j}`. Use extensionality with `t`. Simplify using `only [SetLike.mem_coe, hH, Set.mem_iInter, Set.mem_setOf_eq]`.

Rewrite using `[this]`. Conclude with `isClosed_iInter fun i => isClosed_iInter fun j => isClosed_eq (continuous_const.mul ((continuous_apply j).comp (continuous_apply i))) ((continuous_apply j).comp (continuous_apply i))`. Establish `hint : ∀ f, IsThetaFunO ψ S T f → Integrable (fun x : H => ℓ₀ (d.mixS T ψ μ 𝓕 f x.1)) ν`. Introduce `f hf`. Take `⟨⟨U, hUo, hU⟩, K, hK, hKs⟩` from `GlobalTheory.MixHalf.mixS_half D ψ hψ S S₀ T ρ d μ 𝓕 hμ e he f hf`.

Establish `hKc : IsCompact ((Subtype.val : H → Mx D T.rank ρ) ⁻¹' K)` using `hHc.isClosedEmbedding_subtypeVal.isCompact_preimage hK`. Use `Continuous.integrable_of_hasCompactSupport ?_ (HasCompactSupport.intro hKc fun t ht => ?_)` and prove the remaining obligations. Use `IsLocallyConstant.continuous ?_` and prove the remaining obligations. Rewrite using `[IsLocallyConstant.iff_eventually_eq]`. Introduce `t`.

Establish `hn : {s : H | (s : Mx D T.rank ρ) - t ∈ U} ∈ nhds t`. Use `IsOpen.mem_nhds (hUo.preimage (continuous_subtype_val.sub continuous_const)) ?_` and prove the remaining obligations. Use `show (t : Mx D T.rank ρ) - t ∈ U`. Rewrite using `[sub_self]`. Conclude with `U.zero_mem`.

Use `filter_upwards [hn] with s hs`. Establish `hsH : ∀ i j, cA D e * ((s : Mx D T.rank ρ) - t) i j = ((s : Mx D T.rank ρ) - t) i j` using `(hH _).1 (H.sub_mem s.2 t.2)`. Establish `h1` using `hU _ hs hsH t`. Rewrite `h1` using `[show (t : Mx D T.rank ρ) + ((s : Mx D T.rank ρ) - t) = s by abel]`. Rewrite using `[h1]`.

Assume the negation of the conclusion as `hne`. Conclude with `ht (hKs _ ((hH _).1 t.2) fun h0 => hne (by rw [h0, map_zero]))`. Establish `madd : ∀ f g : WO S T → ℂ, (∀ x w, IntegrableOn (fun a => heisO ψ S T (d.extY T a) (heisO ψ S T (d.extX T x) (heisO ψ S T (d.ext0 T w) f)) 0) 𝓕 μ) → (∀ x w, IntegrableOn (fun a => heisO ψ S T (d.extY T a) (heisO ψ S T (d.extX T x) (heisO ψ S T (d.ext0 T w) g)) 0) 𝓕 μ) → ∀ x, d.mi …`. Introduce `f g hf hg x`. Use function extensionality and compare the values at `w`.

Establish `h1` using `hf x w`. Establish `h2` using `hg x w`. Simplify using `only [HypDec.mixS, HypDec.integrandS_eq, Pi.add_apply, mul_add] at h1 h2 ⊢`. Conclude with `integral_add h1 h2`. Establish `msmul : ∀ (c : ℂ) (f : WO S T → ℂ) x, d.mixS T ψ μ 𝓕 (c • f) x = c • d.mixS T ψ μ 𝓕 f x`.

Introduce `c f x`. Use function extensionality and compare the values at `w`. Simplify using `only [HypDec.mixS, HypDec.integrandS_eq, Pi.smul_apply, smul_eq_mul, mul_left_comm _ c, integral_const_mul]`. Set `P : Submodule ℂ (WO S T → ℂ)` to `{ carrier := {f | (∀ x w, IntegrableOn (fun a => heisO ψ S T (d.extY T a) (heisO ψ S T (d.extX T x) (heisO ψ S T (d.ext0 T w) f)) 0) 𝓕 μ) ∧ Integrable (fun x : H => ℓ₀ (d.mixS T ψ μ 𝓕 f x.1)) ν} add_mem' := by`. Introduce and unpack `f g ⟨hf1, hf2⟩ ⟨hg1, hg2⟩`.

Use `⟨fun x w => ?_, ?_⟩` and prove the remaining obligations. Establish `h1` using `hf1 x w`. Establish `h2` using `hg1 x w`. Simplify using `only [HypDec.integrandS_eq, Pi.add_apply, mul_add] at h1 h2 ⊢`. Conclude with `h1.add h2`.

Use `(hf2.add hg2).congr (Filter.Eventually.of_forall fun x => ?_)` and prove the remaining obligations. Simplify using `only [Pi.add_apply, madd f g hf1 hg1, map_add]`. Use the proof step `zero_mem' := by`. Establish `h0 : ∀ x, d.mixS T ψ μ 𝓕 (0 : WO S T → ℂ) x = 0` using `fun x => by`. Simplify using `using msmul 0 0 x`.

Use `⟨fun x w => ?_, ?_⟩` and prove the remaining obligations. Simplify using `only [HypDec.integrandS_eq, Pi.zero_apply, mul_zero]`. Conclude with `integrableOn_zero`. Simplify using `only [h0, map_zero]`. Conclude with `integrable_zero _ _ _`.

Use the proof step `smul_mem' := by`. Introduce and unpack `c f ⟨hf1, hf2⟩`. Use `⟨fun x w => ?_, ?_⟩` and prove the remaining obligations. Establish `h1` using `hf1 x w`. Simplify using `only [HypDec.integrandS_eq, Pi.smul_apply, smul_eq_mul] at h1 ⊢`.

Simplify using `only [mul_left_comm _ c]`. Conclude with `h1.const_mul c`. Use `(hf2.const_mul c).congr (Filter.Eventually.of_forall fun x => ?_)` and prove the remaining obligations. Simplify using `only [msmul, map_smul, smul_eq_mul] }`. Establish `hP : ∀ f, IsThetaFunO ψ S T f → f ∈ P` using `fun f hf => ⟨fun x w => d.integrableOn_mixS hψ.1.1 hμ hf x w, hint f hf⟩`.

Set `L : P →ₗ[ℂ] ℂ` to `{ toFun := fun f => ∫ x : H, ℓ₀ (d.mixS T ψ μ 𝓕 f.1 x.1) ∂ν map_add' := by`. Introduce and unpack `⟨f, hf1, hf2⟩ ⟨g, hg1, hg2⟩`. Use `show ∫ x : H, ℓ₀ (d.mixS T ψ μ 𝓕 (f + g) x.1) ∂ν = ∫ x : H, ℓ₀ (d.mixS T ψ μ 𝓕 f x.1) ∂ν + ∫ x : H, ℓ₀ (d.mixS T ψ μ 𝓕 g x.1) ∂ν`. Rewrite using `[← integral_add hf2 hg2]`. Use `integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)` and prove the remaining obligations.

Simplify using `only [madd f g hf1 hg1, map_add]`. Use the proof step `map_smul' := by`. Introduce and unpack `c ⟨f, hf1, hf2⟩`. Use `show ∫ x : H, ℓ₀ (d.mixS T ψ μ 𝓕 (c • f) x.1) ∂ν = c • ∫ x : H, ℓ₀ (d.mixS T ψ μ 𝓕 f x.1) ∂ν`. Rewrite using `[smul_eq_mul, ← integral_const_mul]`.

Use `integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)` and prove the remaining obligations. Simplify using `only [msmul, map_smul, smul_eq_mul] }`. Take `⟨ℓ, hℓ⟩` from `LinearMap.exists_extend L`. Conclude with `⟨ℓ, fun f hf => LinearMap.congr_fun hℓ ⟨f, hP f hf⟩⟩`.
-/
theorem halfAvg_linear : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S S₀ T : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (μ : Measure (Mx D T.rank ρ)) (𝓕 : Set (Mx D T.rank ρ)), IsCovolOne (ratMx D T.rank ρ) μ 𝓕 → ∀ e, IsSplitIdem D e → ∀ ℓ₀ : (WO S₀ T → ℂ) →ₗ[ℂ] ℂ, ∀ H : AddSubgroup (Mx D T.rank ρ), (∀ x, x ∈ H ↔ ∀ i j, cA D e * x i j = x i j) → ∀ [MeasurableSpace H] [BorelSpace H] (ν : Measure H) [ν.IsAddHaarMeasure], ∃ ℓ : (WO S T → ℂ) →ₗ[ℂ] ℂ, ∀ f, IsThetaFunO ψ S T f → ℓ f = ∫ x : H, ℓ₀ (d.mixS T ψ μ 𝓕 f x.1) ∂ν := by
  intro D ψ hψ S S₀ T ρ d μ 𝓕 hμ e he ℓ₀ H hH _ _ ν _
  haveI : IsTopologicalAddGroup (Mx D T.rank ρ) := GlobalTheory.HalfAverage.tagMx _ _
  haveI : T2Space (Mx D T.rank ρ) := GlobalTheory.HalfAverage.t2Mx _ _
  haveI : T2Space H := inferInstance
  haveI : R1Space H := T2Space.r1Space
  haveI : ContinuousSub (Mx D T.rank ρ) := by first | exact IsTopologicalAddGroup.to_continuousSub | exact inferInstance
  have hHc : IsClosed (H : Set (Mx D T.rank ρ)) := by
    have : (H : Set (Mx D T.rank ρ)) = ⋂ i, ⋂ j, {t : Mx D T.rank ρ | cA D e * t i j = t i j} := by
      ext t; simp only [SetLike.mem_coe, hH, Set.mem_iInter, Set.mem_setOf_eq]
    rw [this]
    exact isClosed_iInter fun i => isClosed_iInter fun j =>
      isClosed_eq (continuous_const.mul ((continuous_apply j).comp (continuous_apply i)))
        ((continuous_apply j).comp (continuous_apply i))

  have hint : ∀ f, IsThetaFunO ψ S T f → Integrable (fun x : H => ℓ₀ (d.mixS T ψ μ 𝓕 f x.1)) ν := by
    intro f hf
    obtain ⟨⟨U, hUo, hU⟩, K, hK, hKs⟩ := GlobalTheory.MixHalf.mixS_half D ψ hψ S S₀ T ρ d μ 𝓕 hμ e he f hf
    have hKc : IsCompact ((Subtype.val : H → Mx D T.rank ρ) ⁻¹' K) :=
      hHc.isClosedEmbedding_subtypeVal.isCompact_preimage hK
    refine Continuous.integrable_of_hasCompactSupport ?_ (HasCompactSupport.intro hKc fun t ht => ?_)
    · refine IsLocallyConstant.continuous ?_
      rw [IsLocallyConstant.iff_eventually_eq]
      intro t
      have hn : {s : H | (s : Mx D T.rank ρ) - t ∈ U} ∈ nhds t := by
        refine IsOpen.mem_nhds (hUo.preimage (continuous_subtype_val.sub continuous_const)) ?_
        show (t : Mx D T.rank ρ) - t ∈ U
        rw [sub_self]; exact U.zero_mem
      filter_upwards [hn] with s hs
      have hsH : ∀ i j, cA D e * ((s : Mx D T.rank ρ) - t) i j = ((s : Mx D T.rank ρ) - t) i j :=
        (hH _).1 (H.sub_mem s.2 t.2)
      have h1 := hU _ hs hsH t
      rw [show (t : Mx D T.rank ρ) + ((s : Mx D T.rank ρ) - t) = s by abel] at h1
      rw [h1]
    · by_contra hne
      exact ht (hKs _ ((hH _).1 t.2) fun h0 => hne (by rw [h0, map_zero]))

  have madd : ∀ f g : WO S T → ℂ,
      (∀ x w, IntegrableOn (fun a => heisO ψ S T (d.extY T a) (heisO ψ S T (d.extX T x) (heisO ψ S T (d.ext0 T w) f)) 0) 𝓕 μ) →
      (∀ x w, IntegrableOn (fun a => heisO ψ S T (d.extY T a) (heisO ψ S T (d.extX T x) (heisO ψ S T (d.ext0 T w) g)) 0) 𝓕 μ) →
      ∀ x, d.mixS T ψ μ 𝓕 (f + g) x = d.mixS T ψ μ 𝓕 f x + d.mixS T ψ μ 𝓕 g x := by
    intro f g hf hg x
    funext w
    have h1 := hf x w
    have h2 := hg x w
    simp only [HypDec.mixS, HypDec.integrandS_eq, Pi.add_apply, mul_add] at h1 h2 ⊢
    exact integral_add h1 h2
  have msmul : ∀ (c : ℂ) (f : WO S T → ℂ) x, d.mixS T ψ μ 𝓕 (c • f) x = c • d.mixS T ψ μ 𝓕 f x := by
    intro c f x
    funext w
    simp only [HypDec.mixS, HypDec.integrandS_eq, Pi.smul_apply, smul_eq_mul, mul_left_comm _ c, integral_const_mul]
  let P : Submodule ℂ (WO S T → ℂ) :=
    { carrier := {f | (∀ x w, IntegrableOn
          (fun a => heisO ψ S T (d.extY T a) (heisO ψ S T (d.extX T x) (heisO ψ S T (d.ext0 T w) f)) 0) 𝓕 μ) ∧
        Integrable (fun x : H => ℓ₀ (d.mixS T ψ μ 𝓕 f x.1)) ν}
      add_mem' := by
        rintro f g ⟨hf1, hf2⟩ ⟨hg1, hg2⟩
        refine ⟨fun x w => ?_, ?_⟩
        · have h1 := hf1 x w
          have h2 := hg1 x w
          simp only [HypDec.integrandS_eq, Pi.add_apply, mul_add] at h1 h2 ⊢
          exact h1.add h2
        · refine (hf2.add hg2).congr (Filter.Eventually.of_forall fun x => ?_)
          simp only [Pi.add_apply, madd f g hf1 hg1, map_add]
      zero_mem' := by
        have h0 : ∀ x, d.mixS T ψ μ 𝓕 (0 : WO S T → ℂ) x = 0 := fun x => by
          simpa using msmul 0 0 x
        refine ⟨fun x w => ?_, ?_⟩
        · simp only [HypDec.integrandS_eq, Pi.zero_apply, mul_zero]; exact integrableOn_zero
        · simp only [h0, map_zero]; exact integrable_zero _ _ _
      smul_mem' := by
        rintro c f ⟨hf1, hf2⟩
        refine ⟨fun x w => ?_, ?_⟩
        · have h1 := hf1 x w
          simp only [HypDec.integrandS_eq, Pi.smul_apply, smul_eq_mul] at h1 ⊢
          simp only [mul_left_comm _ c]
          exact h1.const_mul c
        · refine (hf2.const_mul c).congr (Filter.Eventually.of_forall fun x => ?_)
          simp only [msmul, map_smul, smul_eq_mul] }
  have hP : ∀ f, IsThetaFunO ψ S T f → f ∈ P := fun f hf =>
    ⟨fun x w => d.integrableOn_mixS hψ.1.1 hμ hf x w, hint f hf⟩
  let L : P →ₗ[ℂ] ℂ :=
    { toFun := fun f => ∫ x : H, ℓ₀ (d.mixS T ψ μ 𝓕 f.1 x.1) ∂ν
      map_add' := by
        rintro ⟨f, hf1, hf2⟩ ⟨g, hg1, hg2⟩
        show ∫ x : H, ℓ₀ (d.mixS T ψ μ 𝓕 (f + g) x.1) ∂ν =
          ∫ x : H, ℓ₀ (d.mixS T ψ μ 𝓕 f x.1) ∂ν + ∫ x : H, ℓ₀ (d.mixS T ψ μ 𝓕 g x.1) ∂ν
        rw [← integral_add hf2 hg2]
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        simp only [madd f g hf1 hg1, map_add]
      map_smul' := by
        rintro c ⟨f, hf1, hf2⟩
        show ∫ x : H, ℓ₀ (d.mixS T ψ μ 𝓕 (c • f) x.1) ∂ν = c • ∫ x : H, ℓ₀ (d.mixS T ψ μ 𝓕 f x.1) ∂ν
        rw [smul_eq_mul, ← integral_const_mul]
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        simp only [msmul, map_smul, smul_eq_mul] }
  obtain ⟨ℓ, hℓ⟩ := LinearMap.exists_extend L
  exact ⟨ℓ, fun f hf => LinearMap.congr_fun hℓ ⟨f, hP f hf⟩⟩

end GlobalTheory.HalfLinForm
